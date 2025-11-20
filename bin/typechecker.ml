open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string


let type_error (l : 'a node) (err : string) = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic = or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with 
  | TInt, TInt 
  | TBool, TBool -> true
  | TNullRef r1, TNullRef r2 
  | TRef r1, TRef r2 
  | TRef r1, TNullRef r2 -> subtype_ref c r1 r2
  | _ -> false
(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with 
  | RString, RString -> true
  | RArray t1', RArray t2' -> t1' = t2'
  | RStruct id1, RStruct id2 -> 
    let comp = fun f1 f2 -> if f1.fieldName < f2.fieldName then -1 else if f1.fieldName > f2.fieldName then 1 else 0 in 
    let s1 = lookup_struct id1 c |> List.sort comp in 
    let s2 = lookup_struct id2 c |> List.sort comp in 
    let n = List.length s2 in 
    if n > List.length s1 
    then false 
    else 
      let s1' = List.init n (fun i -> List.nth s1 i) in 
      if List.length s1' != List.length s2 
      then false  
      else 
        let combined = List.combine s1' s2 in
        List.fold_left (fun acc (f1, f2) -> f1.fieldName = f2.fieldName && f1.ftyp = f2.ftyp && acc) true combined
  | RFun (ts1, rt1), RFun (ts2, rt2) -> 
    if List.length ts1 != List.length ts2 
    then false  
    else 
      let combined = List.combine ts1 ts2 in
      List.fold_left (fun acc (t1', t2') -> (subtype c t2' t1') && acc) true combined
        && (subtype_ret c rt1 rt2)
  | _ -> false
  (* Decides whether H |-r rt1 <: rt2 *)
  and subtype_ret (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
    match t1, t2 with 
    | RetVoid, RetVoid -> true
    | RetVal t1', RetVal t2' -> subtype c t1' t2'
    | _ -> false

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with 
  | TBool
  | TInt -> ()
  | TRef rt 
  | TNullRef rt -> typecheck_rty l tc rt
and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit = 
  match t with 
  | RString -> ()
  | RArray t' -> typecheck_ty l tc t'
  | RStruct id -> 
    begin match lookup_struct_option id tc with 
    | Some _ -> ()
    | _ -> type_error l "Type is not well formed"
    end
  | RFun (ts, rt) -> 
    List.fold_left (fun acc t' -> (typecheck_ty l tc t')) () ts;
    typecheck_rety l tc rt
and typecheck_rety (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit = 
  match t with 
  | RetVoid -> ()
  | RetVal t' -> typecheck_ty l tc t'


(* A helper function to determine whether a type allows the null value *)
let is_nullable_ty (t : Ast.ty) : bool =
  match t with
  | TNullRef _ -> true
  | _ -> false

let sort_struct_fields (f:Ast.field list) : Ast.field list  =
  List.sort 
    (fun f1 f2 -> if f1.fieldName < f2.fieldName then -1 else if f1.fieldName > f2.fieldName then 1 else 0) f 

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oat.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with 
  | CNull rt -> 
    typecheck_rty e c rt; 
    TNullRef rt
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Lhs ln -> typecheck_lhs c ln |> fst
  | CArr (t, es) -> 
    typecheck_ty e c t;
    List.fold_left (fun acc en -> 
      let tn = typecheck_exp c en in 
      if not (subtype c t tn) 
      then type_error e "Expression is not typed correctly (carr)"
      else 
        match tn with 
        | TNullRef _ -> TNullRef (RArray t)
        | _ -> acc 
      ) (TRef (RArray t)) es 
  | NewArr (t, e') -> 
    typecheck_ty e c t;
    begin match typecheck_exp c e' with 
    | TInt -> 
      (match t with 
      | TInt 
      | TBool 
      | TNullRef _ -> TRef (RArray t)
      | _ -> type_error e' "Expression is not typed correctly (newarr)")
    | _ -> type_error e' "Expression is not typed correctly (newarr)"
    end
  | NewArrInit (t, e1, id, e2) -> 
    typecheck_ty e c t;
    let check = typecheck_exp c e1 in 
    begin match check with 
    | TInt -> 
      (match lookup_local_option id c with 
      | Some _ -> type_error e1 "Expression is not typed correctly (newarrinit)"
      | _ -> 
        let updated_c = add_local c id TInt in
        let t' = typecheck_exp updated_c e2 in 
        if subtype c t' t 
        then TRef (RArray t)
        else type_error e2 "Expression is not typed correctly (newarrinit)")
    | _ -> type_error e1 "Expression is not typed correctly (newarrinit)"
    end
  | Length e' -> 
    let t = typecheck_exp c e' in 
    begin match t with 
    | TRef (RArray _) -> TInt 
    | _ -> type_error e' "Expression is not typed correctly (length)"
    end
  | CStruct (id, f) -> 
    begin match lookup_struct_option id c with 
    | Some fields -> 
      let fields = sort_struct_fields fields in 
      let fields' = List.map (fun fi -> {fieldName=fst fi; ftyp=typecheck_exp c (snd fi)}) f |> sort_struct_fields in 
      if List.length fields' != List.length fields 
      then type_error e "Expression is not typed correctly (cstruct)"  
      else 
        let combined = List.combine fields' fields in
        if List.fold_left (fun acc (f1, f2) -> f1.fieldName = f2.fieldName && (subtype c f1.ftyp f2.ftyp) && acc) true combined
        then TRef (RStruct id) 
        else type_error e "Expression is not typed correctly (cstruct)"  
    | _ -> type_error e "Expression is not typed correctly (cstruct)"
    end 
  | Call (e1, es) -> 
    let fty = typecheck_exp c e1 in 
    begin match fty with 
    | TRef (RFun (tl, ret)) -> 
      let params = List.map (typecheck_exp c) es in 
      if List.length params != List.length tl 
      then type_error e "Expression is not typed correctly (call)"  
      else 
        let combined = List.combine params tl in 
        if List.fold_left (fun acc (t1', t2') -> (subtype c t1' t2') && acc) true combined 
        then 
          (match ret with 
          | RetVoid -> fty 
          | RetVal t -> t)
      else type_error e "Expression is not typed correctly (call)"  
    | _ -> type_error e "Expression is not typed correctly (call)"
    end
  | Bop (bop, e1, e2) -> 
    let t1 = typecheck_exp c e1 in 
    let t2 = typecheck_exp c e2 in 
    begin match bop with 
    | Eq 
    | Neq -> 
      if subtype c t1 t2
      then TBool
      else type_error e "Expression is not typed correctly (bop)"  
    | _ ->
      (match typ_of_binop bop with 
      | (t1', t2', res) -> 
        if t1' = t1 && t2' = t2
        then res 
        else type_error e "Expression is not typed correctly (bop)")
    end 
  | Uop (uop, e') -> 
    let t = typecheck_exp c e' in 
    begin match typ_of_unop uop with 
    | (t', res) -> 
      if t' = t
      then res 
      else type_error e "Expression is not typed correctly (uop)"
    end 

(* Typechecks a lhs expression in the typing context c.  Returns the
   type of result, along with a boolean flag indicating whether
   the lhs is "assignable".
   INVARIANT:
     If the flag is true, we can think of lhs as denoting a reference
     to a value of the returned type.

     If the flag is false, the lhs is a (globally defined) function
     pointer (which cannot be written to).
 *)
and typecheck_lhs (c : Tctxt.t) (l : Ast.lhs node) : Ast.ty * bool =
  match l.elt with 
  | Id id -> 
    begin match lookup_local_option id c with 
    | Some t -> t, true
    | _ -> 
      (match lookup_global_option id c with 
        | Some (TRef (RFun (ts, rt))) -> TRef (RFun (ts, rt)), false
        | Some t ->  t, true
        | _ -> type_error l ("LHS Expression is not typed correctly (id) " ^ id))
    end 
  | Proj (e', id) -> 
    let t = typecheck_exp c e' in 
    begin match t with 
    | TRef (RStruct sid) -> 
      (match lookup_field_option sid id c with 
      | Some t' -> t', true
      | _ -> type_error e' "LHS Expression is not typed correctly (proj)")
    | _ -> type_error e' "LHS Expression is not typed correctly (proj)"
    end 
  | Index (e1, e2) -> 
    let t1 = typecheck_exp c e1 in 
    let t2 = typecheck_exp c e2 in 
    begin match t1, t2 with 
    | TRef (RArray t), TInt -> t, true
    | _ -> type_error l "LHS Expression is not typed correctly (index)"
    end 
    
(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement)

     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, the return behavior of the branching 
        statement is the conjunction of the return behavior of the two 
        branches: both both branches must definitely return in order for 
        the whole statement to definitely return.

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entire conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  let typecheck_vdecl (tc : Tctxt.t) (v:Ast.vdecl) : Tctxt.t = 
    let t = typecheck_exp tc (snd v) in 
    begin match lookup_local_option (fst v) tc with 
    | Some _ -> type_error s "Statement is not typed correctly"
    | _ -> 
      (match t with 
      | TRef (RFun (_, RetVoid)) -> type_error s "Cannot assign void"
      | _ -> add_local tc (fst v) t)
    end in
  match s.elt with 
  | Assn (l, e) -> 
    let (t, _) = typecheck_lhs tc l in  
    begin match l.elt with 
    | Id id -> 
      (match lookup_local_option id tc, lookup_global_option id tc with 
      | None, Some (TRef (RFun (_,_))) -> type_error l "cannot assign to a global function"
      | _ -> 
        let t' = typecheck_exp tc e in 
        if subtype tc t' t 
        then tc, false
        else type_error s "Statement is not typed correctly (assn)")
    | _ -> 
      let t' = typecheck_exp tc e in 
      if subtype tc t' t 
      then tc, false
      else type_error s "Statement is not typed correctly (assn)"
    end 
  | Decl v -> typecheck_vdecl tc v, false
  | SCall (e, es) -> 
    let t = typecheck_exp tc e in 
    begin match t with 
    | TRef (RFun (types, RetVoid)) -> 
      let types' = List.map (typecheck_exp tc) es in 
      if List.length types' != List.length types 
      then type_error e "Statement is not typed correctly (scall)"  
      else 
        let combined = List.combine types' types in 
        if List.fold_left (fun acc (t1, t2) -> (subtype tc t1 t2) && acc) true combined 
        then tc, false
        else type_error s "Statement is not typed correctly (scall)"
    | _ -> type_error s "Statement is not typed correctly (scall)"
    end 
  | If (e, s1, s2) -> 
    let t = typecheck_exp tc e in 
    begin match t with 
    | TBool -> 
      let block1, r1 = typecheck_block tc s1 to_ret false in 
      let block2, r2 = typecheck_block tc s2 to_ret false in 
      tc, r1 && r2
    | _ -> type_error s "Statement is not typed correctly (if)"
    end 
  | Cast (rt, id, e, s1, s2) -> 
    let t = typecheck_exp tc e in 
    begin match t with 
    | TNullRef rt' -> 
      if subtype tc (TRef rt') (TRef rt)
      then 
        let updated_tc = add_local tc id (TRef rt) in
        let block1, r1 = typecheck_block updated_tc s1 to_ret false in 
        let block2, r2 = typecheck_block tc s2 to_ret false in 
        tc, r1 && r2
      else type_error s "Statement is not typed correctly (ifq)"
    | _ -> type_error s "Statement is not typed correctly (ifq)"
    end 
  | While (e, ss) -> 
    let t = typecheck_exp tc e in 
    begin match t with 
    | TBool -> 
      let _ = typecheck_block tc ss to_ret false in 
      tc, false
    | _ -> type_error s "Statement is not typed correctly (while)"
    end 
  | For (vs, e_opt, s_opt, ss) ->
    let updated_tc = List.fold_left (fun tc' v -> (typecheck_vdecl tc v)) tc vs in 
    let te = begin match e_opt with 
    | Some e -> 
      let t = typecheck_exp updated_tc e in 
      (match t with 
      | TBool -> TBool
      | _ -> type_error s "Statement is not typed correctly (for)")
    | _ -> TBool
    end in let _ = begin match s_opt with 
    | Some s' -> 
      let _, _ = typecheck_stmt updated_tc s' to_ret in 
      ()
    | _ -> ()
    end in 
    let _ = typecheck_block updated_tc ss to_ret false in 
    tc, false
  | Ret e_opt -> 
    let ret = 
      begin match e_opt with 
      | Some e -> 
        let t' = typecheck_exp tc e in 
        (RetVal t')
      | _ -> RetVoid
      end in
    if subtype_ret tc ret to_ret 
    then tc, true 
    else type_error s "Statement is not typed correctly (ret)"
and typecheck_block (tc : Tctxt.t) (b:Ast.block) (to_ret:ret_ty) (ret:bool) : Tctxt.t * bool =
  match b with 
  | [] -> tc, ret
  | [{elt=Ret _; loc=loc} as s] -> typecheck_stmt tc s to_ret
  | {elt=Ret _; loc=loc} as s::tl -> type_error s "Cannot have statements after return"
  | s::tl -> 
    let updated_tc, ret = typecheck_stmt tc s to_ret in 
    typecheck_block updated_tc tl to_ret ret

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups (fs : field list) =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) (id : id) (fs : field list)  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - ensures formal parameters are distinct
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit = 
  let check_dup_args = List.fold_left 
    (fun tc' arg -> 
      match lookup_local_option (snd arg) tc' with 
      | Some _ -> type_error l ("Repeated fields in " ^ (snd arg))
      | _ -> add_local tc' (snd arg) (fst arg)) tc f.args in 
  let _, ret = typecheck_block check_dup_args f.body f.frtyp true in 
  if ret then () else type_error l "Function doesn't return"
    

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog => H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog => G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog => G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can mention only other global values that were declared earlier
*)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  List.fold_left 
    (fun tc' d -> 
      match d with 
      | Gtdecl t ->
        begin match lookup_struct_option (fst t.elt) tc' with 
        | Some _ -> type_error t ("Repeated structs in " ^ (fst t.elt))
        | _ -> 
          let fields = sort_struct_fields (snd t.elt) in 
          add_struct tc' (fst t.elt) fields
        end
      | _ -> tc') {locals=[]; globals=[]; structs=[]} p

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let add_builtins = List.fold_left 
    (fun tc' f -> 
      let func_ty = TRef (RFun (fst (snd f), snd (snd f))) in 
      add_global tc' (fst f) func_ty) tc builtins in 
  List.fold_left 
    (fun tc' d -> 
      match d with 
      | Gfdecl f -> 
        begin match lookup_global_option f.elt.fname tc' with 
        | Some _ -> type_error f ("Repeated functions in " ^ f.elt.fname)
        | _ -> 
          let arg_types = List.map fst f.elt.args in 
          add_global tc' f.elt.fname (TRef (RFun (arg_types, f.elt.frtyp)))
        end
      | _ -> tc') add_builtins p

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left 
    (fun tc' d -> 
      match d with 
      | Gvdecl g -> 
        begin match lookup_global_option g.elt.name tc' with 
        | Some _ -> type_error g ("Repeated globals in " ^ g.elt.name)
        | _ -> 
          let t = typecheck_exp tc' g.elt.init in
          add_global tc' g.elt.name t
        end
      | _ -> tc') tc p



(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p