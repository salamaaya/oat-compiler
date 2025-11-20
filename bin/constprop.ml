open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare (a:t) (b:t) =
      match a, b with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t

let interp_static_binop (b:bop) (i1:int64) (i2:int64) : int64 = 
  match b with 
  | Add -> Int64.add i1 i2
  | Sub -> Int64.sub i1 i2
  | Mul -> Int64.mul i1 i2
  | Shl -> Int64.shift_left i1 (Int64.to_int i2)
  | Lshr -> Int64.shift_right_logical i1 (Int64.to_int i2)
  | Ashr -> Int64.shift_right i1 (Int64.to_int i2)
  | And -> Int64.logand i1 i2
  | Or -> Int64.logor i1 i2
  | Xor -> Int64.logxor i1 i2

let interp_static_icmp (c:cnd) (i1:int64) (i2:int64) : int64 = 
  if
    match c with 
    | Eq -> (Int64.compare i1 i2) == 0
    | Ne -> (Int64.compare i1 i2) != 0
    | Slt -> (Int64.compare i1 i2) < 0
    | Sle -> (Int64.compare i1 i2) <= 0
    | Sgt -> (Int64.compare i1 i2) > 0
    | Sge -> (Int64.compare i1 i2) >= 0
  then 1L 
  else 0L

(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out with
     result that is computed statically (see the Int64 module)
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let arg_t (o:operand) : SymConst.t = 
    match o with 
    | Const c -> SymConst.Const c 
    | Id id -> 
      begin match UidM.find_opt id d with
      | Some c -> c 
      | None -> SymConst.UndefConst 
      end 
    | _ -> NonConst
  in
  match i with 
  | Binop (b,_,o1,o2) -> 
    begin match arg_t o1, arg_t o2 with 
    | SymConst.Const i1, SymConst.Const i2 -> UidM.add u (SymConst.Const (interp_static_binop b i1 i2)) d
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
    | SymConst.NonConst, _ | _, SymConst.NonConst -> UidM.add u SymConst.NonConst d
    end
  | Icmp (c,_,o1,o2) -> 
    begin match arg_t o1, arg_t o2 with 
    | SymConst.Const i1, SymConst.Const i2 -> UidM.add u (SymConst.Const (interp_static_icmp c i1 i2)) d
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
    | SymConst.NonConst, _ | _, SymConst.NonConst -> UidM.add u SymConst.NonConst d
    end
  | Store (_,_,_) | Call (Void,_,_) -> UidM.add u SymConst.UndefConst d
  | _ -> UidM.add u SymConst.NonConst d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      let merge_helper (u:uid) (s1:SymConst.t option) (s2:SymConst.t option) : SymConst.t option = 
        match s1, s2 with 
        | None, None -> None 
        | Some _, None -> s1 
        | None, Some _ -> s2
        | Some SymConst.Const c1, Some SymConst.Const c2 -> 
          if c1=c2
          then Some (SymConst.Const c1)
          else Some SymConst.NonConst
        | Some SymConst.NonConst, _ | _, Some SymConst.NonConst -> Some SymConst.NonConst
        | Some SymConst.UndefConst, _ | _, Some UndefConst -> Some SymConst.UndefConst
      in
      let combine_helper (f1:fact) (f2:fact) : fact = UidM.merge merge_helper f1 f2
      in List.fold_left combine_helper UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let cp_helper (u:uid) (o:operand)  : Ll.operand = 
      match o with 
      | Id id -> 
        begin match UidM.find id (cb u) with 
        | SymConst.Const c -> Const c
        | _ -> Id id 
        end
      | _ -> o
    in
    let cp_insn (u,i:Ll.uid*Ll.insn) : (uid*insn) = 
      u, match i with 
      | Binop (b,t,o1,o2) -> Binop (b, t, cp_helper u o1, cp_helper u o2)
      | Icmp (c,t,o1,o2) -> Icmp (c, t, cp_helper u o1, cp_helper u o2)
      | Store (t,o1,o2) -> Store (t, cp_helper u o1, cp_helper u o2)
      | Call (t,o,tol) -> Call (t, o, List.map (fun (t,o) -> (t, cp_helper u o)) tol)
      | Gep (t,o,ol) -> Gep (t, o, List.map (cp_helper u) ol)
      | _ -> i
    in
    let cp_term (u,t:Ll.uid*Ll.terminator) : (uid*terminator) = 
      u, match t with 
      | Ret (t,Some o) -> Ret (t, Some (cp_helper u o))
      | Cbr (o,l1,l2) -> Cbr (cp_helper u o, l1, l2)
      | _ -> t
    in 
    let b' = {insns = List.map cp_insn b.insns; term = cp_term b.term} in 
    Cfg.add_block l b' cfg
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
