(** Dead Code Elimination  *)
open Ll
open Datastructures


(* dce_block ---------------------------------------------------------------- *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =
  let dce_helper ((u,i):Ll.uid*Ll.insn) : bool = 
    match i with 
    | Store (_, _, Gid _) 
    | Call _ -> true
    | Store (_, _, Id u') -> 
      (UidS.mem u' (lb u)) 
        || 
        Alias.SymPtr.(compare (UidM.find_or UndefAlias (ab u) u') MayAlias) = 0
    | _ -> UidS.mem u (lb u)
  in 
  {insns = List.filter dce_helper b.insns; term = b.term}

(* Run DCE on all the blocks of a given control-flow-graph. *) 
let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

