open Datastructures

(* dataflow analysis graph signature ---------------------------------------- *)
(* Interface for dataflow graphs structured in a way to facilitate 
   the general iterative dataflow analysis algorithm.                         

   The AsGraph functor in cfg.ml provides an implementation of this
   DFA_GRAPH signature that converts an LL IR control-flow graph to 
   this representation.

   NOTE: The direction of the analysis is goverened by how preds and
   succs are instantiated and how the corresponding flow function
   is defined.  This module pretends that all information is flowing
   "forward", but e.g. liveness instantiates the graph so that "forward"
   here is "backward" in the control-flow graph.

   This means that for a node n, the output information is *explicitly*
   represented by the "Graph.out" function:
     out[n] = Graph.out g n
   The input information for [n] is *implicitly* represented by:
     in[n] = combine preds[n] (out[n])

*)
module type DFA_GRAPH =
  sig
    module NodeS : SetS

    (* type of nodes in this graph *)
    type node = NodeS.elt

    (* dataflow facts associated with the out-edges of the nodes in the graph *)
    type fact

    (* the abstract type of dataflow graphs *)
    type t
    val preds : t -> node -> NodeS.t
    val succs : t -> node -> NodeS.t
    val nodes : t -> NodeS.t

    (* the flow function:
       given a graph node and input fact, compute the resulting fact on the 
       output edge of the node                                                
    *)
    val flow : t -> node -> fact -> fact

    (* lookup / modify the dataflow annotations associated with a node *)    
    val out : t -> node -> fact
    val add_fact : node -> fact -> t -> t
  end

(* abstract dataflow lattice signature -------------------------------------- *)
(* The general algorithm works over a generic lattice of abstract "facts".
   - facts can be combined (this is the 'meet' operation)
   - facts can be compared:
      for `compare x y` the result indicates:
        < 0 : x is less than y
        = 0 : x equals y
        > 0 : x is greater than y
*)
module type FACT =
  sig
    type t
    val combine : t list -> t
    val compare : t -> t -> int
    val to_string : t -> string
  end


(* generic iterative dataflow solver ---------------------------------------- *)
(* This functor takes two modules:
      Fact  - the implementation of the lattice                                
      Graph - the dataflow anlaysis graph

   It produces a module that has a single function 'solve', which 
   implements the iterative dataflow analysis described in lecture.
      - using a worklist (or workset) nodes 
        [initialized with the set of all nodes]

      - process the worklist until empty:
          . choose a node from the worklist
          . find the node's predecessors and combine their flow facts
          . apply the flow function to the combined input to find the new
            output
          . if the output has changed, update the graph and add the node's
            successors to the worklist                                        

   TASK: complete the [solve] function, which implements the above algorithm.
*)
module Make (Fact : FACT) (Graph : DFA_GRAPH with type fact := Fact.t) =
  struct

    let solve (g:Graph.t) : Graph.t =
      let w = Graph.nodes g in 
      let rec helper (w:Graph.NodeS.t) (g:Graph.t) : Graph.t =
        match Graph.NodeS.is_empty w with 
        | false -> 
          let n = Graph.NodeS.choose w in 
          let w = Graph.NodeS.remove n w in
          let old_out = Graph.out g n in 
          let in_n = Fact.combine (Graph.NodeS.fold 
            (fun p acc -> Graph.out g p :: acc) (Graph.preds g n) []) in 
          let out = Graph.flow g n in_n in 
          let new_graph = Graph.add_fact n out g in
          begin 
            if not ((Fact.compare old_out out) = 0)
            then 
              let new_workset = Graph.NodeS.fold (fun m acc -> Graph.NodeS.add m acc) (Graph.succs g n) w in 
              helper new_workset new_graph
            else helper w new_graph
          end
        | true -> g
      in helper w g
  end

