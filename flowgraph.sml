(* flowgraph.sml
 *
 *   Representing flow graphs.
 *     This code is taken from Andrew Appel's book "Modern Compiler
 *     Implementation in ML".
 *)
structure Flow = struct
    structure Graph = Graph
    datatype flowgraph =
	FGRAPH of
	     {
	      (* control: directed graph representing control flow
	       *          from instruction to instruction.  (Each graph
	       *          node represents one instruction. *)
	      control: Graph.graph,
	      (* def: mapping from graph nodes to sets of variables
	       *      defined at these nodes *)
	      def: LVar.Set.set Graph.Map.map,
	      (* use: mapping from graph nodes to sets of variables
	       *      used at these nodes *)
	      use: LVar.Set.set Graph.Map.map,
	      (* ismove: mapping from graph nodes to a boolean telling
	       *         whether the corresponding instruction was a
	       *         MOVE *)
	      ismove: bool Graph.Map.map
	     }

  (* Note:  any "use" within the block is assumed to be BEFORE a "def" 
        of the same variable.  If there is a def(x) followed by use(x)
       in the same block, do not mention the use in this data structure,
       mention only the def.

     More generally:
       If there are any nonzero number of defs, mention def(x).
       If there are any nonzero number of uses BEFORE THE FIRST DEF,
           mention use(x).

     For any node in the graph,  
           Graph.Table.look(def,node) = SOME(def-list)
           Graph.Table.look(use,node) = SOME(use-list)
   *)

end
