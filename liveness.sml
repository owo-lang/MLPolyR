(* liveness.sml
 *
 *   Liveness analysis and interference graph construction.
 *   This is part of a simple graph-coloring register allocator.
 *   The design is based on Andrew Appel's book "Modern Compiler
 *   Implementation in ML".
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Liveness : sig

    structure IGraph: GRAPH
    datatype igraph =
	     IGRAPH of
	     {
	      (* graph: edges between interfering nodes,
	       *        We treat the graph as an UNDIRECTED graph
	       *        (even though the IGraph module implements
	       *         directed graphs) by using the following
	       *         invariant:
	       *         An interference between v and w is represented
	       *         as a directed edge between the "smaller" node
	       *         to the "larger" node where "smaller" is defined
	       *         in terms of LVar.compare. *)
	      graph: IGraph.graph,
	      (* tnode: mapping from lvars to their corresponding
	       *        nodes in the interference graph *)
	      tnode: LVar.lvar -> IGraph.node,
	      (* gtemp: inverse of tnode *)
	      gtemp: IGraph.node -> LVar.lvar,
	      (* List of move-related nodes: *)
	      moves: (IGraph.node * IGraph.node) list
	     }

    val interferenceGraph:
	(* first parameter is the flow graph;
	 * second parameter lists all flow graph nodes in (roughly)
	 * "forward" order (meaning that if n is a predecessor of m,
	 * then n tends to appear to the left of m in the list) *)
	Flow.flowgraph * Flow.Graph.node list ->
	{ igraph: igraph, liveOut: Flow.Graph.node -> LVar.lvar list }

    val show: TextIO.outstream * (LVar.lvar -> string) * igraph -> unit

end = struct

    structure IGraph :> GRAPH = Graph
    structure G = IGraph
    structure GT = G.Map
    structure F = Flow
    structure FG = F.Graph
    structure FGT = FG.Map
    structure T = LVar
    structure TS = T.Set
    structure TT = T.Map

    datatype igraph =
	     IGRAPH of { graph: IGraph.graph,
			 tnode: LVar.lvar -> IGraph.node,
			 gtemp: IGraph.node -> LVar.lvar,
			 moves: (IGraph.node * IGraph.node) list }

    type liveset = TS.set
    type livemap = liveset FGT.map

    fun interferenceGraph (F.FGRAPH { control, def, use, ismove }, fgnl) =
	let val cnodes = rev fgnl (* process nodes in "backward" order *)
	    fun live lm n =
		case FGT.find (lm, n) of
		    SOME ls => ls
		  | NONE => TS.empty
	    (* walk over list of nodes, maintain "live out" and "live in"
	     * sets on a per-node basis;  maintain a "change" flag,
	     * which -- when false -- tells us that the fixpoint iteration
	     * has settled; keep iterating over list of nodes until
	     * fixpoint is reached: *)
	    fun iterate ([], lom, lim, true) =
		  ( (* print "."; *) iterate (cnodes, lom, lim, false))
	      | iterate ([], lom, lim, false) = lom
	      | iterate (n :: ns, lom, lim, change) =
		let val lo = live lom n
		    val lo' =
			foldl TS.union TS.empty (map (live lim) (FG.succ n))
		    val change' = change orelse not (TS.equal (lo, lo'))
		    val lom' = FGT.insert (lom, n, lo')
		    val u = valOf (FGT.find (use, n))
		    val d = valOf (FGT.find (def, n))
		    val li' = TS.union (u, TS.difference (lo', d))
		    val lim' = FGT.insert (lim, n, li')
		in iterate (ns, lom', lim', change')
		end
	    (* run it with change = true to initialize lim properly *)
	    val liveOutMap = iterate (cnodes, FGT.empty, FGT.empty, true)

	    (* now initialize the interference graph that we
	     * are about to build: *)
	    val ig = G.newGraph ()
	    local
		(* a handy mapping from lvars to nodes: *)
		val tmap = ref (TT.empty)
		(* an equally handy mapping from nodes to lvars: *)
		val nmap = ref (GT.empty)
	    in
	    (* tnode maps lvars to nodes, it generates and inserts
	     * new nodes as needed *)
	    fun tnode t =
		case TT.find (!tmap, t) of
		    SOME n => n
		  | NONE =>
		      let val n = G.newNode ig
		      in tmap := TT.insert (!tmap, t, n);
			 nmap := GT.insert (!nmap, n, t);
			 n
		    end
	    (* gtemp is the inverse mapping; we don't use it here
	     * but return it as part of the result *)
	    fun gtemp n = valOf (GT.find (!nmap, n))
	    end

	    (* process one node at a time, "ml" holds the
	     * list of accumulated moves: *)
	    fun interference (fgn, ml) =
		let val u = valOf (FGT.find (use, fgn))
		    val d = valOf (FGT.find (def, fgn))
		    val lo = live liveOutMap fgn
		    infix <?
		    fun x <? s = TS.member (s, x)
		    val ism = Option.getOpt (FGT.find (ismove, fgn), false)
		    val ml' =
			if ism then
			    (tnode (hd (TS.listItems u)),
			     tnode (hd (TS.listItems d))) :: ml
			else ml
		    fun oned d =
			(* deal with one defined variable d:
			 * compare it to every live-out variable lo,
			 * record interference unless d = lo or
			 * the instruction is a move whose source
			 * is lo: *)
			let fun edge (x, y) =
				let val xn = tnode x
				    val yn = tnode y
				in case LVar.compare (x, y) of
				       LESS => G.mk_edge { from = xn, to = yn }
				     | _ => G.mk_edge { from = yn, to = xn }
				end
			    fun onelo lo =
				if d=lo orelse ism andalso lo <? u then ()
				else edge (d, lo)
			in TS.app onelo lo
			end
		in TS.app oned d; ml'
		end
	    val moves = foldl interference [] cnodes
	in { igraph = IGRAPH { graph = ig, tnode = tnode,
			       gtemp = gtemp, moves = moves },
	     liveOut = TS.listItems o live liveOutMap }
	end

    fun show (s, mkstr, IGRAPH { graph = g, moves = m, gtemp, ... }) =
	let fun name n = mkstr (gtemp n)
	    fun oneNode n = let
		fun oneAdj a = TextIO.output (s, " " ^ mkstr a)
	    in TextIO.output (s, mkstr (gtemp n) ^ ":");
	       TS.app oneAdj (TS.addList (TS.empty, (map gtemp (G.adj n))));
	       TextIO.output (s, "\n")
	    end
	    fun oneMove (u, d) =
		TextIO.output (s, concat [name u, " -> ", name d, "\n"])
	in TextIO.output (s, "INTERFERENCES:\n");
	   app oneNode (G.nodes g);
	   TextIO.output (s, "MOVES:\n");
	   app oneMove m
	end
end
