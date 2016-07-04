(* ra.sml
 *
 *   A simple graph-coloring register allocator.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure RegAlloc : sig
    val alloc : { showigraph: bool } ->
		Asm.instr list * Frame.frame * Frame.register list ->
		Asm.instr list * Frame.allocation
end = struct

    fun alloc { showigraph } (il, frame, registers) = let

	fun memberOf l (t: LVar.lvar) = List.exists (fn t' => t=t') l

	fun rewrite (il, spills) = let
	    (*
	    val _ = print "spilling:"
	    val _ = app (fn v => print (" " ^ LVar.toString v)) spills
	    val _ = print "\n"
	     *)
	in
	    foldr (Rewrite.rewrite (frame, spills)) [] il
	end

	fun try (il, pastSpills) = let
	    val (fgraph, fgnl) = MakeGraph.instrs2graph il
	    val { igraph, liveOut } = Liveness.interferenceGraph (fgraph, fgnl)
	    val Liveness.IGRAPH { gtemp, ... } = igraph

	    val _ = if showigraph then
			Liveness.show (TextIO.stdErr,
				       Frame.showTemp Frame.precoloring,
				       igraph)
		    else ()

	    fun spillCost n =
		if memberOf pastSpills (gtemp n) then 10000
		else 1

	    val (allocation, spills) =
		Color.color { interference = igraph,
			      initial = Frame.precoloring,
			      spillCost = spillCost,
			      registers = registers }

	    fun col t = valOf (LVar.Map.find (allocation, t))
	    fun delMove (i as Asm.MOVE { src, dst, ... }, r) =
		if col src = col dst then r else i :: r
	      | delMove (i, r) = i :: r
	in case spills of
	       [] => (foldr delMove [] il, allocation)
	     | _ => try (rewrite (il, spills), spills @ pastSpills)
	end

    in try (il, [])
    end
end
