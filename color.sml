(* color.sml
 *
 *   The graph-coloring part of a simple register allocator.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Color : sig

    val color : { interference: Liveness.igraph,
		  initial: Frame.allocation,
		  spillCost: Liveness.IGraph.node -> int,
		  registers : Frame.register list }
		-> Frame.allocation * LVar.lvar list

end = struct

    structure Frame = Frame
    structure L = Liveness
    structure IG = L.IGraph
    structure TT = LVar.Map
    structure GT = IG.Map
    structure TS = LVar.Set

    fun color { interference, initial, spillCost, registers } =
	let val k = length registers
	    val L.IGRAPH { graph, tnode, gtemp, moves } = interference
	    val nodes = IG.nodes graph
	    fun adjacent n = let
		fun uniq ([], u) = u
		  | uniq (h :: t, u) =
		    uniq (t, if List.exists (fn n => IG.eq (h, n)) u then u
			     else h :: u)
	    in
		uniq (IG.adj n, [])
	    end
	    val degreeOf = length o adjacent

	    fun spillCost' n = spillCost n - degreeOf n

	    (* eligible nodes -- not precolored *)
	    val nodes' =
		List.filter (fn n => not (TT.inDomain (initial, gtemp n)))
	                    nodes

	    fun categ (n, (low, high, m)) = let
		val d = degreeOf n
		val m' = GT.insert (m, n, d)
	    in
		if d < k then (n :: low, high, m') else (low, n :: high, m')
	    end

	    val (low, high, dm) = foldl categ ([], [], GT.empty) nodes'


	    fun select (n, low, high, dm) = let
		val adj = adjacent n
		val dm = #1 (GT.remove (dm, n))
		fun otherThan n1 n2 = not (IG.eq (n1, n2))
		fun lowerDegree (a, (low, high, dm)) =
		    case GT.find (dm, a) of
			NONE => (low, high, dm)
		      | SOME d => let
			    val d' = d - 1
			    val dm = GT.insert (dm, a, d')
			in
			    if d = k then
				(a :: low, List.filter (otherThan a) high, dm)
			    else (low, high, dm)
			end
		val (low, high, dm) = foldl lowerDegree (low, high, dm) adj
	    in
		(low, high, dm, adj)
	    end

	    fun pickColor (n, adj, (allocation, spills)) = let
		fun remove (a, avail) =
		    case TT.find (allocation, gtemp a) of
			NONE => avail
		      | SOME r => List.filter (fn r' => r <> r') avail

		fun biasedPick [] = (allocation, gtemp n :: spills)
		  | biasedPick avail = let
			fun frequency c = let
			    fun cColored x =
				case TT.find (allocation, gtemp x) of
				    NONE => false
				  | SOME c' => c = c'
			    fun count ([], cnt) = cnt
			      | count ((n1, n2) :: ml, cnt) =
				if IG.eq (n1, n) andalso cColored n2
				   orelse IG.eq (n2, n) andalso cColored n1 then
				    count (ml, cnt + 1)
				else count (ml, cnt)
			in
			    count (moves, 0)
			end
			fun loop ([], best, _) =
			      (TT.insert (allocation, gtemp n, best), spills)
			  | loop (c :: cs, b, m) = let
				val cfreq = frequency c
			    in
				if cfreq > m then loop (cs, c, cfreq)
				else loop (cs, b, m)
			    end
		    in
			loop (avail, Frame.boguscolor, ~1)
		    end

	    (* (* for unbiased coloring... *)
	     fun biasedPick [] = ErrorMsg.impossible "run out of registers"
	       | biasedPick (first :: _) =
		 TT.enter (allocation, gtemp n, first)
	     *)
	    in
		biasedPick (foldl remove registers adj)
	    end

	    fun try ([], [], _) = (initial, [])
	      | try ([], h1 :: hn, dm) = let
		    fun cheapest (h1, _, [], hn') = (h1, hn')
		      | cheapest (h1, c1, h2 :: hn, hn') = let
			    val c2 = spillCost' h2
			in
			    if c2 < c1 then
				cheapest (h2, c2, hn, h1 :: hn')
			    else
				cheapest (h1, c1, hn, h2 :: hn')
			end
		    val (h1', hn') = cheapest (h1, spillCost' h1, hn, [])
		in
		    finish (h1', select (h1', [], hn', dm))
		end
	      | try (l1 :: ln, high, dm) =
		  finish (l1, select (l1, ln, high, dm))

	    and finish (n, (low, high, dm, adj)) =
		pickColor (n, adj, try (low, high, dm))
	in
	    try (low, high, dm)
	end
end
