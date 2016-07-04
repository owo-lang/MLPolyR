(* fclusters.sml
 *
 *   This module "clusterifies" the output of closure conversion.
 *   A cluster consists of a number of entry blocks and a number
 *   of labelled (non-entry-) blocks.  Each cluster is the smallest
 *   set of blocks such that direct jumps (to explicit labels) stay
 *   within the current cluster.
 *
 *   A cluster is the closest thing to a C-like function that there is
 *   in MLPolyR.  The main difference between a cluster and an actual
 *   C function is that the cluster can have multiple entry points.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure FunctionClusters : sig

    type clusters = { entrylabel: Label.label, clusters : Closed.cluster list }

    val clusterify : Closed.program -> clusters

end = struct

    structure M = Label.Map
    structure S = Label.Set
    structure C = Closed

    type clusters = { entrylabel: Label.label, clusters: Closed.cluster list }

    fun clusterify { entrypoint, calltargets, jumptargets } =
	let fun enterblock ((l, vl, b), m) = M.insert (m, l, (l, vl, b))
	    fun entereblock ((l, vl, b, eh), m) =
		M.insert (m, l, (l, vl, b, eh))
	    val jm = foldl enterblock M.empty jumptargets
	    val cm = foldl entereblock M.empty (entrypoint :: calltargets)

	    fun has ({ entryblocks, labelblocks, labset }, l) =
		S.member (labset, l)

	    fun findCluster ([], _) = NONE
	      | findCluster (c1 :: cs, l) =
		  if has (c1, l) then SOME (c1, cs)
		  else (case findCluster (cs, l) of
			    NONE => NONE
			  | SOME (cl, other) => SOME (cl, c1 :: other))

	    fun addj (blk as (l, _, _),
		      { entryblocks, labelblocks, labset }) =
		{ entryblocks = entryblocks,
		  labelblocks = blk :: labelblocks,
		  labset = S.add (labset, l) }

	    fun addmj (blk as (l, _, _, _),
		       { entryblocks, labelblocks, labset }) =
		{ entryblocks = blk :: entryblocks,
		  labelblocks = labelblocks,
		  labset = S.add (labset, l) }

	    fun merge ({ entryblocks = e1, labelblocks = l1, labset = s1 },
		       { entryblocks = e2, labelblocks = l2, labset = s2 }) =
		{ entryblocks = e1 @ e2,
		  labelblocks = l1 @ l2,
		  labset = S.union (s1, s2) }

	    fun labelsOf e =
		let fun value (C.LABEL l) = S.singleton l
		      | value (C.VAR _ | C.INT _) = S.empty
		    fun slice (C.SGT x) = value x
		      | slice (C.SEQ { base, start, stop }) =
			  S.union (value base,
				   S.union (value start, value stop))
		    fun slicelist [] = S.empty
		      | slicelist (s :: sl) = S.union (slice s, slicelist sl)
		    fun valuelist [] = S.empty
		      | valuelist (x :: xl) = S.union (value x, valuelist xl)
		    fun addc (s, (cs, js, mjs)) = (S.union (s, cs), js, mjs)
		    fun addmj (l, (cs, js, mjs)) =
			(S.add (cs, l), js, S.add (mjs, l))
		    fun exp (C.VALUES xl) = (valuelist xl, S.empty, S.empty)
		      | exp (C.BIND (_, x, e)) = addc (value x, exp e)
		      | exp (C.CALL (_, _, (x, xs), e)) =
			  addc (valuelist (x :: xs), exp e)
		      | exp (C.ARITH (_, x, y, _, e)) =
			  addc (valuelist [x, y], exp e)
		      | exp (C.RECORD (_, x, sl, _, e)) =
			  addc (S.union (value x, slicelist sl), exp e)
		      | exp (C.SELECT (x, y, _, _, e)) =
			  addc (valuelist [x, y], exp e)
		      | exp (C.UPDATE (x, y, z, e)) =
			  addc (valuelist [x, y, z], exp e)
		      | exp (C.CMP (_, x, y, (l1, xl1), (l2, xl2))) =
			  (valuelist (x :: y :: xl1 @ xl2),
			   S.add (S.singleton l1, l2),
			   S.empty)
		      | exp (C.JUMP (x, xl)) = (valuelist xl, value x, S.empty)
		      | exp (C.GETSP (_, e)) = exp e
		      | exp (C.SETSP (x, e)) = addc (value x, exp e)
		      | exp (C.MAYJUMP (l, e)) = addmj (l, exp e)
		    val (cs, js, mjs) = exp e
		in (S.listItems cs, S.listItems js, S.listItems mjs)
		end

	    fun doc ([], _, clusters) = clusters
	      | doc (c :: cs, done, clusters) =
		  if S.member (done, c) then doc (cs, done, clusters)
		  else (case M.find (cm, c) of
			    NONE => (* external call *)
			      doc (cs, S.add (done, c), clusters)
			  | SOME (l, vl, b, eh) =>
			      let val (bcl, bjl, bmjl) = labelsOf b
			      in dol ({ entryblocks = [(l, vl, b, eh)],
					labelblocks = [],
					labset = S.singleton l },
				      bjl, bmjl,
				      bcl @ cs,
				      S.add (done, c),
				      clusters)
			      end)

	    and dol (cc, [], [], cs, done, clusters) =
		  doc (cs, done, cc :: clusters)
	      | dol (cc, [], mj :: mjs, cs, done, clusters) =
		  (case findCluster (clusters, mj) of
		       NONE =>
		         if has (cc, mj) then
			     dol (cc, [], mjs, cs, done, clusters)
			 else (case M.find (cm, mj) of
				   NONE =>
				     (* this should never happen *)
				     dol (cc, [], mjs, cs, done, clusters)
				 | SOME (blk as (l, vl, b, eh)) =>
				     let val (bcl, bjl, bmjl) = labelsOf b
				     in dol (addmj (blk, cc),
					     bjl, bmjl @ mjs,
					     bcl @ cs, done,
					     clusters)
				     end)
		     | SOME (mjcluster, otherclusters) =>
		         dol (merge (cc, mjcluster), [], mjs, cs, done,
			      otherclusters))
	      | dol (cc, j :: js, mjs, cs, done, clusters) =
		  (case findCluster (clusters, j) of
		       NONE =>
		         if has (cc, j) then
			     dol (cc, js, mjs, cs, done, clusters)
			 else (case M.find (jm, j) of
				   NONE =>
				     (* can this happen? *)
				     dol (cc, js, mjs, cs, done, clusters)
				 | SOME (blk as (l, vl, b)) =>
				     let val (bcl, bjl, bmjl) = labelsOf b
				     in dol (addj (blk, cc),
					     bjl @ js, bmjl @ mjs,
					     bcl @ cs, done,
					     clusters)
				     end)
		     | SOME (jcluster, otherclusters) =>
		         dol (merge (cc, jcluster), js, mjs, cs, done,
			      otherclusters))

	    val clusters = doc ([#1 entrypoint], S.empty, [])

	    fun trim { entryblocks, labelblocks, labset } =
		{ entryblocks = entryblocks, labelblocks = labelblocks }
	in { entrylabel = #1 entrypoint, clusters = map trim clusters }
	end
end
