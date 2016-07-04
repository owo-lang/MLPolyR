(* makegraph.sml
 *
 * Build flowgraph from instruction list for subsequent use by
 * liveness analyses.
 *
 * This code is based on Andrew Appel's book "Modern Compiler
 * Implementation in ML".
 *)
structure MakeGraph : sig
    val instrs2graph: Asm.instr list -> Flow.flowgraph * Graph.node list
end = struct

    fun bug m = ErrorMsg.impossible ("MakeGraph: " ^ m)

    structure F = Flow
    structure G = F.Graph
    structure A = Asm
    structure T = G.Map
    structure TS = LVar.Set
    structure LM = Label.Map

    fun add (t, n, l) = foldl (fn (x, t) => T.insert (t, n, x)) t l

    fun instrs2graph instrs = let
	val g = G.newGraph ()
	val nl = map (fn _ => G.newNode g) instrs
	fun regLab (A.LABEL lab, n, lmap) = LM.insert (lmap, lab, n)
	  | regLab (_, _, lmap) = lmap
	val lmap = ListPair.foldl regLab LM.empty (instrs, nl)
	val empty = TS.empty
	val single = TS.singleton
	fun set l = TS.addList (empty, l)

	fun mkEdges ([], [], use, def, ismove) = (use, def, ismove)
	  | mkEdges (hi :: ti, hn :: tn, use, def, ismove) =
	      let fun edges ll =
		      let fun edge l =
			      case LM.find (lmap, l) of
				  NONE => bug "bad label"
				| SOME n => G.mk_edge { from = hn, to = n }
		      in app edge ll
		      end
		  fun defedge sn = G.mk_edge { from = hn, to = sn }
		  fun continue (u, d, im) =
		      mkEdges (ti, tn,
			       T.insert (use, hn, u),
			       T.insert (def, hn, d),
			       T.insert (ismove, hn, im))
		  fun fst (sn :: _) = sn
		    | fst [] = bug "mkEdges(1)"
	      in case hi of
		     A.OPER { jmp = A.RETURN, src, ... } =>
		       continue (set src, empty, false)
		   | A.OPER { src, dst, jmp = A.JUMP ll, ... } =>
		       (edges ll;
			continue (set src, set dst, false))
		   | A.LABEL _ =>
		       (defedge (fst tn);
			continue (empty, empty, false))
		   | A.OPER { src, dst, jmp = A.NOJUMP, ... } =>
		       (defedge (fst tn);
			continue (set src, set dst, false))
		   | A.MOVE { src, dst, ... } =>
		       (defedge (fst tn);
			continue (single src, single dst, true))
		   | A.REGSAVE =>
		       (defedge (fst tn);
			continue (set Frame.calleesaves, empty, false))
		   | A.REGRESTORE =>
		       (defedge (fst tn);
			continue (empty, set Frame.calleesaves, false))
		   | A.NOSTACK =>
		       ( (* eventually we need to convey this info to
			  * the RA *)
			defedge (fst tn);
			continue (empty, empty, false))
	      end
	  | mkEdges _ = bug "mkEdges(2)"

	val (use, def, ismove) =
	    mkEdges (instrs, nl, T.empty, T.empty, T.empty)
    in (F.FGRAPH { control = g, def = def, use = use, ismove = ismove }, nl)
    end
end
