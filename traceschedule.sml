(* traceschedule.sml
 *
 *   Trace-scheduling basic blocks.
 *   This code is based on Andrew Appel's book "Modern Compiler
 *   Implementation in ML".
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure TraceSchedule : sig

    val schedule : BBTree.cluster -> TraceTree.entrytrace

end = struct

    structure L = Label
    structure M = L.Map
    structure B = BBTree
    structure T = TraceTree

    type label = Label.label

    fun bug m = ErrorMsg.impossible ("TraceSchedule: " ^ m)

    fun schedule { entryblocks, labelblocks } =
	let fun adde ((vl, (l, b), eh), m) = M.insert (m, l, (SOME (vl,eh), b))
	    fun addl ((l, b), m) = M.insert (m, l, (NONE, b))
	    val table = foldl addl (foldl adde M.empty entryblocks) labelblocks

	    fun findjt (table, l) =
		case M.find (table, l) of
		    NONE => NONE
		  | SOME (NONE, b) => SOME b
		  | SOME (SOME _, _) => bug "(c)jump to entry point"

	    fun mktrace (table, (l, b), q) =
		let val table = #1 (M.remove (table, l))
		    fun build (B.JUMP l') =
			  (case findjt (table, l') of
			       NONE => T.JUMP (l', more (table, q))
			     | SOME b' =>
		                 T.LABEL (mktrace (table, (l', b'), q)))
		      | build (B.TCALL (e, el)) =
			  T.TCALL (e, el, more (table, q))
		      | build (B.RETURN e) =
			  T.RETURN (e, more (table, q))
		      | build (B.CJUMP (r, e1, e2, t, f)) =
			  (case findjt (table, f) of
			       NONE =>
		                 (case findjt (table, t) of
				      NONE =>
			                T.CJUMP (r, e1, e2, t,
						 (Label.new NONE,
						  T.JUMP (f, more (table, q))))
				    | SOME b' =>
			                T.CJUMP (TreeOps.notRel r, e1, e2, f,
						 mktrace (table, (t, b'), q)))
			     | SOME b' =>
		                 T.CJUMP (r, e1, e2, t,
					  mktrace (table, (f, b'), t :: q)))
		      | build (B.MOVE (le, e, b')) =
			  T.MOVE (le, e, build b')
		      | build (B.CALL (lel, e, el, b')) =
			  T.CALL (lel, e, el, build b')
		      | build (B.DOEXP (e, b')) =
			  T.DOEXP (e, build b')
		      | build (B.DOCALL (e, el, b')) =
			  T.DOCALL (e, el, build b')
		      | build (B.GCTEST (e, b')) =
			  T.GCTEST (e, build b')
		      | build (B.ALLOCWRITE (e, b')) =
			  T.ALLOCWRITE (e, build b')
		      | build (B.ALLOCCOPY (frombase, len, b')) =
			  T.ALLOCCOPY (frombase, len, build b')
		in (l, build b)
		end

	    and more (_, []) = T.END
	      | more (table, l :: rest) =
		  case M.find (table, l) of
		      SOME (SOME (vl, eh), b) =>
		        T.ENTRY (vl, mktrace (table, (l, b), rest), eh)
		    | SOME (NONE, b) =>
		        T.JTARGET (mktrace (table, (l, b), rest))
		    | NONE =>
		        more (table, rest)
	in case entryblocks of
	       (vl, eb, eh) :: ebs =>
	         (vl, mktrace (table, eb, map (#1 o #2) ebs), eh)
	     | _ => bug "no entry block"
	end
end
