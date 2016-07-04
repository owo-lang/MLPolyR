(* flatten.sml
 *
 *   Perform header-transformation (eta-splitting)
 *   to flatten parameter list.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Flatten : sig

    val transform: ANF.function -> ANF.function

end = struct

    val K = MachSpec.numArgs

    structure A = ANF
    structure M = LVar.Map
    structure S = LVar.Set

    fun bug m = ErrorMsg.impossible ("Flatten: " ^ m)

    fun getinfo f =
	let val m = ref M.empty

	    fun function { f = (f, vl, e), inl, hdlr } =
		let fun candidate v =
			m := M.insert (!m, v, (f, ref (SOME [])))

		    fun sel (v, i, w) =
			case M.find (!m, v) of
			    NONE => ()
			  | SOME (_, ref NONE) => ()
			  | SOME (f', r as ref (SOME im)) =>
			      if f = f' then
				  (r := SOME ((i, w) :: im);
				   candidate w)
			      else r := NONE

		    fun var v =
			case M.find (!m, v) of
			    NONE => ()
			  | SOME (_, r) => r := NONE

		    fun value (A.VAR v) = var v
		      | value _ = ()

		    fun slice (A.SGT x) = value x
		      | slice (A.SEQ { base, start, stop }) =
			  (value base; value start; value stop)

		    fun exp _ (A.VALUES xl) =
			  app value xl
		      | exp r (A.BIND (_, x, e)) =
			  (* we expect this case not to happen because
			   * earlier rounds get rid of it *)
			  (value x; exp r e)
		      | exp r (A.CALL (_, _, (x, xl), e)) =
			  (value x; app value xl; exp r e)
		      | exp r (A.FIX (fl, e)) =
			  (app function fl; exp r e)
		      | exp r (A.ARITH (_, x, y, _, e)) =
			  (value x; value y; exp r e)
		      | exp r (A.RECORD (_, x, sl, _, e)) =
			  (value x; app slice sl; exp r e)
		      | exp false (A.SELECT (A.VAR v, A.INT i,
					     Purity.Pure, w, e)) =
			  (sel (v, i, w); exp false e)
		      | exp r (A.SELECT (x, y, _, _, e)) =
			  (value x; value y; exp r e)
		      | exp r (A.UPDATE (x, y, z, e)) =
			  (value x; value y; value z; exp r e)
		      | exp _ (A.CMP (_, x, y, et, ef)) =
			  (value x; value y; exp true et; exp true ef)
		      | exp _ (A.JUMP (_, (x, xl))) =
			  (value x; app value xl)
		      | exp r (A.GETSP (v, e)) =
			  exp r e
		      | exp r (A.SETSP (x, e)) =
			  (value x; exp r e)
		      | exp r (A.MAYJUMP (v, e)) =
			  (var v; exp r e)
		in app candidate vl;
		   exp false e
		end
	in function f;
	   !m
	end

    fun transform (f as { f = (fname, vl, e), inl, hdlr }) =
	let val m = getinfo f
	    fun grow (_, newformals, [], rsel, elims) =
		  (rev newformals, rsel, elims)
	      | grow (0, newformals1, newformals2, rsel, elims) =
		  (List.revAppend (newformals1, newformals2), rsel, elims)
	      | grow (k, nf1, h :: t, rsel, elims) =
		  (case M.find (m, h) of
		       NONE =>
		         grow (k, h :: nf1, t, rsel, elims)
		     | SOME (_, ref NONE) =>
		         grow (k, h :: nf1, t, rsel, elims)
		     | SOME (_, ref (SOME im)) =>
		         let val n = length im - 1
			 in if n > k then
				grow (k, h :: nf1, t, rsel, elims)
			    else let val targets = map #2 im
				 in grow (k - n, nf1,
					  targets @ t,
					  map (fn (i, v) => (h, i, v)) im @
					  rsel,
					  targets @ elims)
				 end
			 end)
	    fun onefun ({ f = (f, vl, e), inl, hdlr }, fl) =
		case grow (K - length vl, [], vl, [], []) of
		      (_, _, []) => { f = (f, vl, rewrite (S.empty, e)),
				      inl = inl, hdlr = hdlr } :: fl
		  | (vl', rsel, elims) =>
		      let val f' = LVar.clone f
			  fun get m v = getOpt (M.find (m, v), v)
			  fun rename (v, m) =
			      let val v' = LVar.clone v
			      in (v', M.insert (m, v, v'))
			      end
			  fun rename' ([], m) = ([], m)
			    | rename' (h :: t, m) =
			        let val (h', m') = rename (h, m)
				    val (t', m'') = rename' (t, m')
				in (h' :: t', m'')
				end
			  val (vl'', m) = rename' (vl, M.empty)
			  fun build ([], m) =
			        (A.JUMP (Purity.Impure,
					 (A.VAR f',
					  map (A.VAR o get m) vl')))
			    | build ((v, i, w) :: sel, m) =
			        let val v' = get m v
				    val (w', m') = rename (w, m)
				    val b = build (sel, m')
				in A.SELECT (A.VAR v', A.INT i,
					     Purity.Pure, w', b)
				end
			  val b = build (rev rsel, m)
			  val s = S.addList (S.empty, elims)
			  val b' = rewrite (s, e)
		      in { f = (f, vl'', b), inl = true, hdlr = hdlr } ::
			 { f = (f', vl', b'), inl = inl, hdlr = hdlr } ::
			 fl
		      end
	    and rewrite (s, e) =
		let fun exp (e as A.VALUES _) = e
		      | exp (A.BIND (v, x, e)) =
			  A.BIND (v, x, exp e)
		      | exp (A.CALL (p, vl, (x, xl), e)) =
			  A.CALL (p, vl, (x, xl), exp e)
		      | exp (A.FIX (fl, e)) =
			  A.FIX (foldr onefun [] fl, exp e)
		      | exp (A.ARITH (aop, x, y, v, e)) =
			  A.ARITH (aop, x, y, v, exp e)
		      | exp (A.RECORD (p, x, sl, v, e)) =
			  A.RECORD (p, x, sl, v, exp e)
		      | exp (A.SELECT (x, y, p, v, e)) =
			  if S.member (s, v) then exp e
			  else A.SELECT (x, y, p, v, exp e)
		      | exp (A.UPDATE (x, y, z, e)) =
			  A.UPDATE (x, y, z, exp e)
		      | exp (A.CMP (cop, x, y, et, ef)) =
			  A.CMP (cop, x, y, exp et, exp ef)
		      | exp (A.GETSP (v, e)) =
			  A.GETSP (v, exp e)
		      | exp (A.SETSP (x, e)) =
			  A.SETSP (x, exp e)
		      | exp (A.MAYJUMP (v, e)) =
			  A.MAYJUMP (v, exp e)
		      | exp (e as A.JUMP _) = e
		in exp e
		end
	in { f = (fname, vl, rewrite (S.empty, e)), inl = inl, hdlr = hdlr }
	end
end
