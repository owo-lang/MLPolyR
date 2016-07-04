(* lambda2anf.sml
 *
 *   Conversion from straight Lambda to ANF.
 *
 * Copyright (c) 2007 by Matthias Blume (blume@tti-c.org)
 *)
structure LambdaToANF : sig

    val convert : Lambda.function -> ANF.function

end = struct

    structure L = Lambda
    structure A = ANF

    fun wt f = f (LVar.new "tmp")    (* with temporary *)
    fun wc (v, f) = f (LVar.clone v) (* with cloned temporary *)
    fun ws (s, f) = f (LVar.new s)   (* with named temporary (string) *)

    fun wf (NONE, f) = wt f	     (* with fresh variable *)
      | wf (SOME v, f) = wc (v, f)

    fun cont (NONE, x) = A.VALUES [x]
      | cont (SOME k, x) = k x

    fun call (NONE, _, p, a) = A.JUMP (p, a)
      | call (SOME k, v0, p, a) =
	  wf (v0, fn v => A.CALL (p, [v], a, k (A.VAR v)))

    fun ijump f xl = A.JUMP (Purity.Impure, (A.VAR f, xl))
    fun lam (f, vl, b, i, h) = { f = (f, vl, b), inl = i, hdlr = h }

    fun joinpt (NONE, _, b) = b NONE
      | joinpt (SOME k, v0, b) =
	  wt (fn f => wf (v0, fn v =>
	  A.FIX ([lam (f, [v], k (A.VAR v), false, false)],
	  b (SOME (fn x => ijump f [x])))))

    fun list f ([], k) = k []
      | list f (h :: t, k) = f (h, fn h' => list f (t, fn t' => k (h' :: t')))

    fun exp (L.VALUE v, _, k) = cont (k, v)
      | exp (L.LET (v, e, b), v0, k) =
	  exp (e, SOME v, SOME (fn x => A.BIND (v, x, exp (b, v0, k))))
      | exp (L.FIX (fl, b), v0, k) =
	  A.FIX (map convert fl, exp (b, v0, k))
      | exp (L.ARITH (aop, e1, e2), v0, k) =
	  wf (v0, fn v => ex (e1, fn x1 => ex (e2, fn x2 =>
	  A.ARITH (aop, x1, x2, v, cont (k, A.VAR v)))))
      | exp (L.RECORD { purity = m, len = e, slices = sl }, v0, k) =
	  wf (v0, fn v => ex (e, fn x =>
	  list slice (sl, fn sl' =>
	  A.RECORD (m, x, sl', v, cont (k, A.VAR v)))))
      | exp (L.SELECT (e1, e2, m), v0, k) =
	  wf (v0, fn v => ex (e1, fn x1 => ex (e2, fn x2 =>
	  A.SELECT (x1, x2, m, v, cont (k, A.VAR v)))))
      | exp (L.UPDATE (e1, e2, e3), _, k) =
	  ex (e1, fn x1 => ex (e2, fn x2 => ex (e3, fn x3 =>
	  A.UPDATE (x1, x2, x3, cont (k, A.INT 0)))))
      | exp (L.CMP (cop, e1, e2, et, ef), v0, k) =
	  wt (fn f => wf (v0, fn v =>
	  joinpt (k, v0, fn k' =>
	  ex (e1, fn x1 => ex (e2, fn x2 =>
	  A.CMP (cop, x1, x2, exp (et, v0, k'), exp (ef, v0, k')))))))
      | exp (L.APP (p, e, el), v0, k) =
	  wf (v0, fn v => ex (e, fn x => list ex (el, fn xl =>
          call (k, v0, p, (x, xl)))))
      | exp (L.HANDLER (hv, hvl, hb, b), v0, k) =
	  joinpt (k, v0, fn k' => wc (hv, fn hv' =>
	  A.FIX ([lam (hv', hvl, exp (hb, v0, k'), false, false)],
	  ws ("sp", fn oldsp => A.GETSP (oldsp,
	  list wc (hvl, fn hvl' =>
	  A.FIX ([lam (hv, hvl', A.SETSP (A.VAR oldsp,
				 ijump hv' (map A.VAR hvl')),
		       false, true)],
	  A.MAYJUMP (hv, exp (b, v0, k')))))))))

    and ex (e, k) = exp (e, NONE, SOME k)

    and slice (L.SGT e, k) = ex (e, fn x => k (A.SGT x))
      | slice (L.SEQ { base, start, stop }, k) =
	  ex (base, fn b => ex (start, fn s => ex (stop, fn p =>
	  k (A.SEQ { base = b, start = s, stop = p }))))

    and convert (f, vl, b, inl) = lam (f, vl, exp (b, NONE, NONE), inl, false)
end
