(* pranf.sml
 *
 *   Pretty-printing ANF.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure PrintANF : sig

    val exp : (string -> unit) -> ANF.exp -> unit
    val function : (string -> unit) -> ANF.function -> unit
    val value : (string -> unit) -> ANF.value -> unit

end = struct

    structure A = ANF
    structure O = Oper

    fun var pr v = pr (LVar.toString v)

    fun value pr (A.VAR v) = var pr v
      | value pr (A.LABEL l) = pr (Label.name l)
      | value pr (A.INT i) = pr (LiteralData.toString i)

    fun list pr f [] = ()
      | list pr f [x] = f x
      | list pr f (h :: t) = (f h; pr ","; list pr f t)

    fun spaces pr 0 = ()
      | spaces pr n = (pr "  "; spaces pr (n-1))

    fun function0 indent pr { f = (f, vl, e), inl, hdlr } =
	(spaces pr indent;
	 var pr f;
	 if hdlr then pr "!" else ();
	 pr "("; list pr (var pr) vl; pr ")=";
	 if inl then pr "=" else ();
	 exp0 (indent+1) pr e;
	 pr "\n")

    and exp0 indent pr e =
	let fun purity Purity.Pure = ()
	      | purity Purity.Impure = pr "!"
	    fun ar () = pr " <- "
	    fun indentation () = spaces pr indent
	    val var = fn v => var pr v
	    val value = fn x => value pr x
	    fun slice (A.SGT x) = value x
	      | slice (A.SEQ { base, start, stop }) =
		  (value base;
		   pr "{"; value start; pr ".."; value stop; pr "}")
	    fun arithop aop = pr (O.astring aop)
	    fun cmpop cop = pr (O.cstring cop)
	    fun exp e =
		(pr "\n";
		 indentation ();
		 case e of
		     A.VALUES xl => (pr "return "; list pr value xl)
		   | A.BIND (v, x, e) =>
	               (var v; ar (); value x; exp e)
		   | A.CALL (p, vl, (x, xl), e) =>
	               (list pr var vl; ar (); purity p;
			value x; pr "("; list pr value xl; pr ")";
			exp e)
		   | A.FIX (fl, e) =>
	               (pr "fix\n";
			app (function0 (indent+1) pr) fl;
			indentation ();
			pr "in";
			exp0 (indent+1) pr e)
		   | A.ARITH (aop, x, y, v, e) =>
		       (var v; ar (); value x; arithop aop; value y; exp e)
		   | A.RECORD (p, x, sl, v, e) =>
		       (var v; ar (); purity p; pr "[";
			list pr slice sl; pr "]("; value x; pr ")";
			exp e)
		   | A.SELECT (x, y, p, v, e) =>
		       (var v; ar (); value x; purity p; pr "."; value y;
			exp e)
		   | A.UPDATE (x, y, z, e) =>
		       (value x; pr "."; value y; pr " := "; value z;
			exp e)
		   | A.CMP (cop, x, y, et, ef) =>
		       (pr "if "; value x; cmpop cop; value y; pr " then";
			exp0 (indent+1) pr et;
			pr "\n"; indentation (); pr "else";
			exp0 (indent+1) pr ef)
		   | A.JUMP (p, (x, xl)) =>
		       (pr "goto "; purity p; value x; pr "(";
			list pr value xl; pr ")")
		   | A.GETSP (v, e) =>
		       (var v; ar (); pr "$sp"; exp e)
		   | A.SETSP (x, e) =>
		       (pr "$sp"; ar (); value x; exp e)
		   | A.MAYJUMP (v, e) =>
		       (pr "mayjump "; var v; exp e))
	in exp e
	end

    fun function pr f = function0 0 pr f
    fun exp pr e = exp0 0 pr e
end
