(* prfclusters.sml
 *
 *   Pretty-printing function clusters.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure PrintClusters : sig

    val print : (string -> unit) -> FunctionClusters.clusters -> unit

end = struct

    structure C = Closed

    fun print print { clusters, entrylabel } =
	let fun indent () = print "  "
	    fun nl () = print "\n"
	    fun var v = print (LVar.toString v)
	    fun varlist [] = ()
	      | varlist [v] = var v
	      | varlist (v :: vl) = (var v; print ","; varlist vl)
	    fun label l = print (Label.name l)
	    fun value (C.VAR v) = var v
	      | value (C.INT i) = print (LiteralData.toString i)
	      | value (C.LABEL l) = label l
	    fun valuelist [] = ()
	      | valuelist [x] = value x
	      | valuelist (x :: xl) = (value x; print ","; valuelist xl)
	    fun slice (C.SGT x) = value x
	      | slice (C.SEQ { base, start, stop }) =
		  (value base; print "["; value start; print "..";
		   value stop; print ")")
	    fun slicelist [] = ()
	      | slicelist [s] = slice s
	      | slicelist (s :: sl) = (slice s; print ","; slicelist sl)
	    fun jtarget (x, xl) =
		(value x; print "("; valuelist xl; print ")")
	    fun btarget (l, xl) =
		(label l; print "("; valuelist xl; print ")")
	    fun exp (C.VALUES xl) =
		  (indent (); print "return "; valuelist xl; nl ())
	      | exp (C.BIND (v, x, e)) =
		  (indent (); value x; print " -> "; var v; nl (); exp e)
	      | exp (C.CALL (ta, vl, jt, e)) =
		  (indent (); print (if ta = Purity.Pure then "typcall "
				     else "call ");
		   jtarget jt; print " -> ";
		   varlist vl; nl (); exp e)
	      | exp (C.ARITH (aop, x, y, v, e)) =
		  (indent (); value x; print (Oper.astring aop); value y;
		   print " -> "; var v; nl (); exp e)
	      | exp (C.RECORD (m, x, sl, v, e)) =
		  (indent (); if m = Purity.Impure then print "!" else ();
		   print "{"; value x; print ": ";
		   slicelist sl; print "} -> ";
		   var v; nl (); exp e)
	      | exp (C.SELECT (x, y, m, v, e)) =
		  (indent (); value x; print "[";
		   value y; if m = Purity.Impure then print "!"
			    else (); print "] -> ";
		   var v; nl (); exp e)
	      | exp (C.UPDATE (x, y, z, e)) =
		  (indent (); value x; print "!"; value y; print " := ";
		   value z; nl (); exp e)
	      | exp (C.CMP (cop, x, y, btt, btf)) =
		  (indent (); print "if "; value x; print (Oper.cstring cop);
		   value y; print " then goto "; btarget btt;
		   print " else goto "; btarget btf; nl ())
	      | exp (C.JUMP jt) =
		  (indent (); print "goto "; jtarget jt; nl ())
	      | exp (C.GETSP (v, e)) =
		  (indent (); print "$sp -> "; var v; nl (); exp e)
	      | exp (C.SETSP (x, e)) =
		  (indent (); value x; print " -> $sp"; nl (); exp e)
	      | exp (C.MAYJUMP (l, e)) =
		  (indent (); print "mayjump "; label l; nl (); exp e)
	    fun block (l, vl, e) =
		(label l; print "("; valuelist (map C.VAR vl); print "):";
		 nl (); exp e)
	    fun eblock (l, vl, e, eh) =
		(if eh then print "!" else (); block (l, vl, e))
	    fun cluster { entryblocks, labelblocks } =
		(print "========================================\n";
		 app eblock entryblocks;
		 print "----------------------------------------\n";
		 app block labelblocks)
	in print "**ENTRYPOINT: "; label entrylabel; nl ();
	   app cluster clusters
	end
end
