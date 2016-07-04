(* prbbtree.sml
 *
 *   Pretty-printing Basic-Block-Trees.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure PrintBBTree = struct

    structure B = BBTree

    fun prcluster print { entryblocks, labelblocks } =
	let fun nl () = print "\n"
	    fun temp t = print (LVar.toString t)
	    fun label l = print (Label.name l)
	    fun binop bop = print (TreeOps.binop2string bop)
	    fun relop rop = print (TreeOps.relop2string rop)
	    fun int i = if i < 0 then
			    (print "-"; print (LiteralData.toString (~i)))
			else print (LiteralData.toString i)
	    fun sint i = if i < 0 then int i else (print "+"; int i)
	    fun list f [] = ()
	      | list f [x] = f x
	      | list f (x :: xs) = (f x; print ","; list f xs)
	    fun lexp (B.MEM e) = (print "M["; exp e; print "]")
	      | lexp (B.TEMP t) = temp t
	      | lexp B.ALLOCPTR = print "$allocptr"
	      | lexp B.STACKPTR = print "$stackptr"
	    and exp (B.FETCH le) = lexp le
	      | exp (B.BINOP (bop, e1, e2)) =
		  (print "("; exp e1; binop bop; exp e2; print ")")
	      | exp (B.NAME l) = label l
	      | exp (B.CONST i) = int i
	    fun call (k, e, el) =
		(print k; print " "; exp e; print "(";
		 list exp el; print ")")
	    fun prpreblock (B.JUMP l) =
		  (print "  goto "; label l; nl ())
	      | prpreblock (B.TCALL (e, el)) =
		  (call ("  tailcall", e, el); nl ())
	      | prpreblock (B.RETURN el) =
		  (print "  return "; list exp el; nl ())
	      | prpreblock (B.CJUMP (rop, e1, e2, l1, l2)) =
		  (print "  if "; exp e1; relop rop; exp e2;
		   print " then goto "; label l1; print " else goto ";
		   label l2; nl ())
	      | prpreblock (B.CALL (lel, e, el, pb)) =
		  (print "  "; list lexp lel; print " <- ";
		   call ("call", e, el); nl (); prpreblock pb)
	      | prpreblock (B.MOVE (le, e, pb)) =
		  (print "  "; lexp le; print " <- "; exp e; nl ();
		   prpreblock pb)
	      | prpreblock (B.DOCALL (e, el, pb)) =
		  (print "  do "; call ("call", e, el); nl (); prpreblock pb)
	      | prpreblock (B.DOEXP (e, pb)) =
		  (print "  do "; exp e; nl (); prpreblock pb)
	      | prpreblock (B.GCTEST (e, pb)) =
		  (print "  *gctest "; exp e; nl (); prpreblock pb)
	      | prpreblock (B.ALLOCWRITE (e, pb)) =
		  (print "  M[++$allocptr] <- "; exp e; nl (); prpreblock pb)
	      | prpreblock (B.ALLOCCOPY (frombase, len, pb)) =
		  (print "  for i in [0.."; exp len;
		   print ") do M[++$allocptr] <- M["; exp frombase;
		   print "+i]"; nl (); prpreblock pb)
	    fun prblock (l, pb) =
		(label l; print ":"; nl (); prpreblock pb)
	    fun prentryblock (vl, (l, pb), eh) =
		(if eh then print "!" else ();
		 label l; print "("; list temp vl; print "):"; nl ();
		 prpreblock pb)
	in print "========================================\n";
	   app prentryblock entryblocks;
	   print "----------------------------------------\n";
	   app prblock labelblocks
	end
end
