(* treeify.sml
 *
 *   Turning closed ANF into imperative basic blocks while
 *   "re-growing" expression trees.
 *   Expression trees make it possible to do instruction selection
 *   by tree tiling.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Treeify : sig

    val treeify : Closed.cluster -> BBTree.cluster

end = struct

    fun bug m = ErrorMsg.impossible ("Treeify: " ^ m)

    structure C = Closed
    structure B = BBTree
    structure M = LVar.Map
    structure TO = TreeOps

    structure LM = Label.Map

    fun ucount e =
	let infix ++ val op ++ = M.unionWith op +
	    fun value (C.VAR v) = M.singleton (v, 1)
	      | value (C.INT _ | C.LABEL _) = M.empty
	    fun slice (C.SGT x) = value x
	      | slice (C.SEQ { base, start, stop }) =
		  value base ++ value start ++ value stop
	    fun slicelist [] = M.empty
	      | slicelist (s :: sl) = slice s ++ slicelist sl
	    fun valuelist [] = M.empty
	      | valuelist (x :: xl) = xxl (x, xl)
	    and xxl (x, xl) = value x ++ valuelist xl
	    fun exp (C.VALUES xl) = valuelist xl
	      | exp (C.BIND (_, x, e)) = value x ++ exp e
	      | exp (C.CALL (_, _, (x, xl), e)) = xxl (x, xl) ++ exp e
	      | exp (C.ARITH (_, x, y, _, e)) = value x ++ value y ++ exp e
	      | exp (C.RECORD (_, x, sl, _, e)) =
		  value x ++ slicelist sl ++ exp e
	      | exp (C.SELECT (x, y, _, _, e)) = value x ++ value y ++ exp e
	      | exp (C.UPDATE (x, y, z, e)) =
		  value x ++ value y ++ value z ++ exp e
	      | exp (C.CMP (_, x, y, (_, xl), (_, yl))) =
		  xxl (x, xl) ++ xxl (y, yl)
	      | exp (C.JUMP (x, xl)) = xxl (x, xl)
	      | exp (C.GETSP (_, e)) = exp e
	      | exp (C.SETSP (x, e)) = value x ++ exp e
	      | exp (C.MAYJUMP (_, e)) = exp e
	in exp e
	end

    fun isSimple (B.FETCH (B.TEMP _)) = true
      | isSimple (B.NAME _) = true
      | isSimple (B.CONST _) = true
      | isSimple _ = false

    fun gett v = B.FETCH (B.TEMP v)

    fun find (m, v) =
	case M.find (m, v) of
	    SOME t => t
	  | NONE => gett v

    fun delete (m, v) = #1 (M.remove (m, v)) handle _ => m

    fun bind1 (v, t, b) = B.MOVE (B.TEMP v, t, b)
			      
    fun treeify { entryblocks, labelblocks } =
	let
	    val labelmap =
		foldl (fn ((l, vl, _), m) => LM.insert (m, l, vl))
		      LM.empty labelblocks
	    fun getbranchformals l =
		case LM.find (labelmap, l) of
		    SOME vl => vl
		  | NONE => bug "unexpected branch label"

	    val extrablocks = ref []

	    fun oneblock (l, vl, e) =
		let val counts = ucount e
		    fun usage v = getOpt (M.find (counts, v), 0)

		    fun h0 x = x

		    fun value (C.VAR v, m) =
			(let val (m', t) = M.remove (m, v)
			 in if isSimple t orelse usage v < 2 then (t, h0, m')
			    else (gett v, fn b => bind1 (v, t, b), m')
			 end
			 handle LibBase.NotFound => (gett v, h0, m))
		      | value (C.INT i, m) = (B.CONST i, h0, m)
		      | value (C.LABEL l, m) = (B.NAME l, h0, m)

		    fun valuelist ([], m) = ([], h0, m)
		      | valuelist (x :: xl, m) =
			  let val (t, h1, m') = value (x, m)
			      val (tl, h2, m'') = valuelist (xl, m')
			  in (t :: tl, h1 o h2, m'')
			  end

		    fun toBop Oper.PLUS = TO.PLUS
		      | toBop Oper.MINUS = TO.MINUS
		      | toBop Oper.TIMES = TO.MUL
		      | toBop Oper.DIV = TO.DIV
		      | toBop Oper.MOD = TO.MOD

		    fun toRop Oper.EQ = TO.EQ
		      | toRop Oper.LTEQ = TO.LE
		      | toRop Oper.LT = TO.LT
		      | toRop Oper.GTEQ = TO.GE
		      | toRop Oper.GT = TO.GT
		      | toRop Oper.NEQ = TO.NE

		    fun plus (B.CONST i, B.CONST j) = B.CONST (i + j)
		      | plus (B.CONST 0, t') = t'
		      | plus (t, B.CONST 0) = t
		      | plus (t, t') = B.BINOP (TO.PLUS, t, t')

		    fun minus (B.CONST i, B.CONST j) = B.CONST (i - j)
		      | minus (t, B.CONST 0) = t
		      | minus (t, t') = B.BINOP (TO.MINUS, t, t')

		    fun gctest (0, e) = e
		      | gctest (i, e) = B.GCTEST (B.CONST i, e)

		    fun rref (t, t') = B.MEM (plus (t, t'))
		    fun sel (t, t') = B.FETCH (rref (t, t'))

		    fun exp (C.VALUES xl, m) =
			  let val (tl, h, _) = valuelist (xl, m)
			  in (h (B.RETURN tl), 0)
			  end
		      | exp (C.BIND (v, x, e), m) =
			  let val (t, h, m') = value (x, m)
			      val (e', off) = exp (e, M.insert (m', v, t))
			  in (h e', off)
			  end
		      | exp (C.CALL (ta, vl, (x, xl), e), m) =
			  let val (t, h1, m1) = value (x, m)
			      val (tl, h2, m2) = valuelist (xl, m1)
			      val (e', off) = exp (e, m2)
			  in (h1 (h2 (B.CALL (map B.TEMP vl, t, tl,
					      gctest (off, e')))),
			      0)
			  end
		      | exp (C.ARITH (aop, x, y, v, e), m) =
			  let val (t1, h1, m1) = value (x, m)
			      val (t2, h2, m2) = value (y, m1)
			      val (e', off) =
				  if Oper.purearith aop then
				      exp (e, M.insert (m2, v,
						B.BINOP (toBop aop, t1, t2)))
				  else
				      let val (e'', off) = exp (e, m2)
				      in (bind1 (v, B.BINOP (toBop aop,
							     t1, t2),
						 e''),
					  off)
				      end
			  in (h1 (h2 e'), off)
			  end
		      | exp (C.RECORD (_, x0, sl, v, e), m) =
			  let fun inc off = off + MachSpec.wordSize
			      fun init ([], m) =
				    let val (e, off) = exp (e, m)
				    in (e, SOME off, off)
				    end
				| init (C.SGT x :: sl, m) =
				    let val (t, h, m') = value (x, m)
					val (b, off, off0) = init (sl, m')
				    in (h (B.ALLOCWRITE (t, b)),
					Option.map inc off, off0)
				    end
				| init (C.SEQ { base, start, stop } :: sl, m) =
				    let val (bt, bh, m') = value (base, m)
					val (st, sh, m'') = value (start, m)
					val (et, eh, m''') = value (stop, m)
					val (b, _, off0) = init (sl, m''')
					val tmp = LVar.new "start"
				    in (bh (sh (eh (bind1 (tmp, st,
					B.ALLOCCOPY (plus (bt, gett tmp),
						     minus (et, gett tmp),
						     b))))),
					NONE, off0)
				    end
			      val (t0, h0, m0) = value (x0, m)
			      val (e, offopt, off0) = init (sl, m0)
			      val lv = LVar.new "len"
			      val (gch, off') =
				  case offopt of
				      SOME off => (fn e => e, inc off)
				    | NONE =>
				        (fn e =>
					    B.GCTEST (plus (gett lv,
							    B.CONST (inc off0)),
						      e),
					 0)
			      val e' =
				  h0 (bind1 (lv, t0,
				       gch (
				        B.ALLOCWRITE (gett lv,
					 bind1 (v, plus (B.FETCH B.ALLOCPTR,
							 B.CONST (inc 1)),
						e)))))
			  in (e', off')
			  end
		      | exp (C.SELECT (x, y, Purity.Pure, v, e), m) =
			  let val (t1, h1, m1) = value (x, m)
			      val (t2, h2, m2) = value (y, m1)
			      val (e', off) =
				  exp (e, M.insert (m2, v, sel (t1, t2)))
			  in (h1 (h2 e'), off)
			  end
		      | exp (C.SELECT (x, y, Purity.Impure, v, e), m) =
 			  let val (t1, h1, m1) = value (x, m)
			      val (t2, h2, m2) = value (y, m1)
			      val (e', off) = exp (e, m2)
			  in (h1 (h2 (bind1 (v, sel (t1, t2), e'))), off)
			  end
		      | exp (C.UPDATE (x, y, z, e), m) =
			  let val (t1, h1, m1) = value (x, m)
			      val (t2, h2, m2) = value (y, m1)
			      val (t3, h3, m3) = value (z, m2)
			      val (e', off) = exp (e, m3)
			  in (h1 (h2 (h3 (B.MOVE (rref (t1, t2), t3, e')))),
			      off)
			  end
		      | exp (C.CMP (cop, x, y, (tl, txl), (fl, fxl)), m) =
			  let val (tx, hx, m1) = value (x, m)
			      val (ty, hy, m2) = value (y, m1)
			      fun xfer (l, []) = l
				| xfer (l, xl) =
				    let val (tl, h, _) = valuelist (xl, m2)
					val vl = getbranchformals l
					val l' = Label.new NONE
					val nb =
					    (l', h (ListPair.foldl bind1
								   (B.JUMP l)
								   (vl, tl)))
				    in extrablocks := nb :: !extrablocks;
				       l'
				    end
			  in (hx (hy (B.CJUMP (toRop cop, tx, ty,
					       xfer (tl, txl),
					       xfer (fl, fxl)))),
			      0)
			  end
		      | exp (C.JUMP (x, xl), m) =
			  let val (tl, h, m') = valuelist (xl, m)
			      fun build (vl, b) =
				  h (ListPair.foldl bind1 b (vl, tl))
			      val e' =
				  case x of
				      C.VAR v =>
			                let val (t, h', _) = value (x, m')
					in h' (h (B.TCALL (t, tl)))
					end
				    | C.LABEL l =>
				        build (getbranchformals l, B.JUMP l)
				    | C.INT _ => bug "unexpected INT in JUMP"
			  in (e', 0)
			  end
		      | exp (C.GETSP (v, e), m) =
			  exp (e, M.insert (m, v, B.FETCH B.STACKPTR))
		      | exp (C.SETSP (x, e), m) =
			  let val (t, h, m') = value (x, m)
			      val (e', off) = exp (e, m')
			  in (h (B.MOVE (B.STACKPTR, t, e')), off)
			  end
		      | exp (C.MAYJUMP (_, e), m) =
			  exp (e, m)
		    val (e', off) = exp (e, M.empty)
		in (l, gctest (off, e'))
		end
	    fun oneeblock (lab, vl, e, eh) = (vl, oneblock (lab, vl, e), eh)
	    val entryblocks = map oneeblock entryblocks
	    val labelblocks0 = map oneblock labelblocks
	in { entryblocks = entryblocks,
	     labelblocks = !extrablocks @ labelblocks0 }
	end
end
