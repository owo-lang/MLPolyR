(* value-numbering.sml
 *
 *   Simple Common Subexpression Elimination (CSE) by Value Numbering
 *   within basic blocks.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure ValueNumbering : sig

    val block_cse : Closed.block -> Closed.block

    val cluster_cse : Closed.cluster -> Closed.cluster

end = struct

    structure C = Closed

    val callidx = 0
    val recordidx = 1
    val selectidx = 2
    fun arithidx Oper.PLUS = 3
      | arithidx Oper.MINUS = 4
      | arithidx Oper.TIMES = 5
      | arithidx Oper.DIV = 6
      | arithidx Oper.MOD = 7

    fun valuecompare (C.INT i, C.INT i') = LiteralData.compare (i, i')
      | valuecompare (C.INT _, _) = GREATER
      | valuecompare (_, C.INT _) = LESS
      | valuecompare (C.LABEL l, C.LABEL l') = Label.compare (l, l')
      | valuecompare (C.LABEL _, _) = GREATER
      | valuecompare (_, C.LABEL _) = LESS
      | valuecompare (C.VAR v, C.VAR v') = LVar.compare (v, v')

    and valuelistcompare (l, l') = List.collate valuecompare (l, l')

    and slicecompare (C.SGT x, C.SGT x') = valuecompare (x, x')
      | slicecompare (C.SGT _, C.SEQ _) = GREATER
      | slicecompare (C.SEQ _, C.SGT _) = LESS
      | slicecompare (C.SEQ s, C.SEQ s') =
	  valuelistcompare ([#base s, #start s, #stop s],
			    [#base s', #start s', #stop s'])

    and slicelistcompare (l, l') = List.collate slicecompare (l, l')

    fun compare ((i, sl), (i', sl')) =
	case Int.compare (i, i') of
	    EQUAL => slicelistcompare (sl, sl')
	  | unequal => unequal

    structure M = RedBlackMapFn (type ord_key = int * C.slice list
                                 val compare = compare)
    structure EM = LVar.Map

    fun repr (v, eq) = getOpt (EM.find (eq, v), C.VAR v)

    fun block_cse (l, vl, e) =
	let fun value (C.VAR v, eq) = repr (v, eq)
	      | value (x as (C.INT _ | C.LABEL _), _) = x

	    fun valuelist ([], _) = []
	      | valuelist (x :: xl, eq) = value (x, eq) :: valuelist (xl, eq)

	    fun slice (C.SGT x, eq) = C.SGT (value (x, eq))
	      | slice (C.SEQ { base, start, stop }, eq) =
		  C.SEQ { base = value (base, eq),
			  start = value (start, eq),
			  stop = value (stop, eq) }

	    fun slicelist ([], _) = []
	      | slicelist (s :: sl, eq) = slice (s, eq) :: slicelist (sl, eq)

	    fun jtarget ((x, xl), eq) = (value (x, eq), valuelist (xl, eq))

	    fun sgtkey (idx, xl) = (idx, map C.SGT xl)
	    fun callkey (x, xl) = sgtkey (callidx, x :: xl)
	    fun recordkey (x, sl) = (recordidx, C.SGT x :: sl)
	    fun selectkey (x, y) = sgtkey (selectidx, [x, y])

	    fun arithkey (aop, x, y) =
		let val idx = arithidx aop
		in if Oper.commutative aop then
		       case valuecompare (x, y) of
			   GREATER => sgtkey (idx, [y, x])
			 | _ => sgtkey (idx, [x, y])
		   else sgtkey (idx, [x, y])
		end

	    fun memo (k, v, e, m, eq, c) =
		case M.find (m, k) of
		    SOME y => exp (e, m, EM.insert (eq, v, y))
		  | NONE => c (exp (e, M.insert (m, k, C.VAR v), eq))

	    and exp (C.VALUES xl, _, eq) = C.VALUES (valuelist (xl, eq))
	      | exp (C.BIND (v, x, e), m, eq) =
		  exp (e, m, EM.insert (eq, v, value (x, eq)))
	      | exp (C.CALL (Purity.Pure, [v], jt, e), m, eq) =
		  let val (x', xl') = jtarget (jt, eq)
		  in memo (callkey (x', xl'), v, e, m, eq,
			   fn b => C.CALL (Purity.Pure, [v], (x', xl'), b))
		  end
	      | exp (C.CALL (p, vl, jt, e), m, eq) =
		  C.CALL (p, vl, jtarget (jt, eq), exp (e, m, eq))
	      | exp (C.ARITH (aop, x, y, v, e), m, eq) =
		  let val (x', y') = (value (x, eq), value (y, eq))
		  in memo (arithkey (aop, x', y'), v, e, m, eq,
			   fn b => C.ARITH (aop, x', y', v, b))
		  end
	      | exp (C.RECORD (Purity.Impure, x, sl, v, e), m, eq) =
		  C.RECORD (Purity.Impure,
			    value (x, eq), slicelist (sl, eq),
			    v, exp (e, m, eq))
	      | exp (C.RECORD (Purity.Pure, x, sl, v, e), m, eq) =
		 let val x' = value (x, eq)
		     val sl' = slicelist (sl, eq)
		 in memo (recordkey (x', sl'), v, e, m, eq,
			  fn b => C.RECORD (Purity.Pure, x', sl', v, b))
		 end
	      | exp (C.SELECT (x, y, Purity.Impure, v, e), m, eq) =
		  C.SELECT (value (x, eq), value (y, eq), Purity.Impure, v,
			    exp (e, m, eq))
	      | exp (C.SELECT (x, y, Purity.Pure, v, e), m, eq) =
		  let val (x', y') = (value (x, eq), value (y, eq))
		  in memo (selectkey (x', y'), v, e, m, eq,
			   fn b => C.SELECT (x', y', Purity.Pure, v, b))
		  end
	      | exp (C.UPDATE (x, y, z, e), m, eq) =
		  C.UPDATE (value (x, eq), value (y, eq), value (z, eq),
			    exp (e, m, eq))
	      | exp (C.CMP (cop, x, y, (l1, xl1), (l2, xl2)), m, eq) =
		  C.CMP (cop, value (x, eq), value (y, eq),
			 (l1, valuelist (xl1, eq)), (l2, valuelist (xl2, eq)))
	      | exp (C.JUMP jt, _, eq) = C.JUMP (jtarget (jt, eq))
	      | exp (C.GETSP (v, e), m, eq) =
		  C.GETSP (v, exp (e, m, eq))
	      | exp (C.SETSP (x, e), m, eq) =
		  C.SETSP (value (x, eq), exp (e, m, eq))
	      | exp (C.MAYJUMP (l, e), m, eq) =
		  C.MAYJUMP (l, exp (e, m, eq))
	in (l, vl, exp (e, M.empty, EM.empty))
	end

    fun eblock_cse (l, vl, e, eh) =
	let val (l', vl', e') = block_cse (l, vl, e)
	in (l', vl', e', eh)
	end

    fun cluster_cse { entryblocks, labelblocks } =
	{ entryblocks = map eblock_cse entryblocks,
	  labelblocks = map block_cse labelblocks }
end
