(* anf-opt.sml
 *
 *   A simple optimizer working on MLPolyR's ANF intermediate form.
 *   Optimizations:
 *      - constant folding
 *      - simple constant- and value propagation
 *      - eliminating useless bindings
 *      - short-circuiting RECORD-SELECT pairs
 *      - inlining of tiny functions
 *      - some expression simplifications (x+0, x*1, etc.)
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure ANFOpt : sig

    val optimize : ANF.function -> ANF.function

end = struct

    fun bug m = ErrorMsg.impossible ("ANFOpt: " ^ m)

    val simple_size_limit = 3

    structure O = Oper
    structure A = ANF
    structure M = LVar.Map
    structure S = LVar.Set

    structure SCC = GraphSCCFn (LVar)

    type lvar = LVar.lvar

    datatype bindinfo =
	VALUE of A.value
            (* invariant: value is "final" *)
      | RECORD of lvar * bindinfo list
            (* invariant: lvar is directly bound to this RECORD;
	     * bindinfos are "final" *)
      | INLFUN of lvar * A.lvar list * A.exp * S.set
            (* invariant: lvar is directly bound to this INLFUN;
	     * function already optimized; set is set of free vars *)

    infix ++ val op ++ = S.union
    infix -- val op -- = S.difference
    infix ** val op ** = S.intersection
    infix :< fun x :< s = S.member (s, x)
    infix :<< fun xl :<< s = List.exists (fn x => x :< s) xl

    fun var v = S.singleton v
    fun varlist l = S.addList (S.empty, l)

    fun isSimple e =
	let fun exp (d, e) =
		d > 0 andalso
		(case e of
		     A.VALUES _ => true
		   | A.BIND (_, _, e) => exp (d-1, e)
		   | A.CALL (_, _, _, e) => exp (d-1, e)
		   | A.FIX _ => false
		   | A.ARITH (_, _, _, _, e) => exp (d-1, e)
		   | A.RECORD (_, _, _, _, e) => exp (d-1, e)
		   | A.SELECT (_, _, _, _, e) => exp (d-1, e)
		   | A.UPDATE (_, _, _, e) => exp (d-1, e)
		   | A.CMP (_, _, _, e1, e2) => exp (d-1, e1) andalso exp (d-1, e2)
		   | A.JUMP _ => true
		   | A.GETSP (_, e) => exp (d-1, e)
		   | A.SETSP (x, e) => false
		   | A.MAYJUMP _ => false)
	in exp (simple_size_limit, e)
	end

    (* take tag into account *)
    fun recidx i = LiteralData.toInt (i div MachSpec.wordSize)

    fun optimize f =
	let val clonevar = LVar.clone

	    fun bind (v, bi, m) = M.insert (m, v, bi)
	    fun bindval (v, x, m) = bind (v, VALUE x, m)
	    fun bindrec (v, bil, m) = bind (v, RECORD (v, bil), m)
	    fun bindfun (f, vl, b, fvf, m) =
		bind (f, INLFUN (f, vl, b, fvf), m)

	    fun bindinfo m (x as A.VAR v) =
		  (case M.find (m, v) of
		       SOME bi => bi
		     | NONE => VALUE x)
	      | bindinfo _ (x as (A.INT _)) = VALUE x
        | bindinfo _ (x as (A.LABEL _)) = VALUE x

	    fun bi2val (VALUE x) = x
	      | bi2val (RECORD (v, _)) = A.VAR v
	      | bi2val (INLFUN (v, _, _, _)) = A.VAR v

	    fun value m x = bi2val (bindinfo m x)

	    fun fvx (A.VAR v) = S.singleton v
	      | fvx (A.INT _) = S.empty
        | fvx (A.LABEL _) = S.empty

	    fun fvxl [] = S.empty
	      | fvxl (x :: xs) = fvx x ++ fvxl xs

	    fun fvsl [] = S.empty
	      | fvsl (A.SGT x :: sl) = fvx x ++ fvsl sl
	      | fvsl (A.SEQ { base, start, stop } :: sl) =
		  fvx base ++ fvx start ++ fvx stop ++ fvsl sl

	    fun clone (vl, e, rest) =
		let fun withfresh (v, m) f =
			let val v' = clonevar v
			    val m' = M.insert (m, v, v')
			in f (v', m')
			end
		    fun ins (x, y, m) = M.insert (m, x, y)
		    fun withfresh' (vl, m) f =
			let val vl' = map clonevar vl
			in f (vl', ListPair.foldl ins m (vl, vl'))
			end
		    fun varval m v =
			case M.find (m, v) of
			    SOME v' => v'
			  | NONE => v
		    fun value m (A.VAR v) = A.VAR (varval m v)
		      | value _ x = x
		    fun slice m (A.SGT v) = A.SGT (value m v)
		      | slice m (A.SEQ { base, start, stop }) =
			  A.SEQ { base = value m base,
				  start = value m start,
				  stop = value m stop }
		    fun exp0 (m, e, rest) =
			let fun exp m (A.VALUES xl) =
				  let val xl' = map (value m) xl
				  in case rest of
					 NONE => A.VALUES xl'
				       | SOME (vl0, b0) =>
					   ListPair.foldr A.BIND b0 (vl0, xl')
				  end
			      | exp m (A.BIND (v, x, e)) =
				  withfresh (v, m) (fn (v', m') =>
					A.BIND (v', value m x, exp m' e))
			      | exp m (A.CALL (ta, vl, (x, xl), e)) =
				  withfresh' (vl, m) (fn (vl', m') =>
				        A.CALL (ta, vl', (value m x,
							  map (value m) xl),
						exp m' e))
			      | exp m (A.FIX (fl, e)) =
				  let val fs = map (#1 o #f) fl
				      val fs' = map clonevar fs
				      val m' = ListPair.foldl ins m (fs, fs')
				      fun one ({ f = (f, vl, b), inl, hdlr },
					       f') =
					  let val (vl', b') =
						  funbody (m', NONE, vl, b)
					  in { f = (f', vl', b'), inl = inl,
					       hdlr = hdlr }
					  end
				      val fl' = ListPair.map one (fl, fs')
				  in A.FIX (fl', exp m' e)
				  end
			      | exp m (A.ARITH (aop, x1, x2, v, e)) =
				  withfresh (v, m) (fn (v', m') =>
					A.ARITH (aop, value m x1, value m x2,
						 v', exp m' e))
			      | exp m (A.RECORD (mu, x, sl, v, e)) =
				  withfresh (v, m) (fn (v', m') =>
					A.RECORD (mu, value m x,
						  map (slice m) sl,
						  v', exp m' e))
			      | exp m (A.SELECT (x1, x2, mut, v, e)) =
				  withfresh (v, m) (fn (v', m') =>
					A.SELECT (value m x1, value m x2,
						  mut, v', exp m' e))
			      | exp m (A.UPDATE (x1, x2, x3, e)) =
				  A.UPDATE (value m x1, value m x2, value m x3,
					    exp m e)
			      | exp m (A.CMP (cop, x, x', e, e')) =
				  (case rest of
				       NONE =>
				         A.CMP (cop, value m x, value m x',
						exp m e, exp m e')
				     | SOME (vl0, b0) =>
				         let val f = LVar.new "cmp_join"
					     fun branch e =
						 let val vl = map LVar.clone vl0
						     val xl = map A.VAR vl
						     val b =
							 A.JUMP (Purity.Impure,
								 (A.VAR f, xl))
						 in exp0 (m, e, SOME (vl, b))
						 end
					 in A.FIX ([{ f = (f, vl0, b0),
						      inl = false,
						      hdlr = false }],
						   A.CMP (cop, value m x,
							       value m x',
							  branch e,
							  branch e'))
					 end)
			      | exp m (A.JUMP (ta, (x, xl))) =
				  let val x' = value m x
				      val xl' = map (value m) xl
				  in case rest of
					 NONE =>
					   A.JUMP (ta, (x', xl'))
				       | SOME (vl0, b0) =>
					   A.CALL (ta, vl0, (x', xl'), b0)
				  end
			      | exp m (A.GETSP (v, e)) =
				  withfresh (v, m) (fn (v', m') =>
				    A.GETSP (v', exp m' e))
			      | exp m (A.SETSP (x, e)) =
				  A.SETSP (value m x, exp m e)
			      | exp m (A.MAYJUMP (v, e)) =
				  A.MAYJUMP (varval m v, exp m e)
			in exp m e
			end
		    and funbody (m, rest, vl, b) =
			withfresh' (vl, m) (fn (vl', m') =>
			  (vl', exp0 (m', b, rest)))
		in funbody (M.empty, rest, vl, e)
		end

	    fun exp m (A.VALUES xl) =
		  let val xl' = map (value m) xl
		  in (A.VALUES xl', fvxl xl')
		  end
	      | exp m (A.BIND (v, x, e)) =
		  exp (bind (v, bindinfo m x, m)) e
	      | exp m (A.CALL (ta, vl, (x, xl), e)) =
		  let val xl' = map (value m) xl
		      val (e', fve) = exp m e
		  in if ta = Purity.Pure andalso not (vl :<< fve) then
			 (e', fve)
		     else case bindinfo m x of
			      INLFUN (f, vl0, b, fvf) =>
			        let val (vl', b') =
					clone (vl0, b, SOME (vl, e'))
				in (ListPair.foldl A.BIND b' (vl', xl'),
				    ((fvf ++ fve) -- varlist vl) ++ fvxl xl')
				end
			    | VALUE x' => (A.CALL (ta, vl, (x', xl'), e'),
					   (fve -- varlist vl)
					       ++ fvxl (x' :: xl'))
			    | RECORD _ => bug "unexpected RECORD in CALL"
		  end
	      | exp m (A.FIX (fl, e)) =
		  let val (fli, fln) = List.partition #inl fl
		      val fsi = varlist (map (#1 o #f) fli)
		      val fsn = varlist (map (#1 o #f) fln)
		      val fs = S.union (fsi, fsn)
		      val fsl = S.listItems fs
		      fun doi (fu, (l, m')) =
			  let val (fu' as { f = (f, vl, b), ... }, fvf) =
				  function m fu
			      val m'' = bindfun (f, vl, b, fvf, m)
			  in ((fu', fvf) :: l, m'')
			  end
		      val (l_f_fvf_i, m_i) = foldl doi ([], m) fli
		      val l_f_fvf_n = map (function m_i) fln
		      val funm =
			  foldl (fn (info as ({ f = (f, vl, b), inl, hdlr },
					      fvf), m) =>
				    M.insert (m, f, (S.listItems (fvf ** fs),
						     info)))
				M.empty
				(l_f_fvf_i @ l_f_fvf_n)
		      fun follow f =
			  case M.find (funm, f) of
			      NONE => fsl
			    | SOME (l, _) => l
		      val cl = SCC.topOrder { root = LVar.dummy,
					      follow = follow }
		      fun getf f =
			  case M.find (funm, f) of
			      NONE => bug "FIX: no function"
			    | SOME (_, info) => info
		      fun build ([], m) = exp m e
			| build (c :: cs, m) =
			    case c of
				SCC.SIMPLE f =>
				  let val ({ f = (f, vl, b), inl, hdlr }, fvf) =
					  getf f
				      val m' =
					  if not inl andalso isSimple b then
					      bindfun (f, vl, b, fvf, m)
					  else m
				      val (e', fve) = build (cs, m')
				  in if f :< fve then
					 (A.FIX ([{ f = (f, vl, b),
						    inl = inl, hdlr = hdlr }],
						 e'),
					  (fve ++ fvf) -- var f)
				     else (e', fve)
				  end
			      | SCC.RECURSIVE ff =>
				  let val l_f_fvf = map getf ff
				      val fl' = map #1 l_f_fvf
				      val fs = varlist (map (#1 o #f) fl')
				      val fvfl =
					  foldl op ++ S.empty (map #2 l_f_fvf)
				      val (e', fve) = build (cs, m)
				  in if S.isEmpty (fs ** fve) then (e', fve)
				     else (A.FIX (fl', e'), (fve ++ fvfl) -- fs)
				  end
		  in case cl of
			 _ :: cl => build (rev cl, m_i)
		       | [] => bug "no root cluster"
		  end
	      | exp m (A.ARITH (aop, x, y, v, e)) =
		  let fun default (x', y') =
			  let val (e', fve) = exp m e
			  in if v :< fve then
				 (A.ARITH (aop, x', y', v, e'),
				  (fve -- var v) ++ fvxl [x', y'])
			     else (e', fve)
			  end
		  in case (value m x, value m y) of
			 (x' as A.INT i, y' as A.INT j) =>
		           (let val k = Oper.doarith (aop, i, j)
			    in exp (bindval (v, A.INT k, m)) e
			    end handle _ => default (x', y'))
		       | (A.INT i, x') =>
			   (case (i, aop) of
				      (0, O.PLUS) =>
				      exp (bindval (v, x', m)) e
            | (1, O.TIMES) =>
				      exp (bindval (v, x', m)) e
			      | (0, O.TIMES) =>
				      exp (bindval (v, A.INT 0, m)) e
			      | _ => default (A.INT i, x'))
		       | (x', A.INT i) =>
			   (case (i, aop) of
              (0, aop) =>
              if aop = O.PLUS orelse aop = O.MINUS
              then exp (bindval (v, x', m)) e
              else if aop = O.TIMES orelse aop = O.DIV
              then exp (bindval (v, A.INT 0, m)) e
              else default (x', A.INT i)
            | (1, O.TIMES) =>
				      exp (bindval (v, x', m)) e
            | (1, O.DIV) =>
				      exp (bindval (v, x', m)) e
			      | _ => default (x', A.INT i))
		       | (x', y') => default (x', y')
		  end
	      | exp m (A.RECORD (mu, x, sl, v, e)) =
		let fun allSGT [] = SOME []
		      | allSGT (A.SGT x :: sl) =
			  Option.map (fn xl => x :: xl) (allSGT sl)
		      | allSGT (A.SEQ _ :: _) = NONE
		in case (x, allSGT sl) of
		       (A.INT 0, _) => exp (bindval (v, A.INT 0, m)) e
		     | (_, NONE) =>
		         (* FIXME: this should be handled more cleverly *)
		         let val x' = value m x
			     fun slice (A.SGT x) = A.SGT (value m x)
			       | slice (A.SEQ { base, start, stop }) =
				   A.SEQ { base = value m base,
					   start = value m start,
					   stop = value m stop }
			     val sl' = map slice sl
			     val (e', fve) = exp m e
			 in (A.RECORD (mu, x', sl', v, e'),
			     (fve -- var v) ++ fvx x' ++ fvsl sl')
			 end
		     | (_, SOME xl) =>
		         let val x' = value m x
			     val bil = map (bindinfo m) xl
			     val (e', fve) = exp (bindrec (v, bil, m)) e
			 in if v :< fve then
				let val xl' = map bi2val bil
				in (A.RECORD (mu, x', map A.SGT xl', v, e'),
				    (fve -- var v) ++ fvxl (x' :: xl'))
				end
			    else (e', fve)
			 end
		end
	      | exp m (A.SELECT (x, y, Purity.Impure, v, e)) =
		  let val (x', y') = (value m x, value m y)
		      val (e', fve) = exp m e
		  in (A.SELECT (x', y', Purity.Impure, v, e'),
		      (fve -- var v) ++ fvxl [x', y'])
		  end
	      | exp m (A.SELECT (x, y, Purity.Pure, v, e)) =
		  (case (bindinfo m x, value m y) of
		       (RECORD (_, bil), A.INT i) =>
		          let val bi = List.nth (bil, recidx i)
			  in exp (bind (v, bi, m)) e
			  end
		     | (bi, y') =>
		         let val x' = bi2val bi
			     val (e', fve) = exp m e
			 in if v :< fve then
				(A.SELECT (x', y', Purity.Pure, v, e'),
				 (fve -- var v) ++ fvxl [x', y'])
			    else (e', fve)
			 end)
	      | exp m (A.UPDATE (x, y, z, e)) =
		  let val (x', y', z') = (value m x, value m y, value m z)
		      val (e', fve) = exp m e
		  in (A.UPDATE (x', y', z', e'), fve ++ fvxl [x', y', z'])
		  end
	      | exp m (A.CMP (cop, x, y, et, ef)) =
		  (case (value m x, value m y) of
		       (x' as A.INT i, y' as A.INT j) =>
		         if Oper.docmp (cop, i, j) then exp m et else exp m ef
		     | (x', y') =>
		         let val (et', etfv) = exp m et
			     val (ef', effv) = exp m ef
			 in (A.CMP (cop, x', y', et', ef'),
			     etfv ++ effv ++ fvxl [x', y'])
			 end)
	      | exp m (A.JUMP (ta, (x, xl))) =
		  let val xl' = map (value m) xl
		  in case bindinfo m x of
			 INLFUN (f, vl, b, fvf) =>
			   let val (vl', b') = clone (vl, b, NONE)
			   in (ListPair.foldl A.BIND b' (vl', xl'),
			       fvf ++ fvxl xl')
			   end
		       | VALUE x' => (A.JUMP (ta, (x', xl')), fvxl (x' :: xl'))
		       | RECORD _ => bug "unexpected RECORD in JUMP"
		  end
	      | exp m (A.GETSP (v, e)) =
		  let val (e', fve) = exp m e
		  in if v :< fve then (A.GETSP (v, e'), fve -- var v)
		     else (e', fve)
		  end
	      | exp m (A.SETSP (x, e)) =
		  let val x' = value m x
		      val (e', fve) = exp m e
		  in (A.SETSP (x', e'), fve ++ fvx x')
		  end
	      | exp m (A.MAYJUMP (v, e)) =
		  (case M.find (m, v) of
		       SOME _ => bug "unexpected bindinfo for exn handler"
		     | NONE => let val (e', fve) = exp m e
			       in (A.MAYJUMP (v, e'), fve ++ var v)
			       end)

	    and function m { f = (f, vl, b), inl, hdlr } =
		let val (b', fvb) = exp m b
		in ({ f = (f, vl, b'), inl = inl, hdlr = hdlr },
		    fvb -- varlist vl)
		end
	in #1 (function M.empty f)
	end
end
