(* closure.sml
 *
 *   Closure conversion for MLPolyR.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Closure : sig

    val convert: ANF.function -> Closed.program

end = struct

    fun bug m = ErrorMsg.impossible ("Closure: " ^ m)

    structure A = ANF
    structure C = Closed
    structure M = LVar.Map
    structure S = LVar.Set

    type lvar = LVar.lvar
    type label = Label.label

    val newlabel = Label.new

    datatype denotation =
	FUN of { freevars: lvar list,
	         jump: label,	(* known entrypoint for JUMP *)
		 call: label,	(* known entrypoint for CALL *)
		 ecall: label,	(* escaping entrypoint (assume CALL) *)
		 escape: lvar option } (* pre-packaged escaping fun *)

    fun recidx i = C.INT (i * MachSpec.wordSize)
    val zeroidx = recidx 0
    val oneidx = recidx 1

    fun convert f =
	let val clonevar = LVar.clone

	    fun bind (v, d, env) = M.insert (env, v, d)

	    fun h0 e = e

	    infix ++  fun s ++ s' = S.union (s, s')
	    infix --  fun s -- v = S.difference (s, S.singleton v)
	    fun l2s l = S.addList (S.empty, l)
	    fun xl2s l = l2s (List.mapPartial (fn (C.VAR v) => SOME v
						| _ => NONE) l)
	    fun disjoint (s1, s2) = S.isEmpty (S.intersection (s1, s2))

	    fun funlfv (fl, env) =
		let fun value (A.VAR v) =
			  (case M.find (env, v) of
			       SOME (FUN { freevars, escape = NONE, ... }) =>
			         l2s freevars
			     | SOME (FUN { escape = SOME f', ... }) =>
			         S.singleton f'
			     | NONE => S.singleton v)
		      | value (A.INT _ | A.LABEL _) = S.empty
		    fun slice (A.SGT x) = value x
		      | slice (A.SEQ { base, start, stop }) =
			  value base ++ value start ++ value stop
		    fun list f [] = S.empty
		      | list f (x :: xs) = f x ++ list f xs
		    fun exp (A.VALUES xl) = list value xl
		      | exp (A.BIND (v, x, e)) = (exp e -- v) ++ value x
		      | exp (A.CALL (_, vl, a, e)) =
			  S.difference (exp e, l2s vl) ++ call a
		      | exp (A.FIX (fl, e)) =
			  S.difference (list function fl ++ exp e,
					l2s (map (#1 o #f) fl))
		      | exp (A.ARITH (_, x, y, v, e)) =
			  (exp e -- v) ++ value x ++ value y
		      | exp (A.RECORD (_, x, sl, v, e)) =
			  (exp e -- v) ++ value x ++ list slice sl
		      | exp (A.SELECT (x, y, _, v, e)) =
			  (exp e -- v) ++ value x ++ value y
		      | exp (A.UPDATE (x, y, z, e)) =
			  exp e ++ value x ++ value y ++ value z
		      | exp (A.CMP (_, x, y, et, ef)) =
			  exp et ++ exp ef ++ value x ++ value y
		      | exp (A.JUMP (_, a)) =
			  call a
		      | exp (A.GETSP (v, e)) =
			  exp e -- v
		      | exp (A.SETSP (x, e)) =
			  value x ++ exp e
		      | exp (A.MAYJUMP (v, e)) =
			  S.singleton v ++ exp e
		    and call (x as C.VAR f, xl) =
			  (case M.find (env, f) of
			       SOME (FUN { freevars, ... }) =>
			         l2s freevars ++ list value xl
			     | NONE => list value xl ++ S.singleton f)
		      | call (x, xl) = list value (x :: xl)
		    and function { f = (f, vl, b), inl, hdlr } =
			S.difference (exp b, l2s vl)
		in S.difference (list function fl, l2s (map (#1 o #f) fl))
		end

	    fun alpha (e, orig) =
		let val m = ref M.empty
		    fun rename v =
			let val v' = clonevar v
			in m := M.insert (!m, v, v'); v'
			end
		    val new = map rename orig
		    fun value (C.VAR v) =
			  (case M.find (!m, v) of
			       SOME v' => C.VAR v'
			     | NONE => C.VAR v)	(* should not happen *)
		      | value (x as (C.INT _ | C.LABEL _)) = x
		    fun slice (C.SGT x) = C.SGT (value x)
		      | slice (C.SEQ { base, start, stop }) =
			  C.SEQ { base = value base,
				  start = value start,
				  stop = value stop }
		    val valuelist = map value
		    val slicelist = map slice
		    fun jtarget (x, xl) = (value x, valuelist xl)
		    fun btarget (l, xl) = (l, valuelist xl)
		    fun exp (C.VALUES xl) = C.VALUES (valuelist xl)
		      | exp (C.BIND (v, x, e)) =
			  C.BIND (rename v, value x, exp e)
		      | exp (C.CALL (ta, vl, t, e)) =
			  C.CALL (ta, map rename vl, jtarget t, exp e)
		      | exp (C.ARITH (aop, x, y, v, e)) =
			  C.ARITH (aop, value x, value y, rename v, exp e)
		      | exp (C.RECORD (m, x, sl, v, e)) =
			  C.RECORD (m, value x, slicelist sl, rename v, exp e)
		      | exp (C.SELECT (x, y, m, v, e)) =
			  C.SELECT (value x, value y, m, rename v, exp e)
		      | exp (C.UPDATE (x, y, z, e)) =
			  C.UPDATE (value x, value y, value z, exp e)
		      | exp (C.CMP (cop, x, y, tt, ft)) =
			  C.CMP (cop, value x, value y, btarget tt, btarget ft)
		      | exp (C.JUMP t) =
			  C.JUMP (jtarget t)
		      | exp (C.GETSP (v, e)) =
			  C.GETSP (rename v, exp e)
		      | exp (C.SETSP (x, e)) =
			  C.SETSP (value x, exp e)
		      | exp (C.MAYJUMP (l, e)) =
			  C.MAYJUMP (l, exp e)
		in (exp e, new)
		end

	    fun precord (xl, v, e) =
		C.RECORD (Purity.Pure,
			  C.INT (LiteralData.fromInt (length xl) *
				 MachSpec.wordSize),
			  map C.SGT xl,
			  v, e)

	    fun value (A.VAR v, env) =
		  (case M.find (env, v) of
		       SOME (FUN { freevars, escape = NONE, ecall, ... }) =>
		         let val cv = clonevar v val fv = clonevar v
			     fun record ([], v, e) = C.BIND (v, C.INT 0, e)
			       | record ([x], v, e) = C.BIND (v, x, e)
			       | record (xl, v, e) = precord (xl, v, e)
			     fun h e =
				 record (map C.VAR freevars, cv,
					 precord ([C.LABEL ecall, C.VAR cv],
						  fv, e))
			 in (C.VAR fv, h, l2s freevars)
			 end
		     | SOME (FUN { escape = SOME funv, ... }) =>
		         (C.VAR funv, h0, S.singleton funv)
		     | NONE => (C.VAR v, h0, S.singleton v))
	      | value (A.INT i, _) = (C.INT i, h0, S.empty)
	      | value (A.LABEL l, _) = (C.LABEL l, h0, S.empty)

	    fun valuelist ([], _) = ([], h0, S.empty)
	      | valuelist (x :: xs, env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (xs', hxs, fvxs) = valuelist (xs, env)
		  in (x' :: xs', hx o hxs, fvx ++ fvxs)
		  end

	    fun slice (A.SGT x, env) =
		  let val (x', h, fv) = value (x, env)
		  in (C.SGT x', h, fv)
		  end
	      | slice (A.SEQ { base, start, stop }, env) =
		  let val (base', hb, fvb) = value (base, env)
		      val (start', hs, fvs) = value (start, env)
		      val (stop', hl, fvl) = value (stop, env)
		  in (C.SEQ { base = base, start = start', stop = stop' },
		      hb o hs o hl, fvb ++ fvs ++ fvl)
		  end

	    fun slicelist ([], _) = ([], h0, S.empty)
	      | slicelist (s :: sl, env) =
		  let val (s', hs, fvs) = slice (s, env)
		      val (sl', hsl, fvsl) = slicelist (sl, env)
		  in (s' :: sl', hs o hsl, fvs ++ fvsl)
		  end

	    fun exp (A.VALUES xl, env) =
		  let val (xl', h, fvx) = valuelist (xl, env)
		  in (h (C.VALUES xl'), fvx, [], [])
		  end
	      | exp (A.BIND (v, x, e), env) =
		  let val (x', h, fvx) = value (x, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (h (C.BIND (v, x', e')), fvx ++ (fve -- v), je, ce)
		  end
	      | exp (A.CALL (ta, vl, (A.VAR f, xl), e), env) =
		  let val (xl', hxl, fvxl) = valuelist (xl, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in case M.find (env, f) of
			 SOME (FUN { call, freevars, ... }) =>
			   (hxl (C.CALL (ta, vl, (C.LABEL call,
					     map C.VAR freevars @ xl'),
					 e')),
			    S.addList (fvxl ++ S.difference (fve, l2s vl),
				       freevars),
			    je, ce)
		       | NONE =>
			   let val fp = clonevar f
			       val cl = clonevar f
			   in (hxl (C.SELECT (C.VAR f, zeroidx, Purity.Pure, fp,
				      C.SELECT (C.VAR f, oneidx, Purity.Pure, cl,
					C.CALL (ta, vl,
						(C.VAR fp, C.VAR cl :: xl'),
						e')))),
			       S.add (fvxl ++ S.difference (fve, l2s vl), f),
			       je, ce)
			   end
		  end
	      | exp (A.CALL (ta, vl, (A.LABEL l, xl), e), env) =
		  let val (xl', hxl, fvxl) = valuelist (xl, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hxl (C.CALL (ta, vl, (C.LABEL l, xl'), e')),
		      fvxl ++ S.difference (fve, l2s vl),
		      je, ce)
		  end
	      | exp (A.CALL (_, _, (A.INT _, _), _), _) =
		  bug "unexpected CALL of INT"
	      | exp (A.FIX (fl, e), env) =
		  let val fs = l2s (map (#1 o #f) fl)
		      val freevars = S.listItems (funlfv (fl, env))
		      fun flab f = newlabel (SOME f)
		      val entrypoints =
			  map (fn { f = (f,_,_), ... } =>
				  (flab f, flab f, flab f)) fl
		      val env' =
			  ListPair.foldl
			      (fn ({ f = (f,_,_), ... },(j,c,ec),env) =>
				  M.insert (env, f,
					    FUN { freevars = freevars,
						  jump = j,
						  call = c,
						  ecall = ec,
						  escape = NONE }))
			      env
			      (fl, entrypoints)
		      val (jfl, cfl) =
			  ListPair.foldr
			      (fn ({ f = (f, vl, b), hdlr, ... }, (j, c, ec),
				   (jfl0, cfl0)) =>
				  let val (b', _, jb, cb) = exp (b, env')
				      val (b'', fpb) = alpha (b', freevars @ vl)
				      val fpb_c = map clonevar fpb
				      val b_c =
					  C.JUMP (C.LABEL j, map C.VAR fpb_c)
				      val clv_ec = clonevar f
				      val vl_ec = map clonevar vl
				      fun mk_b_ec ([], _, svl) =
					  C.JUMP (C.LABEL j,
						  map C.VAR (rev svl @ vl_ec))
					| mk_b_ec (v :: r, i, svl) =
					    let val sv = clonevar v
					    in C.SELECT (C.VAR clv_ec,
							 recidx i,
							 Purity.Pure,
							 sv,
							 mk_b_ec (r, i+1,
								  sv :: svl))
					    end
				      fun mk_b_ec' [_] =
					  C.JUMP (C.LABEL j,
						  map C.VAR (clv_ec :: vl_ec))
					| mk_b_ec' vl = mk_b_ec (vl, 0, [])
				      val b_ec = mk_b_ec' freevars
				  in ((j, fpb, b'') ::
				        jb @ jfl0,
				      (c, fpb_c, b_c, hdlr) ::
				        (ec, clv_ec :: vl_ec, b_ec, hdlr) ::
				          cb @ cfl0)
				  end)
			      ([], [])
			      (fl, entrypoints)
		      val env'' =
			  ListPair.foldl
			      (fn ({ f = (f,_,_), ... },(j,c,ec),env) =>
				  M.insert (env, f,
					    FUN { freevars = freevars,
						  jump = j,
						  call = c,
						  ecall = ec,
						  escape = SOME f }))
			      env
			      (fl, entrypoints)
		      val (e', efv, je, ce) = exp (e, env'')
		      val escfuns = S.intersection (fs, efv)
		      val escfunl = S.listItems escfuns
		      fun bindesc [] = (e', efv)
			| bindesc (f :: fs) =
			    let val (b', bfv) = bindesc fs
			    in if S.member (bfv, f) then
				   let val (x, h, ffv) = value (A.VAR f, env')
				   in (h (C.BIND (f, x, b')),
				       (bfv -- f) ++ ffv)
				   end
			       else (b', bfv)
			    end
		      val (e'', efv') = bindesc escfunl

		  in (e'', efv', jfl @ je, cfl @ ce)
		  end
	      | exp (A.ARITH (aop, x, y, v, e), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (y', hy, fvy) = value (y, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hx (hy (C.ARITH (aop, x', y', v, e'))),
		      fvx ++ fvy ++ (fve -- v), je, ce)
		  end
	      | exp (A.RECORD (m, x, sl, v, e), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (sl', hsl, fvsl) = slicelist (sl, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hx (hsl (C.RECORD (m, x', sl', v, e'))),
		      fvx ++ fvsl ++ (fve -- v), je, ce)
		  end
	      | exp (A.SELECT (x, y, m, v, e), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (y', hy, fvy) = value (y, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hx (hy (C.SELECT (x', y', m, v, e'))),
		      fvx ++ fvy ++ (fve -- v), je, ce)
		  end
	      | exp (A.UPDATE (x, y, z, e), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (y', hy, fvy) = value (y, env)
		      val (z', hz, fvz) = value (z, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hx (hy (hz (C.UPDATE (x', y', z', e')))),
		      fvx ++ fvy ++ fvz ++ fve, je, ce)
		  end
	      | exp (A.CMP (cop, x, y, te, fe), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (y', hy, fvy) = value (y, env)
		      val (te', fvte, jte, cte) = exp (te, env)
		      val (fe', fvfe, jfe, cfe) = exp (fe, env)
		      val tlab = newlabel NONE
		      val flab = newlabel NONE
		      val fvlte = S.listItems fvte
		      val fvlfe = S.listItems fvfe
		      val (te'', fpte) = alpha (te', fvlte)
		      val (fe'', fpfe) = alpha (fe', fvlfe)
		  in (hx (hy (C.CMP (cop, x', y',
				     (tlab, map C.VAR fvlte),
				     (flab, map C.VAR fvlfe)))),
		      fvx ++ fvy ++ fvte ++ fvfe,
		      (tlab, fpte, te'') :: (flab, fpfe, fe'') :: jte @ jfe,
		      cte @ cfe)
		  end
	      | exp (A.JUMP (_, (A.VAR f, xl)), env) =
		  let val (xl', hxl, fvxl) = valuelist (xl, env)
		  in case M.find (env, f) of
			 SOME (FUN { jump, freevars, ... }) =>
			   (hxl (C.JUMP (C.LABEL jump,
					 map C.VAR freevars @ xl')),
			    S.addList (fvxl, freevars),
			    [], [])
		       | NONE =>
			   let val fp = clonevar f
			       val cl = clonevar f
			   in (hxl (C.SELECT (C.VAR f, zeroidx, Purity.Pure, fp,
				      C.SELECT (C.VAR f, oneidx, Purity.Pure, cl,
					C.JUMP (C.VAR fp, C.VAR cl :: xl')))),
			       S.add (fvxl, f),
			       [], [])
			   end
		  end
	      | exp (A.JUMP (_, (A.LABEL l, xl)), env) =
		  let val (xl', hxl, fvxl) = valuelist (xl, env)
		  in (hxl (C.JUMP (C.LABEL l, xl')), fvxl, [], [])
		  end
	      | exp (A.JUMP (_, (A.INT _, _)), _) =
		  bug "unexpected JUMP to INT"
	      | exp (A.GETSP (v, e), env) =
		  let val (e', fve, je, ce) = exp (e, env)
		  in (C.GETSP (v, e'), fve -- v, je, ce)
		  end
	      | exp (A.SETSP (x, e), env) =
		  let val (x', hx, fvx) = value (x, env)
		      val (e', fve, je, ce) = exp (e, env)
		  in (hx (C.SETSP (x', e')), fvx ++ fve, je, ce)
		  end
	      | exp (A.MAYJUMP (v, e), env) =
		  (case M.find (env, v) of
		       SOME (FUN { ecall, ... }) =>
		         let val (e', fve, je, ce) = exp (e, env)
			 in (C.MAYJUMP (ecall, e'), fve, je, ce)
			 end
		     | NONE => bug "handler not bound")

	    val { f = (mainv, mainformals, mainbody), inl = _, hdlr = _ } = f
	    val (mainbody', fvmainbody, je, ce) = exp (mainbody, M.empty)
	    val fvmain = S.difference (fvmainbody, l2s mainformals)
	    val _ = if not (S.isEmpty fvmain) then
			raise bug (String.concatWith " "
				    ("unexpected free variables:" ::
				     map LVar.toString (S.listItems fvmain)))
		    else ()
	    val entrylab = Label.external "mlpr_main"
	in { calltargets = ce, jumptargets = je,
	     entrypoint = (entrylab, mainformals, mainbody', false) }
	end
end
