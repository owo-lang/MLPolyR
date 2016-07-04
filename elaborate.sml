(* elaborate.sml
 *
 *   This module implements the Hindley-Milner-style type-checker/inferencer
 *   and elaborator of the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Elaborate : sig

    exception Elaborate

    val elaborate : Source.inputSource * Types.typschema Env.env * bool ->
		    Ast.program ->
		    Absyn.program

end = struct

    fun bug m = ErrorMsg.impossible ("Elaborate: " ^ m)

    exception Elaborate

    structure S = Ast
    structure A = Absyn
    structure T = Types
    structure TU = TypesUtil
    structure U = Unify
    structure RL = RecordLabel
    structure LS = RL.Set
    structure SS = Symbol.Set

    fun t2ts t = #1 (TU.dontgeneralize t)
    fun bindTys (v, ts, e) = Env.bind (v, ts, e)
    fun bindTy (v, t, e) = bindTys (v, t2ts t, e)

    fun bindpt (NONE, _, e) = e
      | bindpt (SOME v, t, e) = bindTy (v, t, e)

    fun elaborate (src, baseenv, pdefs) (mainexp, mainregion) =
	let fun error1 r m =
		(ErrorMsg.error src r ErrorMsg.COMPLAIN (concat m)
				ErrorMsg.nullErrorBody;
		 raise Elaborate)

	    fun tyclasherr (r0, (r1, r2), m, t1, t2) =
		let val reg1 = ErrorMsg.matchErrorString src r1
		    val reg2 = ErrorMsg.matchErrorString src r2
		    val tos = TU.mkPrinter ()
		    fun tos' t = tos (t2ts t)
		    val (ts1, ts2) = (tos' t1, tos' t2)
		in ErrorMsg.error src r0 ErrorMsg.COMPLAIN
				  (concat ["type mismatch: ", m,
					   " [clash between ",
					   ts1, " from ", reg1,
					   " and ",
					   ts2, " from ", reg2,
					   "]"])
				  ErrorMsg.nullErrorBody;
		   raise Elaborate
		end

	    fun addferr (r0, (r1, r2), m, t) =
		let val reg1 = ErrorMsg.matchErrorString src r1
		    val reg2 = ErrorMsg.matchErrorString src r2
		    val tos = TU.mkPrinter ()
		    val ts = tos t
		in ErrorMsg.error src r0 ErrorMsg.COMPLAIN
				  (concat ["record extension error: ", m,
					   " [left-hand side type: ",
					   ts, " from ", reg1,
					" cannot be extended with fields from ",
					   reg2, "]"])
				  ErrorMsg.nullErrorBody;
		   raise Elaborate
		end
		

	    fun checkduplab (l, fl, r, what) =
		if List.exists (fn (l', _) => RL.same (l, l')) fl then
		    error1 r ["duplicate record label ",
			      RL.toString l,
			      " in ", what, "\n"]
		else ()

	    fun unify r0 (t1, t2) =
		U.unify (t1, t2)
		handle U.Unify (r12, msg) => tyclasherr (r0, r12, msg, t1, t2)

	    fun runify r0 (rt1, rt2) =
		U.runify (rt1, rt2)
		handle U.Unify (r12 as (r1, r2), msg) =>
		       (* hack: *)
		       tyclasherr (r0, r12, msg, T.SUMty (rt1, r1),
				                 T.SUMty (rt2, r2))

	    fun mksumty (rt, r) =
		T.VARty (TVar.tvar (T.INST (T.SUMty (rt, r))))

	    fun joinvs (vs, vs', r) =
		let val overlap = SS.intersection (vs, vs')
		in if not (SS.isEmpty overlap) then
		       error1 r ["duplicate pattern variable(s): ",
				 String.concatWith " "
				     (map Symbol.toString
					  (SS.listItems overlap))]
		   else SS.union (vs, vs')
		end

	    fun elpat (p, r, t, d, env, gen) =
		let val (ts, pri) = if gen then TU.generalize d t
				    else TU.dontgeneralize t
		    val (p', env', ss) = elpat' (p, r, ts, d, env, gen)
		in ((p', (t, pri)), env', ss)
		end

	    and elpat' (p, r, ts, d, env, gen) =
		case p of
		    S.WILDpat =>
		      (A.WILDpat, env, SS.empty)
		  | S.VARpat v =>
		      (A.VARpat v, bindTys (v, ts, env), SS.singleton v)
		  | S.MARKpat (p, r) =>
		      elpat' (p, r, ts, d, env, gen)
		  | S.ANDpat (p1, p2) =>
		      let val (pp1, env', vs1) =
			      elpat' (p1, r, ts, d, env, gen)
			  val (pp2, env'', vs2) =
			      elpat' (p2, r, ts, d, env', gen)
		      in (A.ANDpat (pp1, pp2), env'', joinvs (vs1, vs2, r))
		      end
		  | S.TUPLEpat pl =>
		      let val (t, pri) = TU.instantiate (d, r) ts
			  val ptl = map (fn p => (p, TU.freshty (d, r))) pl
			  fun pt2tr (_, t) = (t, r)
			  val _ = unify r (t, T.TUPLEty (map pt2tr ptl, r))
			  fun loop ([], _, rpfl, env, vs) =
			        (A.RECORDpat (Purity.Pure,
					      rev rpfl, NONE, pri), env, vs)
			    | loop ((p, t) :: ptl, i, rpfl, env, vs) =
			        let val l = RL.NUMlab i
				    val (pp, env', vs') =
					elpat (p, r, t, d, env, gen)
				in loop (ptl, i+1, (l, pp) :: rpfl,
					 env', joinvs (vs, vs', r))
				end
		      in loop (ptl, 1, [], env, SS.empty)
		      end
		  | S.RECORDpat (purity, fpl) =>
		      let val (t, pri) = TU.instantiate (d, r) ts
			  fun collect ([], rlptl, NONE) =
			        (rev rlptl, NONE, T.EMPTYrty r)
			    | collect ([], rlptl, SOME p) =
			        let val excl = RL.toMap (#1, #1 o #2) rlptl
				    val excl' =
					RL.Map.insert (excl, RL.LENlab, r)
				    val rt = TU.freshrty (d, excl', r)
				in (rev rlptl, SOME p, rt)
				end
			    | collect ((NONE, p) :: pl, rlptl, NONE) =
			        collect (pl, rlptl, SOME p)
			    | collect ((NONE, p) :: pl, rlptl, SOME _) =
			        error1 r ["duplicate ellipsis \"...\"\
					  \ in record pattern"]
			    | collect ((SOME (l, lr), p) :: pl,
				       rlptl, popt) =
			        (checkduplab (l, rlptl, lr, "record pattern");
			         collect (pl,
					  (l, (lr, p, TU.freshty (d, r)))
					  :: rlptl,
					  popt))
			  val (lptl, popt, rt) = collect (fpl, [], NONE)
			  fun addfield ((l, (lr, p, pt)), rt) =
			      T.FIELDrty ((l, (pt, lr)), rt)
			  val t' = T.RECORDty (purity,
					       foldr addfield rt lptl, r)
			  val _ = unify r (t, t')
			  fun loop ([], rpfl, env, vs) =
			        (case popt of
				     NONE =>
				       (A.RECORDpat (purity,
						     rev rpfl, NONE, pri),
					env, vs)
				   | SOME p =>
				       let val (pp, env', vs') =
					       elpat (p, r,
						      T.RECORDty (purity, rt, r),
						      d, env, gen)
				       in (A.RECORDpat (purity,
							rev rpfl, SOME pp, pri),
					   env', joinvs (vs, vs', r))
				       end)
			    | loop ((l, (lr, p, pt)) :: lptl,
				    rpfl, env, vs) =
			        let val (pp, env', vs') =
					elpat (p, r, pt, d, env, gen)
				in loop (lptl, (l, pp) :: rpfl,
					 env', joinvs (vs, vs', r))
				end
		      in loop (lptl, [], env, SS.empty)
		      end
		  | S.MATCHpat fpl =>
		      let val (t, pri) = TU.instantiate (d, r) ts
			  fun collect ([], rlptl, NONE) =
			        (rev rlptl, NONE, T.EMPTYrty r)
			    | collect ([], rlptl, SOME p) =
			        let val excl = RL.toMap (#1, #1 o #2) rlptl
				    val excl' =
					RL.Map.insert (excl, RL.LENlab, r)
				    val rt = TU.freshrty (d, excl', r)
				in (rev rlptl, SOME p, rt)
				end
			    | collect ((NONE, p) :: pl, rlptl, NONE) =
			        collect (pl, rlptl, SOME p)
			    | collect ((NONE, p) :: _, _, SOME _) =
			        error1 r ["duplicate ellipsis \"...\"\
					  \ in match pattern"]
			    | collect ((SOME (l, lr), p) :: pl,
				       rlptl, popt) =
			        (checkduplab (l, rlptl, lr, "match pattern");
				 collect (pl,
					  (l, (lr, p, TU.freshty (d, r)))
					  :: rlptl,
					  popt))
			  val (lptl, popt, rt) = collect (fpl, [], NONE)
			  fun addcase ((l, (lr, p, pt)), rt) =
			      T.FIELDrty ((l, (pt, lr)), rt)
			  val srt = foldr addcase rt lptl
			  val rant = TU.freshty (d, r)
			  val ert = TU.freshrty0 (d, r)
			  val t' = T.MATCHty (srt, rant, ert, r)
			  val _ = unify r (t, t')
			  fun loop ([], rpfl, env, vs) =
			        (case popt of
				     NONE =>
				       (A.RECORDpat (Purity.Pure,
						     rev rpfl, NONE, pri),
					env, vs)
				   | SOME p =>
				       let val rmt =
					       T.MATCHty (rt, rant, ert, r)
					   val (pp, env', vs') =
					       elpat (p, r, rmt, d, env, gen)
				       in (A.RECORDpat (Purity.Pure,
							rev rpfl, SOME pp, pri),
					   env', joinvs (vs, vs', r))
				       end)
			    | loop ((l, (lr, p, pt)) :: lptl,
				    rpfl, env, vs) =
			        let 
				    val (pp, env', vs') =
					elpat (p, r, T.FUNty (pt, rant, ert, r),
					       d, env, gen)
				in loop (lptl, (l, pp) :: rpfl,
					 env', joinvs (vs, vs', r))
				end
		      in loop (lptl, [], env, SS.empty)
		      end

	    val tos = TU.mkPrinter ()

	    fun show env (def, d) =
		let fun showvar v =
			case Env.find (env, v) of
			    SOME ts =>
			      print (concat ["val ", Symbol.toString v,
					     ": ", tos ts, "\n"])
			  | NONE => bug "showvar: variable not found"
		in case def of
		       A.VALdef (_, ss, _) => Symbol.Set.app showvar ss
		     | A.FUNdef (fl, _, rcl) =>
		         (app (showvar o #f) fl;
			  app (showvar o #c) rcl)
		end

	    fun elab (e, r, ty, ert, d, env, pdef) = let
		fun mfreshty d = TU.freshty (d, r)
		fun el (e, ty) = elab (e, r, ty, ert, d, env, false)
		val unify = unify r
		val runify = runify r
		fun elbop (bop as S.BOOLCONN _, e, e') =
		      (unify (ty, T.BOOLty r);
		       A.BINOPexp (bop, el (e, T.BOOLty r),
				        el (e', T.BOOLty r), ty))
		  | elbop (bop as S.CMP _, e, e') =
		      (unify (ty, T.BOOLty r);
		       A.BINOPexp (bop, el (e, T.INTty r),
				   el (e', T.INTty r),
				   ty))
		  | elbop (bop as S.ARITH _, e, e') =
		      (unify (ty, T.INTty r);
		       A.BINOPexp (bop, el (e, T.INTty r),
				   el (e', T.INTty r),
				   ty))
		  | elbop (bop as S.CONS, e, e') =
		      let val t = mfreshty d
		      in unify (ty, T.LISTty (t, r));
			 A.BINOPexp (bop, el (e, t), el (e', ty), ty)
		      end

		fun eluop (uop as S.UMINUS, e) =
		      (unify (ty, T.INTty r);
		       A.UOPexp (uop, el (e, T.INTty r), ty))
		  | eluop (uop as S.ISNULL, e) =
		      (unify (ty, T.BOOLty r);
		       A.UOPexp (uop, el (e, T.LISTty (mfreshty d, r)), ty))
		  | eluop (uop as S.NOT, e) =
		      (unify (ty, T.BOOLty r);
		       A.UOPexp (uop, el (e, T.BOOLty r), ty))

	    in case e of
		   S.LETexp (dl, b) =>
		     let fun loop ([], rdl, d, env) =
			       let val dl = rev rdl
			       in if pdef then app (show env) dl
				  else ();
				  A.LETexp (dl, elab (b, r, ty, ert, d,
						      env, false))
			       end
			   | loop (S.VALdef (p, e) :: dl, rdl, d, env) =
			       let val t = mfreshty d
				   (* NOTE: ert is right here,
				    * if generalizable, then ert
				    * will not have become part of
				    * t *)
				   val ee = elab (e, r, t, ert, d, env, false)
				   val gen = S.isSynVal e
				   val (pp, env', ss) =
				       elpat (p, r, t, d, env, gen)
				   val def = A.VALdef (pp, ss, ee)
			       in loop (dl, (def, d) :: rdl, d+1, env')
			       end
			   | loop (S.FUNdef (funl, rcl, r) :: dl, rdl, d, env) =
			       let val (funl', pri, rcl', env') =
				       elfuns (funl, rcl, ert, r, d, env)
				   val def = A.FUNdef (funl', pri, rcl')
			       in loop (dl, (def, d) :: rdl, d+1, env')
			       end
		     in loop (dl, [], d, env)
		     end
		 | S.IFexp (e1, e2, e3) =>
		     A.IFexp (el (e1, T.BOOLty r), el (e2, ty), el (e3, ty), ty)
		 | S.CASEexp (e, { nilcase = nce, conscase = (hp, tp, cce) }) =>
		     let val elt = mfreshty d
			 val lt = T.LISTty (elt, r)
			 val ee = elab (e, r, lt, ert, d, env, false)
			 val ncee = el (nce, ty)
			 val (tpp, env', vs1) =
			     elpat (tp, r, lt, d, env, false)
			 val (hpp, env'', vs2) =
			     elpat (hp, r, elt, d, env', false)
			 val _ = joinvs (vs1, vs2, r)
			 val ccee = elab (cce, r, ty, ert, d+1, env'', false)
		     in A.LCASEexp (ee, ncee, hpp, tpp, ccee, ty)
		     end
		 | S.WHEREexp (purity, e, fl) =>
		     let fun loop ([], rtfl, rdtl, refl) =
			       let val excl = RL.toMap (#1, #2 o #2) rtfl
				   val excl' =
				       RL.Map.insert (excl, RL.LENlab, r)
				   val rt = TU.freshrty (d, excl', r)
				   val et = T.RECORDty
						(purity,
						 foldr T.FIELDrty rt rdtl, r)
				   val ee = el (e, et)
			       in unify (ty, T.RECORDty
						 (purity,
						  foldr T.FIELDrty rt rtfl, r));
				  A.WHEREexp (purity,
					      ee, et, rev refl, ty)
			       end
			   | loop ((NONE, _) :: _, _, _, _) =
			       error1 r ["ellipsis \"...\" not permitted\
					 \ in where-expression"]
			   | loop ((SOME (l, lr), fe) :: fl,
				   rtfl, rdtl, refl) =
			       let val ft = mfreshty d
				   val dt = mfreshty d
				   val fee = el (fe, ft)
			       in checkduplab (l, refl, r,
					       "where expression");
				  loop (fl, (l, (ft, lr)) :: rtfl,
					    (l, (dt, lr)) :: rdtl,
					    (l, fee) :: refl)
			       end
		     in loop (fl, [], [], [])
		     end
		 | S.BINOPexp (bop, e1, e2) => elbop (bop, e1, e2)
		 | S.UOPexp (uop, e) => eluop (uop, e)
		 | S.APPexp (e1, e2) =>
		     let val dom = mfreshty d
		     in A.APPexp (el (e1, T.FUNty (dom, ty, ert, r)),
				  el (e2, dom), ty)
		     end
		 | S.ASSIGNexp (re, (l, lr), e) =>
		     let val et = mfreshty d
			 val ee = el (e, et)
			 val ret =
			     T.RECORDty
				 (Purity.Impure,
				  T.FIELDrty ((l, (et, lr)),
					      TU.freshrty1 (d, l, r)),
				  r)
			 val ree = el (re, ret)
		     in unify (ty, T.UNITty r);
			A.ASSIGNexp (ree, ret, l, ee)
		     end
		 | S.SELexp (purity, e, (l, lr)) =>
		     let val et =
			   T.RECORDty
			      (purity,
			       T.FIELDrty ((l, (ty, lr)),
					   TU.freshrty1 (d, l, r)),
			       r)
			 val ee = el (e, et)
		     in A.SELexp (purity, ee, et, l, ty)
		     end
		 | S.BOOLexp b => (unify (ty, T.BOOLty r); A.BOOLexp b)
		 | S.NUMBERexp i => (unify (ty, T.INTty r); A.NUMBERexp i)
		 | S.STRINGexp s => (unify (ty, T.STRINGty r); A.STRINGexp s)
		 | S.VARexp v =>
		     (case Env.find (env, v) of
			  SOME ts => let val (t, pril) =
					     TU.instantiate (d, r) ts
				     in unify (ty, t);
					A.VARexp (v, t, pril)
				     end
			| NONE => error1 r ["unbound variable: ",
					    Symbol.toString v])
		 | S.SEQexp [] => (unify (ty, T.UNITty r); A.UNITexp)
		 | S.SEQexp [e] => el (e, ty)
		 | S.SEQexp (h1 :: h2 :: t) =>
		     let fun u x = el (x, T.UNITty r)
			 fun lp (e, x, []) = A.SEQexp (e, el (x, ty))
			   | lp (e, x, y :: ys) = lp (A.SEQexp (e, u x), y, ys)
		     in lp (u h1, h2, t)
		     end
		  | S.LISTexp l =>
		      let val elty = mfreshty d
		      in unify (T.LISTty (elty, r), ty);
			 A.LISTexp (map (fn x => el (x, elty)) l, ty)
		      end
		  | S.RECORDexp (purity, fl) =>
		      let fun collect ([], rtfl, refl1, SOME (e, refl2)) =
			        let val excl = RL.toMap (#1, #2 o #2) rtfl
				    val excl' =
					RL.Map.insert (excl, RL.LENlab, r)
				    val rt = TU.freshrty (d, excl', r)
				    val et = T.RECORDty (purity, rt, r)
				    val ee = el (e, et)
				in unify (ty, T.RECORDty
						 (purity,
						  foldl T.FIELDrty rt rtfl, r));
				   A.RECORDexp (purity,
						rev refl1,
						SOME (ee, et, rev refl2), ty)
				end
			    | collect ([], rtfl, refl, NONE) =
			        (unify (ty, T.RECORDty
				    (purity,
				     foldl T.FIELDrty (T.EMPTYrty r) rtfl, r));
				 A.RECORDexp (purity, rev refl, NONE, ty))
			    | collect ((NONE, e) :: fl, rtfl, refl, NONE) =
			        collect (fl, rtfl, refl, SOME (e, []))
			    | collect ((NONE, _) :: _, _, _, SOME _) =
			        error1 r ["duplicate ellipsis \"...\" \
					  \in record expression"]
			    | collect ((SOME (l, lr), fe) :: fl,
				       rtfl, refl1, ropt) =
			        let val ft = mfreshty d
				    val fee = el (fe, ft)
				in checkduplab (l, rtfl, r,
						"record expression");
				   case ropt of
				       NONE =>
				         collect (fl, (l, (ft, lr)) :: rtfl,
					          (l, fee) :: refl1,
					          NONE)
				     | SOME (e, refl2) =>
				         collect (fl, (l, (ft, lr)) :: rtfl,
						  refl1,
						  SOME (e, (l, fee) :: refl2))
				end
		      in collect (fl, [], [], NONE)
		      end
		  | S.MATCHexp (rl, eopt) =>
		      let val rest = mfreshty d
			  val ert' = TU.freshrty0 (d, r)
			  fun loop ([], rtfl, refl) =
			        let fun mksrt (rt0, rtfl) =
					foldl T.FIELDrty rt0 rtfl
				in case eopt of
				       NONE =>
				         let val srt =
						 mksrt (T.EMPTYrty r, rtfl)
					 in unify (ty,
						   T.MATCHty (srt, rest,
							      ert', r));
					    A.RECORDexp (Purity.Pure,
							 rev refl, NONE, ty)
					 end
				     | SOME e =>
				         let val excl =
						 RL.toMap (#1, #2 o #2) rtfl
					     val excl' = RL.Map.insert
							   (excl, RL.LENlab, r)
					     val rt = TU.freshrty (d, excl', r)
					     val srt = mksrt (rt, rtfl)
					     val mt = T.MATCHty (srt, rest,
								 ert', r)
					     val _ = unify (ty, mt)
					     val srt' = mksrt (rt, [])
					     val mt' = T.MATCHty (srt', rest,
								  ert', r)
					     val e' = el (e, mt')
					 in A.RECORDexp (Purity.Pure,
							 rev refl,
							 SOME (e', mt', []),
							 ty)
					 end
				end
			    | loop (((l, lr), (p, e), r) :: rl, rtfl, refl) =
			        let val pt = mfreshty d
				    val (p', env', ss) =
					elpat (p, r, pt, d, env, false)
				    val e' = elab (e, r, rest, ert', d+1,
						   env', false)
				    val e'' =
					A.FNexp (p', e', T.FUNty (pt, rest,
								  ert', r))
				in loop (rl,
					 (l, (pt, lr)) :: rtfl,
					 (l, e'') :: refl)
				end
		      in loop (rl, [], [])
		      end
		  | S.TUPLEexp al =>
		      let val tl = map (fn _ => mfreshty d) al
			  val tlr = map (fn t => (t, r)) tl
			  val el = ListPair.map el (al, tl)
		      in unify (ty, T.TUPLEty (tlr, r));
			 A.TUPLEexp (el, ty)
		      end
		  | S.FNexp (p, b) =>
		      let val pt = mfreshty d
			  val rt = mfreshty d
			  val ert' = TU.freshrty0 (d, r)
			  val fty = T.FUNty (pt, rt, ert', r)
			  val _ = unify (fty, ty)
			  val (p', env', ss) = elpat (p, r, pt, d, env, false)
			  val b' = elab (b, r, rt, ert', d+1, env', false)
		      in A.FNexp (p', b', ty)
		      end
		  | S.CONexp ((l, lr), e) =>
		      let val et = mfreshty d
			  val sty = mksumty (T.FIELDrty
						 ((l, (et, lr)),
						  TU.freshrty1 (d, l, r)),
					     r)
			  val _ = unify (ty, sty)
			  val ee = el (e, et)
		      in A.CONexp ((l, ee), ty)
		      end
		  | S.SWIDENexp (e, (l, lr)) =>
		      let val ft = mfreshty d
			  val excl = RL.Map.insert (RL.Map.singleton (l, lr),
						    RL.LENlab, r)
			  val rt = TU.freshrty (d, excl, r)
			  val et = mksumty (rt, r)
			  val wt = mksumty (T.FIELDrty ((l, (ft, lr)), rt), r)
			  val _ = unify (wt, ty)
			  val ee = el (e, et)
		      in A.SWIDENexp (ee, et, l, wt)
		      end
		  | S.PSCASEexp (e, m) =>
		      let val exn_rt = ert
			  val ert = TU.freshrty0 (d, r)
			  val et = T.SUMty (ert, r)
			  val mt = T.MATCHty (ert, ty, exn_rt, r)
			  val ee = el (e, et)
			  val mm = el (m, mt)
		      in A.PSCASEexp (ee, mm, ty)
		      end
		  | S.TRYexp { scrutinee, success = (succ_p, succ_e),
			       handling, rehandling, catchall } =>
		      let val succ_t = mfreshty d
			  val hlabs = RL.toMap (#1 o #1, #2 o #1) handling
			  val rhlabs = RL.toMap (#1 o #1, #2 o #1) rehandling
			  val labs = RL.Map.unionWith #1 (hlabs, rhlabs)
			  val h_t_l = map (fn _ => mfreshty d) handling
			  val rh_t_l = map (fn _ => mfreshty d) rehandling
			  val rh_t0_l = map (fn _ => mfreshty d) rehandling
			  val rt = TU.freshrty (d, labs, r)
			  fun mkft (((l, lr), _, _), t, rt) =
			      T.FIELDrty ((l, (t, lr)), rt)
			  val ert' =
			      ListPair.foldl mkft
					     (ListPair.foldl mkft
							     rt
							     (handling, h_t_l))
					     (rehandling, rh_t_l)
			  val ca =
			      case catchall of
				  NONE =>
				    let val ert0 =
					    ListPair.foldl
						mkft
						rt
						(rehandling, rh_t0_l)
				    in runify (ert, ert0);
				       NONE
				    end
				| SOME (p, e) =>
				    let val t = mksumty (rt, r)
					val (pp, env', _) =
					    elpat (p, r, t, d, env, false)
					val ee =
					    elab (e, r, ty, ert, d+1,
						  env', false)
				    in SOME (pp, ee)
				    end
			  val scrutinee_e =
			      elab (scrutinee, r, succ_t, ert', d, env, false)
			  val (succ_pp, succ_env, _) =
			      elpat (succ_p, r, succ_t, d, env, false)
			  val succ_ee =
			      elab (succ_e, r, ty, ert, d+1, succ_env, false)
			  fun one_h (((l, _), (p, e), r), t) =
			      let val (pp, env', _) =
				      elpat (p, r, t, d, env, false)
				  val ee =
				      elab (e, r, ty, ert, d+1, env', false)
			      in (l, pp, ee)
			      end
			  val handling =
			      ListPair.map one_h (handling, h_t_l)
			  val rehandling =
			      ListPair.map one_h (rehandling, rh_t_l)
			  fun do_ca (p, e) =
			      let val t = mfreshty d
				  val (pp, env', _) =
				      elpat (p, r, t, d, env, false)
				  val ee =
				      elab (e, r, ty, ert, d+1, env', false)
			      in (pp, ee)
			      end
		      in A.TRYexp { scrutinee = scrutinee_e,
				    ert = ert',
				    success = (succ_pp, succ_ee),
				    handling = handling,
				    rehandling = rehandling,
				    catchall = ca }
		      end
		  | S.RAISEexp e =>
		      let val st = mksumty (ert, r)
			  val ee = el (e, st)
		      in A.RAISEexp (ee, ty)
		      end
		  | S.MARKexp (e, r) =>
		      A.MARKexp (elab (e, r, ty, ert, d, env, pdef), r)
	    end

	    (* TODO: need to do an SCC decomposition here *)
	    (*    - every function sees every function (in funl)
	     *    - every rcl entry sees every function
	     *    - every function sees every rcl entry
	     *    - rcl entries see other rcl entries if
	     *      they appear earlier within rcl *)
	    and elfuns (funl, rcl, ert, r, d, env) =
		let fun checkdup_rc ([], _) = ()
		      | checkdup_rc (S.RC (n, _, nr) :: t, s) =
			  if Symbol.Set.member (s, n) then
			      error1 nr ["name `",
					 Symbol.toString n,
					 "'for recursive cases already \
					 \defined here"]
			  else checkdup_rc (t, Symbol.Set.add (s, n))
		    fun checkdup_f ([], s) = checkdup_rc (rcl, s)
		      | checkdup_f (S.FUN (f, _, _, fr) :: t, s) =
			  if Symbol.Set.member (s, f) then
			      error1 fr ["duplicate function `",
					Symbol.toString f]
			  else checkdup_f (t, Symbol.Set.add (s, f))
		    val _ = checkdup_f (funl, Symbol.Set.empty)
		    fun bind_f (S.FUN (n, _, _, _), ts, env) =
			bindTys (n, ts, env)
		    fun bind_rc (S.RC (n, _, _), t, env) = bindTy (n, t, env)

		    fun mkftys (S.FUN (_, pl, e, r)) =
			let fun freshtys () = T.PLAINtys (TU.freshty (d, r))
			    fun onep (p, (rhsval, rhsty, i, kl)) =
				let val (erts, i') =
					if rhsval then (T.REFrtys i, i+1)
					else (TU.freshrtys0 (d, r), i)
				in (true,
				    T.FUNtys (freshtys (), rhsty, erts, r),
				    i',
				    Types.unconstrained :: kl)
				end
			    val (_, ftys, _, rargs) =
				foldr onep (S.isSynVal e, freshtys (), 0, []) pl
			in { targs = 0, rargs = rargs, body = ftys }
			end

		    val ftysl = map mkftys funl
		    val ftyl = map (#1 o TU.instantiate (d, r)) ftysl

		    val rctyl =
			map (fn S.RC (_, _, r) => TU.freshty (d, r)) rcl
		    val env_f = ListPair.foldl bind_f env (funl, ftysl)

		    (* recursive cases are evaluated one by one (in order),
		     * building up the environment along the way *)
		    fun one_rc (S.RC (n, rhs, r), rcty, (rl, env)) =
			let fun mfreshty d = TU.freshty (d, r)
			    val rt = TU.freshrty0 (d, r)
			    val resty = mfreshty d
			    val _ = unify r (rcty,
					     T.MATCHty (rt, resty, ert, r))
			    val rhs' = elab (rhs, r, rcty, ert, d+1,
					     env, false)
			    val env' = bindTy (n, rcty, env)
			in ({ c = n, ct = rcty, rhs = rhs' } :: rl, env')
			end

		    val (r_rcl_elab, env_full) =
			ListPair.foldl one_rc ([], env_f) (rcl, rctyl)
		    val rcl_elab = rev r_rcl_elab

		    (* functions are evaluated in full env: *)
		    fun one_f (S.FUN (n, pl, b, r), fty) =
			let fun mfreshty d = TU.freshty (d, r)
			    val resty0 = mfreshty d
			    fun onepat (p, (resty, ppl, env, ert, vs)) =
				let val t = mfreshty d
				    val (pp, env', vs') =
					elpat (p, r, t, d, env, false)
				in (T.FUNty (t, resty, ert, r),
				    pp :: ppl, env',
				    TU.freshrty0 (d, r),
				    joinvs (vs, vs', r))
				end
			    val ert' = TU.freshrty0 (d, r)
			    val (funty, ppl, env'', _, _) =
				foldr onepat
				      (resty0, [], env_full,
				       ert', Symbol.Set.empty)
				      pl
			    val _ = unify r (fty, funty)
			    val b' = elab (b, r, resty0, ert', d+1,
					   env'', false)
			in (n, ppl, b')
			end

		    val funl_elab = ListPair.map one_f (funl, ftyl)

		    val (ftysl, pri) = TU.generalize' d ftyl
		    val rctysl = map t2ts rctyl

		    fun makegen ((n, pl, b), ftys, (funl, env)) =
			({ f = n, params = pl, body = b } :: funl,
			 bindTys (n, ftys, env))

		    val (rfunl', env_gen_f) =
			ListPair.foldl makegen ([], env) (funl_elab, ftysl)

		    val env_res = ListPair.foldl bind_rc env_gen_f (rcl, rctyl)
		in (rev rfunl', pri, rcl_elab, env_res)
		end
	in elab (mainexp, mainregion, T.INTty mainregion,
		 T.EMPTYrty mainregion, 0, baseenv, pdefs)
	end
end
