(* translate.sml
 *
 *   Type-directed translation from Absyn to Lambda.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Translate : sig

    val translate : Absyn.program * Lambda.exp Env.env ->
		    { lambda: Lambda.function,
		      strings: (string * Label.label) list }

end = struct

    fun bug m = ErrorMsg.impossible ("Translate: " ^ m)

    structure O = Oper
    structure S = Ast
    structure A = Absyn
    structure P = Purity
    structure L = Lambda
    structure T = Types
    structure TU = TypesUtil
    structure RL = RecordLabel
    structure LD = LiteralData

    structure SM = RedBlackMapFn (type ord_key = string
                                  val compare = String.compare)

    fun int i = L.VALUE (L.INT i)

    (* Invariant: wordSize is even, so the result of recidx
     * does not need any further tagging and will be recognized
     * as a non-pointer by the GC. *)
    fun recidx i = int (i * MachSpec.wordSize)

    val zeroval = int 0
    val oneval = int 2

    val zeroidx = recidx 0
    val oneidx = recidx 1
    fun incidx e = L.ARITH (O.PLUS, e, oneidx)

    fun var v = L.VALUE (L.VAR v)

    fun vapp (e, el) = L.APP (P.Impure, e, el)
    fun papp (e, el) = L.APP (P.Pure, e, el)
    fun tapp (e, el) = papp (e, el)

    val blackhole = ExternalAccess.access "mlpr_cases_blackhole_fun"

    type lbinding = LVar.lvar
    type rhobinding = lbinding RL.Map.map * lbinding option
    type tenv = rhobinding T.RTMap.map

    type vbinding = L.exp
    type venv = vbinding Env.env

    datatype texp =
	Ex of L.exp
      | Cx of L.exp * L.exp -> L.exp

    fun unEx (Ex e) = e
      | unEx (Cx mke) = mke (oneval, zeroval)

    fun unCx (Cx mke) = mke
      | unCx (Ex e) = (fn (te, fe) => L.CMP (O.EQ, e, zeroval, fe, te))

    fun swap (x, y) = (y, x)

    fun bindvar (v, x, ve) = Env.bind (v, L.VALUE x, ve)
    fun findvar (v, ve) = Env.find (ve, v)

    (*** new index calculation (as in ICFP paper): *)

    (* (r)labels: (row)type -> labelset * rowvarinfo option
     *   - rowvarinfo is a pair: rowvar * excluded *)
    fun rlabels rt =
	let fun rtloop (T.VARrty rv, s) =
		(case TVar.rget rv of
		     T.ROPEN (_, k, r) => (s, SOME (rv, k))
		   | T.RINST rt => rtloop (rt, s))
	      | rtloop (T.EMPTYrty _, s) = (s, NONE)
	      | rtloop (T.FIELDrty ((l, _), rt), s) =
		  rtloop (rt, RL.Set.add (s, l))
	in rtloop (rt, RL.Set.empty)
	end

    fun labels t =
	let fun tloop (T.VARty v) =
		  (case TVar.tget v of
		       T.INST t => tloop t
		     | _ => bug "labels: not instantiated")
	      | tloop (T.CONty ((T.RECORDtyc _ | T.SUMtyc), _, [rt], _)) =
		  rlabels rt
	      | tloop (T.CONty (T.MATCHtyc, _, [rt, _], _)) =
		  rlabels rt
	      | tloop (T.CONty _) = bug "labels: not a RECORD, SUM, or MATCH"
	in tloop t
	end

    fun labels' t =
	let val (s, rvi) = labels t in (RL.Set.listItems s, rvi) end

    (* Number of labels in a set that is smaller than the given label. *)
    fun pos (l, s) = RL.Set.numItems
			 (RL.Set.filter (fn l' => RL.gt (l, l')) s)

    (* index0 : option * index map -> indexexp *)
    fun index0 (l, im) =
	  (case RL.Map.find (im, l) of
	       NONE => bug "label info not found"
	     | SOME v => var v)

    fun rigidindex (l, s) = recidx (LD.fromInt (pos (l, s)))

    (* index: typenv * label * (labelset * rowvarinfo option) -> indexexp *)
    fun index (te, l, (s, NONE)) = rigidindex (l, s)
      | index (te, l, (s, SOME (rv, excl))) =
	  (case T.RTMap.find (te, rv) of
	       SOME im =>
	         let val idx0 = index0 (l, im)
		     val adj = pos (l, RL.Set.difference (RL.map2set excl, s))
		 in if adj = 0 then idx0
		    else L.ARITH (O.MINUS, idx0, recidx (LD.fromInt adj))
		 end
	     | NONE => rigidindex (l, s))

    fun lenindex (te, t) = index (te, RL.LENlab, labels t)
    fun fieldindex (te, t, l) = index (te, l, labels t)
    fun exnindex (te, rt, l) = index (te, l, rlabels rt)

    (* index arguments (corresponding to row type applications in System F) *)

    fun indexargs (te, pri) =
	let fun onerv ((rv, excluded), rest) =
		let val (s, rvi) = rlabels (T.VARrty rv)
		    val s'excl = RL.Set.union (s, excluded)
		    fun oneidx (l, rest) =
			index (te, l, (s'excl, rvi)) :: rest
		in foldr oneidx rest (RL.Set.listItems excluded)
		end
	in foldr onerv [] pri
	end

    fun getvarexp (A.MARKexp (e, _)) = getvarexp e
      | getvarexp (A.VARexp (sy, sty, pri)) = SOME (sy, sty, pri)
      | getvarexp _ = NONE

    fun SEL (x, y) = L.SELECT (x, y, P.Pure) (* immutable selection *)

    fun pair (x, y) =
	L.RECORD { purity = Purity.Pure,
		   len = recidx 2,
		   slices = [L.SGT x, L.SGT y] }
    fun car x = SEL (x, zeroidx)
    fun cdr x = SEL (x, oneidx)

    fun translate (main, ve) =
	let val newvar = LVar.new
	    val clonevar = LVar.clone
	    fun mkvar v = newvar (Symbol.toString v)
	    fun idxvar () = newvar "idx"
	    fun tmpvar () = newvar "tmp"
	    fun patvar' (A.WILDpat) = newvar "wild"
	      | patvar' (A.VARpat v) = mkvar v
	      | patvar' (A.RECORDpat _) = newvar "rec"
	      | patvar' (A.MARKpat (p, _)) = patvar' p
	      | patvar' (A.ANDpat (p1, _)) = patvar' p1
	    fun patvar (p, _) = patvar' p
	    fun mknvars 0 = []
	      | mknvars n = tmpvar () :: mknvars (n-1)
	    val nextl = ref 0
	    val sm = ref SM.empty
	    fun string s =
		case SM.find (!sm, s) of
		    SOME l => l
		  | NONE => let val l = Label.stringlabel ()
			    in sm := SM.insert (!sm, s, l);
			       l
			    end
	    fun seq (e, Ex e') =
		  Ex (L.LET (tmpvar (), e, e'))
	      | seq (e, Cx mke) =
		  Cx (fn (te, fe) => L.LET (tmpvar (), e, mke (te, fe)))

	    fun priformals (pri, te) =
		let fun onerho ((rv, info), (vl, rte)) =
			let val excluded = info
			    fun onelab (l, (vl, im)) =
				let val v = idxvar ()
				in (v :: vl, RL.Map.insert (im, l, v))
				end
			    val (vl', im) =
				RL.Set.foldr onelab (vl, RL.Map.empty) excluded
			in (vl', T.RTMap.insert (rte, rv, im))
			end
		    val (vl, te') = foldr onerho ([], te) pri
		in (vl, te')
		end

	    fun pat ((p, (t, pri)), mkrhs, ve, te, k) =
		let val vv = patvar' p
		in case priformals (pri, te) of
		       ([], te') =>
		         L.LET (vv, mkrhs te',
				pat' (p, L.VAR vv, t, ve, te, k))
		     | (vl, te') =>
		         L.FIX ([(vv, vl, mkrhs te', false)],
				pat' (p, L.VAR vv, t, ve, te, k))
		end

	    (* and pat' (p, x, t, ve, te, k)  *)
	    and pat' (A.WILDpat, _, _, ve, te, k) =
		  k ve
	      | pat' (A.VARpat v, x, _, ve, _, k) =
		  k (bindvar (v, x, ve))
	      | pat' (A.MARKpat (p, _), x, t, ve, te, k) =
		  pat' (p, x, t, ve, te, k)
	      | pat' (A.ANDpat (p1, p2), x, t, ve, te, k) =
		  pat' (p1, x, t, ve, te,
			fn ve' => pat' (p2, x, t, ve', te, k))
	      | pat' (A.RECORDpat (purity, fpl, popt, pri), x, t, ve, te, k) =
		  let val fpl = RL.sortBy #1 fpl
		      val lset = RL.toSet #1 fpl
		      val nfields = LD.fromInt (RL.Set.numItems lset)
		      fun instrec te =
			  case indexargs (te, pri) of
			      [] => L.VALUE x
			    | idxl => tapp (L.VALUE x, idxl)
		      fun restrec (v, te) =
			  let val (fll, flex) = labels' t
			      val ptfl =
				  List.filter (fn l =>
						  not (RL.Set.member (lset, l)))
					      fll
			      val y = var v
			      fun head e = L.LET (v, instrec te, e)
			  in case flex of
				 NONE =>
				   (* we actually know all the labels... *)
				   let fun one l =
					   let val i = fieldindex (te, t, l)
					   in L.SGT (L.SELECT (y, i, purity))
					   end
				       val n = LD.fromInt (length ptfl)
				   in head (L.RECORD { purity = purity,
						       len = recidx n,
						       slices = map one ptfl })
				   end
			       | SOME (_, excluded) =>
				   (* we don't know all the labels, so we
				    * have to generate slices... *)
				   let fun seq (a, b) =
					 L.SEQ { base = y, start = a, stop = b }
				       fun build ([], si, a) =
					     let val ei = lenindex (te, t)
					     in (rev (seq (si, ei) :: a), ei)
					     end
					 | build ((l, _) :: fl, si, a) =
					     let val ei = fieldindex (te, t, l)
						 val si' = incidx ei
					     in build (fl, si',
						       seq (si, ei) :: a)
					     end
				       val (slices, leni) =
					   build (fpl, zeroidx, [])
				       val leni' =
					   L.ARITH (O.MINUS, leni,
						    recidx nfields)
				   in head (L.RECORD { purity = Purity.Impure,
						       len = leni',
						       slices = slices })
				   end
			  end
		      fun loop [] ve =
			    (case popt of
				 NONE => k ve
			       | SOME p =>
				   pat (p, fn te => restrec (patvar p, te),
					ve, te, k))
			| loop ((l, p) :: fpl) ve =
			    let val i = fieldindex (te, t, l)
			    in pat (p, fn te => L.SELECT (instrec te, i, purity),
				    ve, te, loop fpl)
			    end
		  in loop fpl ve
		  end

	    fun exp (A.LETexp (dl, b), ve, te, eh) =
		  let fun build ([], ve) = unEx (exp (b, ve, te, eh))
			| build ((A.VALdef (p, _, e), _) :: dl, ve) =
			    pat (p, fn te => unEx (exp (e, ve, te, eh)), ve, te,
			         fn ve' => build (dl, ve'))
			| build ((A.FUNdef (fl, pri, rcl), _) :: dl, ve) =
			    let val (header, ve') =
				    funl (fl, pri, rcl, ve, te, eh)
			    in header (build (dl, ve'))
			    end
		  in Ex (build (dl, ve))
		  end
	      | exp (A.IFexp (e1, e2, e3, t), ve, te, eh) =
		  let val c1 = unCx (exp (e1, ve, te, eh))
		  in case (exp (e2, ve, te, eh), exp (e3, ve, te, eh)) of
			 (Ex x2, ee3) => Ex (c1 (x2, unEx ee3))
		       | (ee2, Ex x3) => Ex (c1 (unEx ee2, x3))
		       | (Cx c2, Cx c3) =>
			   let val (tv, fv) = (tmpvar (), tmpvar ())
			   in Cx (fn (te, fe) =>
				     L.FIX ([(tv, [], te, false),
					     (fv, [], fe, false)],
					    c1 (c2 (vapp (var tv, []),
						    vapp (var fv, [])),
						c3 (vapp (var tv, []),
						    vapp (var fv, [])))))
			   end
		  end
	      | exp (A.LCASEexp (e, ne, hp, tp, ce, t), ve, te, eh) =
		  let val x = unEx (exp (e, ve, te, eh))
		      val vx = tmpvar ()
		      val nx = unEx (exp (ne, ve, te, eh))
		      val hv = patvar hp
		      val tv = patvar tp
		  in Ex (L.LET (vx, x,
			L.CMP (O.EQ, var vx, zeroval,
			       nx,
			       L.LET (hv, car (var vx),
			       L.LET (tv, cdr (var vx),
			       pat (hp, fn _ => var hv,
				    ve, te,
			       fn ve' => pat (tp, fn _ => var tv,
					      ve', te,
			       fn ve'' => unEx (exp (ce, ve'', te, eh)))))))))
		  end
	      | exp (A.WHEREexp (p, e, et, fl, t), ve, te, eh) =
		  updtrec ([], e, et, fl, t, ve, te, eh, false, p)
	      | exp (A.UOPexp (S.UMINUS, e, t), ve, te, eh) =
		  Ex (L.ARITH (O.MINUS, zeroval, unEx (exp (e, ve, te, eh))))
	      | exp (A.UOPexp ((S.NOT | S.ISNULL), e, t), ve, te, eh) =
		  Cx (unCx (exp (e, ve, te, eh)) o swap)
	      | exp (A.BINOPexp (S.BOOLCONN bc, e1, e2, t), ve, te, eh) =
		  let val c1 = unCx (exp (e1, ve, te, eh))
		      val c2 = unCx (exp (e2, ve, te, eh))
		      val f = tmpvar ()
		  in case bc of
			 S.ANDALSO =>
			   Cx (fn (te, fe) =>
				  L.FIX ([(f, [], fe, false)],
					 c1 (c2 (te, vapp (var f, [])),
					     vapp (var f, []))))
		       | S.ORELSE =>
			   Cx (fn (te, fe) =>
				  L.FIX ([(f, [], te, false)],
					 c1 (vapp (var f, []),
					     c2 (vapp (var f, []),
						 fe))))
		  end
	      | exp (A.BINOPexp (S.CMP co, e1, e2, t), ve, te, eh) =
		  let val x1 = unEx (exp (e1, ve, te, eh))
		      val x2 = unEx (exp (e2, ve, te, eh))
		  in Cx (fn (te, fe) => L.CMP (co, x1, x2, te, fe))
		  end
	      | exp (A.BINOPexp (S.ARITH ao, e1, e2, t), ve, te, eh) =
		  let val x1 = unEx (exp (e1, ve, te, eh))
		      val x2 = unEx (exp (e2, ve, te, eh))
		  in Ex (L.ARITH (ao, x1, x2))
		  end
	      | exp (A.BINOPexp (S.CONS, e1, e2, t), ve, te, eh) =
		  cons (e1, e2, ve, te, eh)
	      | exp (A.APPexp (e1, e2, t), ve, te, eh) =
		  Ex (vapp (unEx (exp (e1, ve, te, eh)),
			    [var eh, unEx (exp (e2, ve, te, eh))]))
	      | exp (A.ASSIGNexp (e1, e1t, lab, e2), ve, te, eh) =
		  let val x1 = unEx (exp (e1, ve, te, eh))
		      val x2 = unEx (exp (e2, ve, te, eh))
		  in Ex (L.UPDATE (x1, fieldindex (te, e1t, lab), x2))
		  end
	      | exp (A.SELexp (purity, e, et, lab, t), ve, te, eh) =
		  let val x = unEx (exp (e, ve, te, eh))
		  in Ex (L.SELECT (x, fieldindex (te, et, lab), purity))
		  end
	      | exp (A.BOOLexp b, ve, te, eh) =
		  Cx (fn (te, fe) => if b then te else fe)
	      | exp (A.NUMBERexp i, ve, te, eh) =
		  Ex (int i)
	      | exp (A.STRINGexp s, ve, te, eh) =
		  Ex (L.VALUE (L.LABEL (string s)))
	      | exp (A.UNITexp, ve, te, eh) =
		  Ex zeroval
	      | exp (A.VARexp (s, t, pri), ve, te, eh) =
		  (case findvar (s, ve) of
		       NONE => bug ("unbound variable: " ^ Symbol.toString s)
		     | SOME e =>
		         (case indexargs (te, pri) of
			      [] => Ex e
			    | idxl => Ex (tapp (e, idxl))))
	      | exp (A.SEQexp (e1, e2), ve, te, eh) =
		  seq (unEx (exp (e1, ve, te, eh)), exp (e2, ve, te, eh))
	      | exp (A.LISTexp (el, t), ve, te, eh) =
		  (case el of
		       [] => Ex zeroval
		     | h :: tl => cons (h, A.LISTexp (tl, t), ve, te, eh))
	      | exp (A.RECORDexp (purity, fl, NONE, t), ve, te, eh) =
		  let val vfl = map (fn f => (tmpvar (), f)) fl
		      val sorted = RL.sortBy (#1 o #2) vfl
		      val len = LD.fromInt (length sorted)
		      val record =
			  L.RECORD { purity = purity,
				     len = recidx len,
				     slices = map (L.SGT o var o #1) sorted }
		      fun onefield ((v, (l, e)), b) =
			  L.LET (v, unEx (exp (e, ve, te, eh)), b)
		  in Ex (foldr onefield record vfl)
		  end
	      | exp (A.RECORDexp (p, fl1, SOME (e0, t0, fl2), t), ve, te, eh) =
		  updtrec (fl1, e0, t0, fl2, t, ve, te, eh, true, p)
	      | exp (A.CONexp ((l, e), t), ve, te, eh) =
		  Ex (pair (fieldindex (te, t, l), unEx (exp (e, ve, te, eh))))
	      | exp (A.SWIDENexp (e, t0, l, t1), ve, te, eh) =
		  let val (v, tagv) = (tmpvar (), tmpvar ())
		      val vx = var v
		      val tagvx = var tagv
		  in Ex (L.LET (v, unEx (exp (e, ve, te, eh)),
			 L.LET (tagv, car vx,
			 L.CMP (Oper.GTEQ, tagvx, fieldindex (te, t1, l),
				pair (incidx tagvx, cdr vx),
				vx))))
		  end
	      | exp (A.PSCASEexp (e, m, t), ve, te, eh) =
		  let val ev = tmpvar () val ex = var ev
		      val mv = tmpvar () val mx = var mv
		  in Ex (L.LET (ev, unEx (exp (e, ve, te, eh)),
			 L.LET (mv, unEx (exp (m, ve, te, eh)),
				vapp (SEL (mx, car ex), [var eh, cdr ex]))))
		  end
	      | exp (A.FNexp (p, e, t), ve, te, eh) =
		  let val f = newvar "fn"
		      val v = patvar p
		      val eh' = newvar "eh"
		  in Ex (L.FIX ([(f, [eh', v],
				  pat (p, fn _ => var v,
				       ve, te,
				       fn ve' => unEx (exp (e, ve', te, eh'))),
				  false)],
				var f))
		  end
	      | exp (A.RAISEexp (e, t), ve, te, eh) =
		  let val v = newvar "exn"
		  in Ex (L.LET (v, unEx (exp (e, ve, te, eh)),
				vapp (var eh, [car (var v), cdr (var v)])))
		  end
	      | exp (A.TRYexp { scrutinee, ert, success = (sp, se),
				handling = [], rehandling = [],
				catchall = NONE }, ve, te, eh) =
		  Ex (pat (sp, fn te' => unEx (exp (scrutinee, ve, te', eh)),
			   ve, te, fn ve' => unEx (exp (se, ve', te, eh))))
(*
   (* this case is now subsumed by the next case *)
	      | exp (A.TRYexp { scrutinee, ert, success = (sp, se),
				handling = [], rehandling = [],
				catchall = SOME (cap, cae) }, ve, te, eh) =
		  let val eh' = newvar "eh"
		      val tagv = newvar "tagv"
		      val payloadv = newvar "payloadv"
		      val sumv = newvar "exnv"
		  in Ex (L.HANDLER
			   (eh', [tagv, payloadv],
			    L.LET (sumv, pair (var tagv, var payloadv),
			      pat (cap, fn _ => var sumv,
				   ve, te,
			           fn ve' => unEx (exp (cae, ve', te, eh)))),
			    pat (sp, fn te' =>
					unEx (exp (scrutinee, ve, te', eh')),
				 ve, te,
			         fn ve' => unEx (exp (se, ve', te, eh)))))
		  end
*)
	      | exp (A.TRYexp { scrutinee, ert, success = (sp, se),
				handling, rehandling, catchall }, ve, te, eh) =
		  let val eh' = newvar "eh"
		      val tagv = newvar "tag"
		      val payloadv = newvar "payload"
		      fun cmp3 (e1, e2, lt_e, eq_e, gt_e) =
			  let val v1 = newvar "tmp1"
			      val v2 = newvar "tmp2"
			  in L.LET (v1, e1,
			       L.LET (v2, e2,
				 L.CMP (O.EQ, var v1, var v2,
				   eq_e,
				   L.CMP (O.LT, var v1, var v2,
				     lt_e,
				     gt_e))))
			  end

		      val (ca_fun, cahdr, haveca) =
			  case catchall of
			      NONE => (eh, fn e0 => e0, false)
			    | SOME (ca_p, ca_e) =>
			        let val ca_f = newvar "ca"
				    val ca_tagv = newvar "catag"
				    val ca_payloadv = newvar "capayload"
				    val ca_sumv = newvar "casumv"
				    val ca_body =
					L.LET (ca_sumv,
					       pair (var ca_tagv,
						     var ca_payloadv),
					  pat (ca_p, fn _ => var ca_sumv,
					       ve, te,
					       fn ve' =>
						  unEx (exp (ca_e,
							     ve', te, eh))))
				    fun cahdr e0 =
					L.FIX ([(ca_f, [ca_tagv, ca_payloadv],
						 ca_body, false)], e0)
				in (ca_f, cahdr, true)
				end

		      fun mark m lpe = (lpe, m)
		      val hl = RL.sortBy (#1 o #1)
					 (map (mark true) handling @
					  map (mark haveca) rehandling)
		      fun count ((lpe, narrow), (rhl, i)) =
			  ((lpe, i) :: rhl, if narrow then i+1 else i)
		      val (rhl, maxadj) = foldl count ([], 0) hl
		      val ha = Array.fromList (rev rhl)
		      val alen = Array.length ha

		      fun bsearch (low, high, hadj) =
			  if high <= low then
			      let val newtag =
				      L.ARITH (O.MINUS, var tagv,
					       recidx (LD.fromInt hadj))
			      in vapp (var ca_fun, [newtag, var payloadv])
			      end
			  else let val mid = (high+low) div 2
				   val ((l, p, e), madj) = Array.sub (ha, mid)
				   val idx = exnindex (te, ert, l)
			       in cmp3 (var tagv, idx,
					bsearch (low, mid, madj),
					pat (p, fn _ => var payloadv,
					     ve, te,
					     fn ve' =>
						unEx (exp (e, ve', te, eh))),
					bsearch (mid+1, high, hadj))
			       end

		      val hdlr = bsearch (0, alen, maxadj)
		  in Ex (cahdr (L.HANDLER
			     (eh', [tagv, payloadv], hdlr,
			      pat (sp, fn te' =>
					  unEx (exp (scrutinee, ve, te', eh')),
				   ve, te,
				   fn ve' => unEx (exp (se, ve', te, eh))))))
		  end
	      | exp (A.MARKexp (e, r), ve, te, eh) = exp (e, ve, te, eh)

	    (* fl may or may not overlap with fields in e0 here *)
	    and updtrec (fl1, e0, t0, fl2, t, ve, te, eh, isextend, purity) =
		let val (fll, flex) = labels' t
		    val e0v = tmpvar ()
		    val vfl1 = map (fn f => (tmpvar (), f)) fl1
		    val vfl2 = map (fn f => (tmpvar (), f)) fl2
		    val vfl = vfl1 @ vfl2
		    fun thelab l (_, (l', _)) = RL.same (l, l')
		    fun onefield ((v, (_, e)), b) =
			L.LET (v, unEx (exp (e, ve, te, eh)), b)
		    fun return r =
			Ex (foldr onefield
				  (L.LET (e0v, unEx (exp (e0, ve, te, eh)),
					  foldr onefield r vfl2))
				  vfl1)
		in case flex of
		       SOME _ =>
		         (* Here we generate slices interspersed with
			  * singletons from those field lists *)
		         let fun seq (start, stop) =
				 L.SEQ { base = var e0v,
					 start = start,
					 stop = stop }
			     fun build ([], si, a) =
				   let val ei = lenindex (te, t0)
				   in rev (seq (si, ei) :: a)
				   end
			       | build (l :: fll, si, a) =
				   let val p = fieldindex (te, t0, l)
				       val (sgt, si') =
					   case List.find (thelab l) vfl of
					       NONE =>
					         (L.SELECT (var e0v, p, purity),
						  incidx p)
					     | SOME (v, _) =>
					         (var v,
						  if isextend then p
						  else incidx p)
				   in build (fll, si',
					     L.SGT sgt :: seq (si, p) :: a)
				   end
			     val slices = build (fll, zeroidx, [])
			     val len = lenindex (te, t)
			 in return (L.RECORD { purity = purity,
					       len = len,
					       slices = slices })
			 end
		     | NONE =>
		         (* we know all the fields, so we can
			  * generate a bunch of singletons: *)
		         let fun onel l =
				 case List.find (thelab l) vfl of
				     SOME (v, _) => L.SGT (var v)
				   | NONE =>
				       let val p = fieldindex (te, t0, l)
				       in L.SGT (L.SELECT (var e0v, p, purity))
				       end
			     val len = LD.fromInt (length fll)
			 in return (L.RECORD { purity = purity,
					       len = recidx len,
					       slices = map onel fll })
			 end
		end

	    and funl (fl, pri, rcl, ve, te, eh0) =
		let val f_vl = map (mkvar o #f) fl
		    fun bindf ({ f, params, body }, v, ve) =
			bindvar (f, L.VAR v, ve)
		    val ve_f = ListPair.foldl bindf ve (fl, f_vl)
		    val (rc_v, ve_result, rul) =
			case rcl of
			    [] => (NONE, ve_f, [])
			  | { c, ... } :: _ =>
			      let val v = newvar ("blkhl_" ^ Symbol.toString c)
				  val vx = L.VALUE (L.VAR v)
				  fun do_rc ({ c, ct, rhs } :: rcl, i, ve, ul) =
				      let val ie = recidx i
					  val acc_e =
					      L.SELECT (vx, ie, Purity.Impure)
					  val ve' = Env.bind (c, acc_e, ve)
					  val init_e =
					      unEx (exp (rhs, ve, te, eh0))
					  val updt_e = L.UPDATE (vx, ie, init_e)
				      in do_rc (rcl, i+1, ve', updt_e :: ul)
				      end
				   | do_rc ([], _, ve, ul) = (ve, ul)
				  val (ve', rul) = do_rc (rcl, 0, ve_f, [])
			      in (SOME v, ve', rul)
			      end
		    fun f_one ({ f = fname, params, body }, f) =
			let val (privl, te') = priformals (pri, te)
			    (* Inside the body of a function, re-bind
			     * all functions so that they are accessed
			     * via the appropriate type application.
			     *)
			    val bindfun =
				case privl of
				    [] => bindf
				  | _ =>
				      (fn (f, v, ve) =>
					  Env.bind (#f f,
						    tapp (var v, map var privl),
						   ve))
			    val ve' =
				ListPair.foldl bindfun ve_result (fl, f_vl)
			    fun dop (p, v, [], ve, eh) =
				  pat (p, fn _ => var v, ve, te',
				       fn ve' =>
					  unEx (exp (body, ve', te', eh)))
			      | dop (p, v, p' :: pl, ve, eh) =
				  let val f' = mkvar fname
				      val v' = patvar p'
				      val eh' = newvar "eh"
				  in pat (p, fn _ => var v, ve, te',
				          fn ve' =>
					     L.FIX ([(f', [eh', v'],
						     dop (p', v', pl, ve', eh'),
						      false)],
						    var f'))
				  end
			    val (p, pl) =
				case params of
				    p :: pl => (p, pl)
				  | _ => bug "translate: empty formals"
			    val v = patvar p
			    val eh = newvar "eh"
			    val body = dop (p, v, pl, ve', eh)
			in case privl of
			       [] => (f, [eh, v], body, false)
			     | vl => let val f' = mkvar fname
				     in (f, vl,
					 L.FIX ([(f', [eh, v], body, false)],
						var f'),
					 false)
				     end
			end

		    fun rc_one_alloc { c, ct, rhs } =
			L.SGT (papp (blackhole, [lenindex (te, ct)]))

		    val fl' = ListPair.map f_one (fl, f_vl)

		    val res_k =
			case rc_v of
			    NONE => (fn e => L.FIX (fl', e))
			  | SOME v =>
			      let val rc_x = L.VALUE (L.VAR v)
				  fun asgn (x, e) = L.LET (tmpvar (), x, e)
				  val rc_rec =
				      L.RECORD { purity = Purity.Impure,
						 len = recidx
						      (LD.fromInt (length rcl)),
						 slices = map rc_one_alloc rcl }
			      in fn e =>
				    L.LET (v, rc_rec,
					   L.FIX (fl', foldl asgn e rul))
			      end
		in (res_k, ve_result)
		end

	    and cons (h, t, ve, te, eh) =
		Ex (pair (unEx (exp (h, ve, te, eh)),
			  unEx (exp (t, ve, te, eh))))

	    val eh0 = newvar "eh0"
	    val main' = exp (main, ve, T.RTMap.empty, eh0)
	    val mainv = newvar "main"
	    val progfun = (mainv, [eh0], unEx main', false)
	in
	    { lambda = progfun, strings = SM.listItemsi (!sm) }
	end
end
