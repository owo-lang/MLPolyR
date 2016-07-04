(* unify.sml
 *
 *   Imperative unification of types.
 *
 * Copyright (c) 2006 by Matthias Blume (blume@tti-c.org)
 *)
structure Unify : sig

    exception Unify of (Ast.region * Ast.region) * string

    val unify : Types.typ * Types.typ -> unit
    val runify : Types.rtyp * Types.rtyp -> unit

end = struct

    fun bug m = ErrorMsg.impossible ("Unify: " ^ m)

    exception Unify of (Ast.region * Ast.region) * string

    structure S = Ast
    structure T = Types
    structure TU = TypesUtil

    structure RL = RecordLabel
    structure LM = RL.Map

    fun error rr m = raise Unify (rr, m)
    fun extrafield (r, r', l) =
	error (r, r') ("missing or extra record field " ^ RL.toString l)

    datatype var =
	TYVAR of T.tyvar
      | RTYVAR of T.rtyvar
      | NOVAR

    exception Circularity

    fun adjust (v, d, t) =
	let val visited = ref T.TSet.empty
	    fun adj v (T.VARty tv') =
		  if T.TSet.member (!visited, tv') then ()
		  else (visited := T.TSet.add (!visited, tv');
			case TVar.tget tv' of
			    T.INST t => adj v t
			  | T.OPEN (d', r') =>
	                      (TVar.tset (tv', T.OPEN (Int.min (d, d'), r'));
			       case v of
				   TYVAR tv =>
		                     if TVar.teq (tv, tv') then
					 raise Circularity
				     else ()
				 | (RTYVAR _ | NOVAR) => ()))
	      | adj v (T.CONty (T.SUMtyc, [], [rt], _)) =
		  (* occurs check is turned off after stepping into
		   * a SUM type: *)
		  radj NOVAR rt
	      | adj v (T.CONty (T.MATCHtyc, [t], [rt], _)) =
		  (adj v t;
		   (* a match type has an implicit sum type inside ->
		    * turn occurs check off *)
		   radj NOVAR rt)
	      | adj v (T.CONty (_, tl, rtl, _)) = (app (adj v) tl;
						   app (radj v) rtl)
	    and radj v (T.VARrty rtv') =
		  (case TVar.rget rtv' of
		       T.RINST rt => radj v rt
		     | T.ROPEN (d', k, r') =>
		         (TVar.rset (rtv', T.ROPEN (Int.min (d, d'), k, r'));
			  case v of
			      RTYVAR rtv =>
			        if TVar.req (rtv, rtv') then raise Circularity
				else ()
			    | (TYVAR _ | NOVAR) => ()))
	      | radj v (T.EMPTYrty _) = ()
	      | radj v (T.FIELDrty ((_, (t, _)), rt)) = (adj v t; radj v rt)
	in adj v t
	end

    fun unify_vt (v, t') =
	case TVar.tget v of
	    T.INST (t as T.VARty vv) =>	(* not sure if we need this case *)
	      if TVar.link (v, vv) then unify_vt (vv, t')
	      else bug "strange recursive type"
	  | T.INST t => unify (t, t')
	  | T.OPEN (d, r) =>
	      (adjust (TYVAR v, d, t')
	       handle Circularity => error (r, T.regionOf t') "circularity";
	       TVar.tset (v, T.INST t'))

    and unify (t as T.VARty v, t' as T.VARty v') =
	  let val tvv = TVar.tget v
	      val tvv' = TVar.tget v'
	  in if TVar.link (v, v') then
		 case (tvv, tvv') of
		     (T.INST t, _) => unify (t, t')
		   | (_, T.INST t') => unify (t, t')
		   | (T.OPEN (d, r), T.OPEN (d', _)) =>
		       TVar.tset (v, T.OPEN (Int.min (d, d'), r))
	     else ()
	  end
      | unify (t as T.VARty v, t') = unify_vt (v, t')
      | unify (t, t' as T.VARty v') = unify_vt (v', t)
      | unify (T.CONty (tyc, tl, rtl, r), T.CONty (tyc', tl', rtl' ,r')) =
	  if T.sameTyc (tyc, tyc') then
	      ((ListPair.appEq unify (tl, tl'))
	       handle ListPair.UnequalLengths =>
		      bug "CONty arity mismatch (ty)";
	       (ListPair.appEq runify (rtl, rtl'))
	       handle ListPair.UnequalLengths =>
		      bug "CONty arity mismatch (rty)")
	  else error (r, r')
		     (concat ["tycon mismatch: ",
			      TU.tyc2string tyc, " vs. ", TU.tyc2string tyc'])

    and runify (rt, rt') =
	let fun collect (T.VARrty v, fs) =
		  (case TVar.rget v of
		       T.RINST rt => collect (rt, fs)
		     | T.ROPEN (d, e, r) => (fs, SOME (v, d, e), r))
	      | collect (T.FIELDrty (f, rt), fs) = collect (rt, f :: fs)
	      | collect (T.EMPTYrty r, fs) = (fs, NONE, r)
	    val (fs, vopt, r) = collect (rt, [])
	    val (fs', vopt', r') = collect (rt', [])
	    val fl = RL.sortBy #1 fs
	    val fl' = RL.sortBy #1 fs'
	    fun split ([]: T.typ T.field list, fl', tpl, ofl, ofl') =
		  (rev ofl, List.revAppend (ofl', fl'), tpl)
	      | split (fl, [], tpl, ofl, ofl') =
		  (List.revAppend (ofl, fl), rev ofl', tpl)
	      | split ((f as (l, (t, _))) :: fl, (f' as (l', (t', _))) :: fl',
		       tpl, ofl, ofl') =
		  (case RL.compare (l, l') of
		       LESS => split (fl, f' :: fl', tpl, f :: ofl, ofl')
		     | GREATER => split (f :: fl, fl', tpl, ofl, f' :: ofl')
		     | EQUAL => split (fl, fl', (t, t') :: tpl, ofl, ofl'))
	    val (ofl, ofl', tpl) = split (fl, fl', [], [], [])
	    (* Unification of common fields could instantiate vopt
	     * or vopt', so we must defer these steps until the shape
	     * of rt and rt' have been unified already. Therefore, we
	     * run unification of these common fields last. *)
	    fun finish () = app unify tpl
	    fun inst (v, d, e, fl, tail) =
		(app (fn (_, (t, _)) => adjust (RTYVAR v, d, t)) fl
		 handle Circularity => error (r, r') "circularity";
		 case List.find (fn (l, _) => LM.inDomain (e, l)) fl of
		     SOME (l, (_, r)) =>
		       extrafield (r, LM.lookup (e, l), l)
		   | NONE => TVar.rset (v, T.RINST (foldr T.FIELDrty tail fl)))
	    fun onevar (v, r, d, e, fl, []) =
		  (inst (v, d, e, fl, T.EMPTYrty r);
		   finish ())
	      | onevar (_, r, _, _, _, (l, (_, r')) :: _) =
		  extrafield (r, r', l)
	in case (vopt, vopt') of
	       (SOME (v, d, rg), SOME (v', d', rg')) =>
	         let val excl = LM.unionWith #1 (rg, rg')
		     val kk = excl
		     val tail =
			 (********** TODO: the region argument needs some re-thinking here *)
			 T.VARrty (TVar.rvar (T.ROPEN (Int.min (d, d'), kk, r)))
		 in inst (v, d, rg, ofl', tail);
		    inst (v', d', rg', ofl, tail);
		    finish ()
		 end
	     | (SOME (v, d, rg), NONE) =>
	         onevar (v, r, d, rg, ofl', ofl)
	     | (NONE, SOME (v', d', rg')) =>
	         onevar (v', r', d', rg', ofl, ofl')
	     | (NONE, NONE) =>
	         (case (ofl, ofl') of
		      ([], []) => finish ()
		    | ((l, _) :: _, _) => extrafield (r, r', l)
		    | (_, (l, _) :: _) => extrafield (r, r', l))
	end
end
