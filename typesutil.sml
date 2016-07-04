(* typesutil.sml
 *
 *   Utility routines that work on MLPolyR types.
 *
 * Copyright (c) 2006 by Matthias Blume (blume@tti-c.org)
 *)
structure TypesUtil : sig

    val freshty   : Types.depth * Types.region -> Types.typ
    val freshrty  : Types.depth * Types.exclusion * Types.region -> Types.rtyp
    val freshrty1 : Types.depth * RecordLabel.label * Types.region -> Types.rtyp
    val freshrty0 : Types.depth * Types.region -> Types.rtyp
    val freshrtys0: Types.depth * Types.region -> Types.rtyps

    val generalize : Types.depth -> Types.typ -> Types.typschema * Types.pri
    (* simultaneous generalization of several types,
     * used for mutual recursion where we need consistent pri
     * across all schemas: *)
    val generalize' : Types.depth ->
		      Types.typ list -> Types.typschema list * Types.pri
    val dontgeneralize : Types.typ ->  Types.typschema * Types.pri
    val instantiate : Types.depth * Types.region ->
		      Types.typschema -> Types.typ * Types.pri

    val mkPrinter : unit -> Types.typschema -> string

    val mkRecordTyp : (string * Types.typ * Types.region) list * Types.region
		      -> Types.typ

    val tyc2string : Types.tycon -> string
    val type2string : Types.typ -> string
end = struct

    structure RL = RecordLabel
    structure LS = RL.Set
    structure LM = RL.Map

    fun bug m = ErrorMsg.impossible ("TypesUtil: " ^ m)

    structure T = Types
    structure IM = IntRedBlackMap

    fun freshty (d, r) = T.VARty (TVar.tvar (T.OPEN (d, r)))
    fun freshrty (d, excluded, r) =
	T.VARrty (TVar.rvar (T.ROPEN (d, excluded, r)))
    fun freshrty0 (d, r) =
	T.VARrty (TVar.rvar (T.ROPEN (d, T.unconstrained, r)))
    fun freshrty1 (d, l, r) = freshrty (d, LM.singleton (l, r), r)
    fun freshrtys0 (d, r) =
	T.VARrtys (TVar.rvar (T.ROPEN (d, T.unconstrained, r)))

    fun pri_rvk excluded = RL.map2set excluded

    fun generalize0 isOk tl =
	(* common subtype detection turned off; this needs work *)
	let (* positive values correspond to generalized variables: *)
	    val nta = ref 0
	    val gtm = ref T.TMap.empty
	    val nra = ref 0 and rargs = ref [] and pri = ref []
	    val grm = ref T.RTMap.empty
	    fun targ (v, r) =
		let val i = !nta
		in nta := i+1;
		   gtm := T.TMap.insert (!gtm, v, i);
		   i
		end
	    fun tfind (tm, v) =
		case T.TMap.find (!gtm, v) of
		    SOME tsv => SOME tsv
		  | NONE => T.TMap.find (tm, v)

	    fun rarg (rv, k) =
		let val i = !nra
		in nra := i+1;
		   rargs := k :: !rargs;
		   pri := (rv, pri_rvk k) :: !pri;
		   grm := T.RTMap.insert (!grm, rv, i);
		   i
		end
	    fun rfind rv = T.RTMap.find (!grm, rv)
	    (* negative values mark sums *)
	    val ntm = ref (~1)
	    fun smarker () = let val i = !ntm in ntm := i-1; i end

	    (* process a type *)
	    fun typ tm (T.VARty v) =
		  (case tfind (tm, v) of
		       SOME tsv => T.REFtys tsv
		     | NONE =>
		         (case TVar.tget v of
			      T.INST (t as T.CONty (T.SUMtyc, _, _, _)) =>
			        let val tsv = smarker ()
				    val tm' = T.TMap.insert (tm, v, tsv)
				in T.MUtys (tsv, typ tm' t, T.regionOf t)
				end
			    | T.INST t => typ tm t
			    | T.OPEN (d, r) =>
		                if isOk d then
				    let val tsv = targ (v, r)
				    in T.REFtys tsv
				    end
				else T.PLAINtys (T.VARty v)))
	      | typ tm (T.CONty (tc, tl, rtl, r)) =
		  T.CONtys (tc, map (typ tm) tl, map (rtyp tm) rtl, r)

	    (* process a row *)
	    and rtyp tm (T.VARrty rv) =
		  (case rfind rv of
		       SOME rtsv => T.REFrtys rtsv
		     | NONE =>
		         (case TVar.rget rv of
			      T.RINST rt => rtyp tm rt
			    | T.ROPEN (d, k, _) =>
			        if isOk d then
				    let val rtsv = rarg (rv, k)
				    in T.REFrtys rtsv
				    end
				else T.VARrtys rv))
	      | rtyp tm (T.EMPTYrty r) = T.EMPTYrtys r
	      | rtyp tm (T.FIELDrty (f, rt)) =
		  T.FIELDrtys (field tm f, rtyp tm rt)

	    (* process a record field or a sum element *)
	    and field tm (l, (t, r)) = (l, (typ tm t, r))

	    (* do it: *)
	    val bodies = map (typ T.TMap.empty) tl
	    val targs = !nta
	    val rargs = List.rev (!rargs)

	    val schemas =
		map (fn b => { targs = targs, rargs = rargs, body = b }) bodies

	    val pri = List.rev (!pri)
	in (schemas, pri)
	end

    fun generalize' d = generalize0 (fn d' => d' >= d)
    fun generalize d t =
	case generalize' d [t] of
	    ([ts], pri) => (ts, pri)
	  | _ => bug "generalize: bogus result from generalize'"
    fun dontgeneralize0 t =
	case generalize0 (fn _ => false) [t] of
	    ([ts], []) => (ts, [])
	  | _ => bug "dontgeneralize0: bogus result form generalize0"
    fun dontgeneralize t =
	({ targs = 0, rargs = [], body = T.PLAINtys t }, [])

    fun instantiate (d, r) { targs, rargs, body } =
	let (* add entry for generalized type var *)

	    val tm0 =
		let fun loop (i, m) =
			if i >= targs then m
			else let val v = TVar.tvar (T.OPEN (d, r))
			     in loop (i+1, IM.insert (m, i, v))
			     end
		in loop (0, IM.empty)
		end

	    (* add entry for generalized row var *)
	    fun rarg (k, (i, l, m)) =
		let val rv = TVar.rvar (T.ROPEN (d, k, r))
		in (i+1, (rv, pri_rvk k) :: l, IM.insert (m, i, rv))
		end

	    val (_, rpri, rm0) = foldl rarg (0, [], IM.empty) rargs

	    fun typ m (T.PLAINtys t) = t
	      | typ m (T.CONtys (tc, tl, rtl, r)) =
		  T.CONty (tc, map (typ m) tl, map (rtyp m) rtl, r)
	      | typ m (T.MUtys (tsv, ts, r)) =
		  let val v = TVar.tvar (T.OPEN (d, r))
		      val m' = IM.insert (m, tsv, v)
		      val t = typ m' ts
		  in TVar.tset (v, T.INST t);
		     T.VARty v
		  end
	      | typ m (T.REFtys tsv) =
		  (case IM.find (m, tsv) of
		       SOME v => T.VARty v
		     | NONE => bug "REFtys")

	    and rtyp m (T.VARrtys rv) = T.VARrty rv
	      | rtyp m (T.EMPTYrtys r) = T.EMPTYrty r
	      | rtyp m (T.FIELDrtys (f, rts)) =
		  T.FIELDrty (field m f, rtyp m rts)
	      | rtyp m (T.REFrtys rtsv) =
		  (case IM.find (rm0, rtsv) of
		       SOME rv => T.VARrty rv
		     | NONE => bug "REFrtys")

	    and field m (l, (ts, r)) = (l, (typ m ts, r))

	    (* build the body *)
	    val t = typ tm0 body
	in (t, rev rpri)
	end

    fun t2ts t = #body (#1 (dontgeneralize0 t))

    fun printinfo body =
	let fun join_t (i, i') = i + i'
	    fun join_r ((i, ls), (i', ls')) = (i + i', LS.union (ls, ls'))

	    fun join ((btvm, brvm, fts, frs), (btvm', brvm', fts', frs')) =
		(IM.unionWith join_t (btvm, btvm'),
		 IM.unionWith join_r (brvm, brvm'),
		 T.TSet.union (fts, fts'),
		 T.RTSet.union (frs, frs'))

	    fun list f [] =
		  ([], (IM.empty, IM.empty, T.TSet.empty, T.RTSet.empty))
	      | list f (h :: t) =
		  let val (h', mh) = f h
		      val (t', mt) = list f t
		  in (h' :: t', join (mh, mt))
		  end

	    fun typ (ts as T.PLAINtys (T.VARty v)) =
		  (case TVar.tget v of
		       T.INST t => typ (t2ts t)
		     | _ => (ts, 
			     (IM.empty, IM.empty,
			      T.TSet.singleton v, T.RTSet.empty)))
	      | typ (T.PLAINtys t) = typ (t2ts t)
	      | typ (T.CONtys (tyc, tsl, rtsl, r)) =
		  let val (tsl', mt) = list typ tsl
		      val (rtsl', mrt) = list rtyp0 rtsl
		  in (T.CONtys (tyc, tsl', rtsl', r), join (mt, mrt))
		  end
	      | typ (T.MUtys (v, ts, r)) =
		  let val (ts', (btvm, brvm, ftvs, frvs)) = typ ts
		      val btvm' =
			  case IM.find (btvm, v) of
			      SOME i => IM.insert (btvm, v, i+1)
			    | NONE => btvm
		  in (T.MUtys (v, ts', r), (btvm', brvm, ftvs, frvs))
		  end
	      | typ (ts as T.REFtys v) =
		  (ts, (IM.singleton (v, 1), IM.empty,
			T.TSet.empty, T.RTSet.empty))

	    and rtyp (rts as T.VARrtys rv, ls) =
		  (rts, (IM.empty, IM.empty,
			 T.TSet.empty, T.RTSet.singleton rv))
	      | rtyp (rts as T.EMPTYrtys _, _) =
		  (rts, (IM.empty, IM.empty, T.TSet.empty, T.RTSet.empty))
	      | rtyp (T.FIELDrtys ((l, (ts, r)), rts), ls) =
		  let val (ts', fm) = typ ts
		      val (rts', rm) = rtyp (rts, LS.add (ls, l))
		  in (T.FIELDrtys ((l, (ts', r)), rts'), join (fm, rm))
		  end
	      | rtyp (rts as T.REFrtys v, ls) =
		  (rts, (IM.empty, IM.singleton (v, (1, ls)),
			 T.TSet.empty, T.RTSet.empty))

	    and rtyp0 rts = rtyp (rts, LS.empty)

	in typ body
	end


    fun mkPrinter () =
	let val bnames = ["a", "b", "c", "d", "e", "f", "g", "h", "i",
			  "j", "k", "l", "m", "n", "o", "p", "q", "r",
			  "s", "t", "u", "v", "w", "x", "y", "z"]
	    val fnames = ["A", "B", "C", "D", "E", "F", "G", "H", "I",
			  "J", "K", "L", "M", "N", "O", "P", "Q", "R",
			  "S", "T", "U", "V", "W", "X", "Y", "Z"]
	    val ftnames = ref fnames
	    val frnames = ref fnames

	    val btnames = ref bnames
	    val brnames = ref bnames

	    val ftm = ref T.TMap.empty
	    val frm = ref T.RTMap.empty

	    fun resetbound () = (btnames := bnames; brnames := bnames)

	    fun isTuple fl =
		let fun loop ([], _) = true
		      | loop ((RL.NUMlab l, _) :: fl, i) =
			      l = i andalso loop (fl, i+1)
		      | loop _ = false
		in loop (fl, 1)
		end

	    fun nextname what prefix supply () =
		case !supply of
		    [] => "?"
		  | h :: t => let val h' = prefix ^ h in supply := t; h' end

	    val nextbtname = nextname "bound type" "'" btnames
	    val nextbrname_nolen = nextname "bound row" "''" brnames
	    val nextbrname_len = nextname "bound row" "'~" brnames
	    val nextftname = nextname "free type" "'" ftnames
	    val nextfrname = nextname "free row" "''" frnames

	    fun nextbrname needlen =
		if needlen then nextbrname_len ()
		else nextbrname_nolen ()

	    fun typschema { targs, rargs, body } =
		let val (body, (btinfo, brinfo, ftinfo, frinfo)) =
			printinfo body

		    val btstrings =
			IM.map (fn cnt =>
				   if cnt > 1 then nextbtname () else "_")
			       btinfo
		    val ftstrings =
			T.TSet.foldl (fn (v, m) =>
					 T.TMap.insert (m, v, nextftname ()))
				     T.TMap.empty
				     ftinfo
		    val frstrings =
			T.RTSet.foldl (fn (rv, m) =>
					  T.RTMap.insert (m, rv, nextfrname ()))
				      T.RTMap.empty
				      frinfo

		    fun rarg (k, (i, m, sl)) =
			let val excluded = k
			    val excluded = RL.map2set excluded
			    val needlen = RL.Set.member (excluded, RL.LENlab)
			    val excluded =
				if needlen then
				    RL.Set.delete (excluded, RL.LENlab)
				else excluded
			    val (cnt, seen) =
				case IM.find (brinfo, i) of
				    NONE => (0, LS.empty)
				  | SOME (cnt, ls) => (cnt, ls)
			    val toexclude = LS.difference (excluded, seen)
			    fun exclusion () =
				case LS.listItems toexclude of
				    [] => ""
				  | [l] => "::" ^ RL.toString l
				  | h :: t =>
				      concat ("::(" :: RL.toString h ::
					      foldr (fn (l, a) =>
							"," :: RL.toString l :: a)
						    [")"]
						    t)
					      
			    fun prefix n = n ^ exclusion ()

			in if needlen orelse not (LS.isEmpty toexclude) then
			       let val n = nextbrname needlen
				   val sl' =
				       if LS.isEmpty toexclude then sl
				       else prefix n :: sl
			       in (i+1, IM.insert (m, i, n), sl')
			       end
			   else if cnt > 1 then
			       (i+1,
				IM.insert (m, i, nextbrname needlen),
				sl)
			   else (i+1, IM.insert (m, i, ""), sl)
			end

		    val (_, brstrings, rrprefix) =
			foldl rarg (0, IM.empty, []) rargs

		    (* loa: left-of-arrow flag *)
		    fun typ (T.PLAINtys (T.VARty v), loa) =
			  (case T.TMap.find (ftstrings, v) of
			       NONE => bug "unexpected VARty"
			     | SOME s => s)
		      | typ (T.PLAINtys t, loa) =
			  bug "unexpected PLAINtys"
		      | typ (T.CONtys (tyc, tl, rtl, _), loa) =
			  conty (tyc, tl, rtl, loa)
		      | typ (T.MUtys (i, ts, _), loa) = mutyp (i, ts, loa)
		      | typ (T.REFtys i, loa) =
			  (case IM.find (btstrings, i) of
			       NONE => bug "unexpected REFtys"
			     | SOME s => s)

		    and conty (T.INTtyc, [], [], _) = "int"
		      | conty (T.BOOLtyc, [], [], _) = "bool"
		      | conty (T.STRINGtyc, [], [], _) = "string"
		      | conty (T.FUNtyc, [t1, t2], [erts], loa) =
			  (* TODO: handle printing of exception row type *)
			  let val (lb, rb) = if loa then ("(", ")")
					     else ("", "")
			  in concat [lb, typ (t1, true),
				     funarrow erts,
				     typ (t2, false), rb]
			  end
		      | conty (T.MATCHtyc, [ts], [rts, erts], loa) =
			  concat ["(", styp rts,
				  matcharrow erts,
				  typ (ts, false), ")"]
		      | conty (T.LISTtyc, [t], [], _) =
			  "[" ^ typ (t, false) ^ "]"
		      | conty (T.RECORDtyc p, [], [rts], _) =
			  rtyp (p, rts)
		      | conty (T.SUMtyc, [], [rts], _) =
			  styp rts
		      | conty _ = bug "ill-formed CONtys`"

		    and rtyp (Purity.Pure, rts) =
			  rowtype (rts, "{ ", " }", ", ... : ", true, NONE)
		      | rtyp (Purity.Impure, rts) =
			  rowtype (rts, "{| ", " |}", ", ... : ", false, NONE)

		    and styp rts =
			rowtype (rts, "<", ">", "; ", false, NONE)

		    and funarrow rts =
			rowtype (rts, " -/", "/-> ", "; ", false, SOME " -> ")

		    and matcharrow rts =
			rowtype (rts, " =/", "/=> ", "; ", false, SOME " => ")

		    and mutyp (i, ts, loa) =
			case IM.find (btstrings, i) of
			    SOME s =>
			      concat ["(", s, " as ", typ (ts, false), ")"]
			  | NONE => typ (ts, loa)

		    and rowtype (rts, lb, rb, rvsep, trytuple, ifunconstr) =
			let fun commas f l = String.concatWith ", " (map f l)
			    fun withrowvar ("", []) =
				  (case ifunconstr of
				       NONE => concat [lb, "...", rb]
				     | SOME uc => uc)
			      | withrowvar ("", fl) =
				  let val fl = RL.sortBy #1 fl
				  in concat [lb, commas field fl, ", ...", rb]
				  end
			      | withrowvar (s, []) = concat [lb, s, rb]
			      | withrowvar (s, fl) =
				  let val fl = RL.sortBy #1 fl
				  in concat [lb, commas field fl, rvsep, s, rb]
				  end
			    and rtyp (T.VARrtys rv, fl) =
				  (case T.RTMap.find (frstrings, rv) of
				       NONE => bug "unexpected VARtys"
				     | SOME s => withrowvar (s, fl))
			      | rtyp (T.EMPTYrtys _, fl) =
				  let val fl = RL.sortBy #1 fl
				  in if trytuple andalso isTuple fl then
					 concat ["(", commas tfield fl, ")"]
				     else concat [lb, commas field fl, rb]
				  end
			      | rtyp (T.FIELDrtys (f, rts), fl) =
				  rtyp (rts, f :: fl)
			      | rtyp (T.REFrtys i, fl) =
				  (case IM.find (brstrings, i) of
				       NONE => bug "unexpected REFrtys"
				     | SOME s => withrowvar (s, fl))

			    and field (l, (t, _)) =
				concat [RL.toString l, ": ", typ (t, false)]

			    and tfield (_, (t, _)) = typ (t, false)
			in rtyp (rts, [])
			end

		    val _ = resetbound ()
		    val b = typ (body, false)
		in case rrprefix of
		       [] => b
		     | _ => concat ("\\ " ::
				    List.revAppend (rrprefix, [" . ", b]))
		end
	in typschema
	end

    fun mkRecordTyp (fl, r) =
	let fun one (n, t, r) = (RecordLabel.SYMlab (Symbol.atom n), (t, r))
	in T.RECORDty (Purity.Pure,
		       foldr T.FIELDrty (T.EMPTYrty r)
			     (RecordLabel.sortBy #1 (map one fl)),
		       r)
	end

    fun tyc2string T.INTtyc = "int"
      | tyc2string T.BOOLtyc = "bool"
      | tyc2string T.STRINGtyc = "string"
      | tyc2string T.FUNtyc = "(...->...)"
      | tyc2string T.MATCHtyc = "(...=>...)"
      | tyc2string T.LISTtyc = "[...]"
      | tyc2string (T.RECORDtyc Purity.Pure) = "{...}"
      | tyc2string (T.RECORDtyc Purity.Impure) = "{|...|}"
      | tyc2string T.SUMtyc = "<...>"

    fun type2string (T.VARty v) =
	  (case TVar.tget v of
	       T.INST t => type2string t
	     | T.OPEN _ => "?")
      | type2string (T.CONty (tyc, _, _, _)) = tyc2string tyc
end
