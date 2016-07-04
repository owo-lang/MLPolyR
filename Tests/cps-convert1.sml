structure CPS = struct

    datatype lexp =
	LCONST of int
      | LVAR of int
      | LLAM of int list * lexp
      | LAPP of lexp * lexp list

    datatype cvalue =
	CCONST of int
      | CVAR of int
      | CLAM of int list * cexp

    and cexp =
	CVALUE of cvalue
      | CAPP of cvalue * cvalue list

    fun convert e =
	let val n = ref 1000
	    fun withnew f = let val i = !n in n := i+1; f i end

	    fun cvt (e, k) =
		case e of
		    LAPP (e, el) =>
		      withnew (fn v => app_cvt (e, el, CLAM ([v], k (CVAR v))))
		  | LCONST i => k (CCONST i)
		  | LVAR v => k (CVAR v)
		  | LLAM (vl, e) =>
		      withnew (fn kv => k (CLAM (kv :: vl, tail_cvt (e, kv))))

	    and tail_cvt (e, kv) =
		case e of
		    LAPP (e, el) => app_cvt (e, el, CVAR kv)
		  | e => cvt (e, fn x => CAPP (CVAR kv, [x]))

	    and app_cvt (e, el, kx) =
		cvt (e, fn x => list_cvt (el, fn xl => CAPP (x, kx :: xl)))

	    and list_cvt (el, k) =
		case el of
		    [] => k []
		  | h :: t =>
		      cvt (h, fn vh => list_cvt (t, fn vt => k (vh :: vt)))
	in withnew (fn k0v => CLAM ([k0v], tail_cvt (e, k0v)))
	end

end
