structure CPS = struct

    datatype 'body value =
	CONST of int
      | VAR of int
      | LAM of int list * 'body

    datatype ('arg, 'body) exp =
	VALUE of 'body value
      | APP of 'arg * 'arg list

    datatype lexp = L of (lexp, lexp) exp

    datatype cexp = C of (cexp value, cexp) exp

    fun convert e =
	let val n = ref 1000
	    fun withnew f = let val i = !n in n := i+1; f i end

	    fun value_cvt (x, k) =
		case x of
		    CONST i => k (CONST i)
		  | VAR v => k (VAR v)
		  | LAM (vl, e) =>
		      withnew (fn kv => k (LAM (kv :: vl, tail_cvt (e, kv))))

	    and cvt (L e, k) =
		case e of
		    APP (e, el) =>
		      withnew (fn v => app_cvt (e, el, LAM ([v], k (VAR v))))
		  | VALUE e => value_cvt (e, fn x => C (VALUE x))

	    and tail_cvt (L e, kv) =
		case e of
		    APP (e, el) => app_cvt (e, el, VAR kv)
		  | VALUE e => value_cvt (e, fn x => C (APP (VAR kv, [x])))

	    and app_cvt (e, el, kx) =
		cvt (e, fn x => list_cvt (el, fn xl => C (APP (x, kx :: xl))))

	    and list_cvt (el, k) =
		case el of
		    [] => k []
		  | h :: t =>
		      cvt (h, fn vh => list_cvt (t, fn vt => k (vh :: vt)))
	in withnew (fn k0v => LAM ([k0v], tail_cvt (e, k0v)))
	end
end
