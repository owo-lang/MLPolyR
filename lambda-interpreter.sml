(* lambda-interpreter.sml
 *
 *   A meta-circular interpreter of the Lambda language
 *   used by the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure LambdaInterpreter : sig

    datatype value =
	INTv of LiteralData.integer
      | RECv of recfields
      | FUNv of value list -> value list
    withtype recfields = value ref list

    val eval : (Label.label -> value) -> Lambda.exp -> value

end = struct

    structure L = Lambda

    datatype value =
	INTv of LiteralData.integer
      | RECv of recfields
      | FUNv of value list -> value list
    withtype recfields = value ref list

    fun vINT (INTv i) = i 
      | vINT _ = raise Fail "integer required"
    fun vREC (RECv xrl) = xrl
      | vREC _ = raise Fail "record required"
    fun vFUN (FUNv f) xl =
	  (case f xl of
	       [y] => y
	     | _ => ErrorMsg.impossible "LambdaInterpreter: multiple results")
      | vFUN _ _ = raise Fail "function required"

    fun tuple xl = RECv (map ref xl)

    fun bind (v: LVar.lvar, x, env) v' = if v = v' then x else env v'
    fun bindl (vl, xl, env) = ListPair.foldl bind env (vl, xl)

    fun recidx i = LiteralData.toInt (i div MachSpec.wordSize)

    fun eval labenv e =
	let fun value (L.VAR v, env) = env v
	      | value (L.LABEL l, _) = labenv l
	      | value (L.INT i, _) = INTv i
	    fun exp (L.VALUE x, env) =
		  value (x, env)
	      | exp (L.LET (v, e, b), env) =
		  exp (b, bind (v, exp (e, env), env))
	      | exp (L.FIX (fl, b), env) =
		  let fun env' v0 =
			  case List.find (fn (f, _, _, _) => f = v0) fl of
			      SOME (f, vl, e, _) =>
			        FUNv (fn xl  =>
					    [exp (e, bindl (vl, xl, env'))])
			    | NONE => env v0
		  in exp (b, env')
		  end
	      | exp (L.ARITH (aop, e1, e2), env) =
		  INTv (Oper.doarith (aop, vINT (exp (e1, env)),
				              vINT (exp (e2, env))))
	      | exp (L.RECORD { purity, len, slices }, env) =
		  let val _ = exp (len, env) (* for effect *)
		      fun build [] = []
			| build (L.SGT e :: sl) =
			    exp (e, env) :: build sl
			| build (L.SEQ { base, start, stop } :: sl) =
			    let val br = vREC (exp (base, env))
				val s = vINT (exp (start, env))
				val e = vINT (exp (stop, env))
				fun grow i =
				    if i >= e then build sl
				    else !(List.nth (br, recidx i))
					 :: grow (i+MachSpec.wordSize)
			    in grow s
			    end
		  in tuple (build slices)
		  end
	      | exp (L.SELECT (e1, e2, _), env) =
		  let val (erl, i) =
			  (vREC (exp (e1, env)), vINT (exp (e2, env)))
		  in !(List.nth (erl, recidx i))
		  end
	      | exp (L.UPDATE (e1, e2, e3), env) =
		  let val (erl, i, v) =
			  (vREC (exp (e1, env)),
			   vINT (exp (e2, env)),
			   exp (e3, env))
		  in List.nth (erl, recidx i) := v;
		     INTv 0
		  end
	      | exp (L.CMP (cop, e1, e2, et, ee), env) =
		  if Oper.docmp (cop, vINT (exp (e1, env)),
				      vINT (exp (e2, env)))
		  then exp (et, env)
		  else exp (ee, env)
	      | exp (L.APP (_, e, el), env) =
		  vFUN (exp (e, env))
		       (map (fn e => (exp (e, env))) el)
	      | exp (L.HANDLER (hv, hvl, hb, b), env) =
		  let exception E of value list
		  in exp (b, bind (hv, FUNv (fn xl => raise E xl), env))
		     handle E xl => exp (hb, bindl (hvl, xl, env))
		  end
	in exp (e, fn _ => raise Fail "unbound variable")
	end
end
