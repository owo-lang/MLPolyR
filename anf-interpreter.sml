(* anf-interpreter.sml
 *
 *   A simple meta-circular interpreter for MLPolyR's
 *   ANF intermediate language.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure ANFInterpreter : sig

    datatype value =
	INTv of LiteralData.integer
      | RECv of recfields
      | FUNv of cont -> value list -> value list
    withtype recfields = value ref list
	 and cont = value list -> value list

    val eval : (Label.label -> value) -> ANF.exp -> value list

end = struct

    structure A = ANF

    datatype value =
	INTv of LiteralData.integer
      | RECv of recfields
      | FUNv of cont -> value list -> value list
    withtype recfields = value ref list
	 and cont = value list -> value list

    fun vINT (INTv i) = i 
      | vINT _ = raise Fail "integer required"
    fun vREC (RECv xrl) = xrl
      | vREC _ = raise Fail "record required"
    fun vFUN (FUNv f) = f
      | vFUN _ = raise Fail "function required"

    fun tuple xl = RECv (map ref xl)

    fun bind (v: LVar.lvar, x, env) v' = if v = v' then x else env v'

    fun bindl (vl, xl, env) = ListPair.foldl bind env (vl, xl)

    fun recidx i = LiteralData.toInt (i div MachSpec.wordSize)

    fun eval labenv e =
	let fun value env (A.VAR v) = env v
	      | value _ (A.LABEL l) = labenv l
	      | value _ (A.INT i) = INTv i
	    fun apply ((x, xl), env, k) =
		vFUN (value env x) k (map (value env) xl)
	    fun exp (A.VALUES xl, env, k) =
		k (map (value env) xl)
	      | exp (A.BIND (v, x, e), env, k) =
		  exp (e, bind (v, value env x, env), k)
	      | exp (A.CALL (_, vl, a, e), env, k) =
		  apply (a, env, fn xl => exp (e, bindl (vl, xl, env), k))
	      | exp (A.FIX (fl, e), env, k) =
		  let fun env' v0 =
			  case List.find (fn f => #1 (#f f) = v0) fl of
			      SOME { f = (f, vl, e), ... } =>
			        FUNv (fn k' => fn xl =>
				           exp (e, bindl (vl, xl, env'), k'))
			    | NONE => env v0
		  in exp (e, env', k)
		  end
	      | exp (A.ARITH (aop, x, y, v, e), env, k) =
		  exp (e, bind (v, INTv (Oper.doarith (aop,
						       vINT (value env x),
						       vINT (value env y))),
				env),
		       k)
	      | exp (A.RECORD (_, _, sl, v, e), env, k) =
		  let fun build [] = []
			| build (A.SGT x :: sl) = value env x :: build sl
			| build (A.SEQ { base, start, stop } :: sl) =
			    let val br = vREC (value env base)
				val s = vINT (value env start)
				val e = vINT (value env stop)
				fun grow i =
				    if i >= e then build sl
				    else !(List.nth (br, recidx i)) ::
					 grow (i+MachSpec.wordSize)
			    in grow s
			    end
		  in exp (e, bind (v, tuple (build sl), env), k)
		  end
	      | exp (A.SELECT (x, y, _, v, e), env, k) =
		  exp (e, bind (v, !(List.nth (vREC (value env x),
					       recidx (vINT (value env y)))),
				env),
		       k)
	      | exp (A.UPDATE (x, y, z, e), env, k) =
		  (List.nth (vREC (value env x), recidx (vINT (value env y)))
		        := value env z;
		   exp (e, env, k))
	      | exp (A.CMP (cop, x, y, et, ee), env, k) =
		  if Oper.docmp (cop, vINT (value env x), vINT (value env y))
		  then exp (et, env, k)
		  else exp (ee, env, k)
	      | exp (A.JUMP (_, a), env, k) =
		  apply (a, env, k)
	      | exp (A.GETSP (v, e), env, k) =
		  exp (e, bind (v, FUNv (fn _ => k), env), k)
	      | exp (A.SETSP (x, e), env, k) =
		  exp (e, env, vFUN (value env x) k)
	      | exp (A.MAYJUMP (_, e), env, k) =
		  exp (e, env, k)
	in exp (e, fn _ => raise Fail "unbound variable", fn xl => xl)
	end
end
