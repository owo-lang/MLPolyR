(* anf.sml
 *
 *   The ANF intermediate language of the MLPolyR compiler.
 *   (ANF = Lambda Calculus in A-Normal Form)
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure ANF = struct

    type lvar = LVar.lvar

    datatype value = datatype Lambda.value

    datatype exp =
	VALUES of value list
      | BIND of lvar * value * exp
      | CALL of Purity.purity * lvar list * app * exp
      | FIX of function list * exp
      | ARITH of Oper.arithop * value * value * lvar * exp
      | RECORD of Purity.purity * value * slice list * lvar * exp
      | SELECT of value * value * Purity.purity * lvar * exp
      | UPDATE of value * value * value * exp
      | CMP of Oper.cmpop * value * value * exp * exp
      | JUMP of Purity.purity * app
      | GETSP of lvar * exp
      | SETSP of value * exp
      | MAYJUMP of lvar * exp
    and slice =
	SGT of value
      | SEQ of { base: value, start: value, stop: value }
    withtype function = { f : lvar * lvar list * exp, inl: bool, hdlr: bool }
	 and app = value * value list
end
