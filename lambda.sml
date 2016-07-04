(* lambda.sml
 *
 *   The Lambda intermediate language of the MLPolyR compiler.
 *   Lambda is the output of the Translate phase.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Lambda = struct

    type lvar = LVar.lvar
    type purity = Purity.purity

    datatype value =
	VAR of lvar
      | LABEL of Label.label
      | INT of LiteralData.integer

    datatype exp =
        VALUE of value
      | LET of lvar * exp * exp
      | FIX of function list * exp
      | ARITH of Oper.arithop * exp * exp
      | RECORD of { purity: purity, len: exp, slices: slice list }
      | SELECT of exp * exp * purity
      | UPDATE of exp * exp * exp
      | CMP of Oper.cmpop * exp * exp * exp * exp
      | APP of purity * exp * exp list
      | HANDLER of lvar * lvar list * exp * exp
    and slice =
	SGT of exp
      | SEQ of { base: exp, start: exp, stop: exp }
    (* the boolean flag, when set to true, is a strong
     * hint to have this function inlined *)
    withtype function = lvar * lvar list * exp * bool
end
