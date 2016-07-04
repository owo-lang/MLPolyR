(* closed.sml
 *
 *   This module describes the "Closed ANF" intermediate language
 *   which is the output of MLPolyR's closure conversion.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Closed = struct

    type lvar = LVar.lvar
    type label = Label.label
    datatype value = datatype Lambda.value

    datatype exp =
	VALUES of value list
      | BIND of lvar * value * exp
      | CALL of Purity.purity * lvar list * jtarget * exp
      | ARITH of Oper.arithop * value * value * lvar * exp
      | RECORD of Purity.purity * value * slice list * lvar * exp
      | SELECT of value * value * Purity.purity * lvar * exp
      | UPDATE of value * value * value * exp
      | CMP of Oper.cmpop * value * value * btarget * btarget
      | JUMP of jtarget
      | GETSP of lvar * exp
      | SETSP of value * exp
      | MAYJUMP of label * exp
    and slice =
	SGT of value
      | SEQ of { base: value, start: value, stop: value }
    withtype jtarget = value * value list
	 and btarget = label * value list

    type block = label * lvar list * exp
    type entryblock = label * lvar list * exp * bool
    (* true: exception handler entry point *)

    type program = { calltargets: entryblock list,
		     jumptargets: block list,
		     entrypoint: entryblock }

    type cluster = { entryblocks: entryblock list, labelblocks: block list }
end
