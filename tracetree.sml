(* tracetree.sml
 *
 *   Basic blocks with trees arranged into "traces".
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure TraceTree = struct

    type temp = LVar.lvar
    type label = Label.label

    datatype exp = datatype BBTree.exp
    datatype lexp = datatype BBTree.lexp

    datatype trace =
	LABEL of labtrace	(* labeled trace *)
      | JUMP of label * newstart (* unconditional jump followed by
				  * unrelated code *)
      | TCALL of exp * exp list * newstart (* tail call followed by
					    * unrelated code *)
      | RETURN of exp list * newstart (* function return followed by
				  * unrelated code *)
      | CJUMP of TreeOps.relop * exp * exp * label * labtrace
                                 (* conditional jump (if condition true),
				  * fall through to labeled trace when false*)
      | CALL of lexp list * exp * exp list * trace (* call w/ multi-result *)
      | MOVE of lexp * exp * trace (* assignment followed by trace *)
      | DOEXP of exp * trace	     (* eval. for effect, followed by trace *)
      | DOCALL of exp * exp list * trace (* eval call for effect *)
      | GCTEST of exp * trace	     (* make sure there is space available *)
      | ALLOCWRITE of exp * trace    (* allocate one word *)
      | ALLOCCOPY of exp * exp * trace (* allocate a sequence of words
					* by copying *)

    and newstart =
	END			(* no more code *)
      | JTARGET of labtrace	(* a target for a jump *)
      | ENTRY of entrytrace     (* a function entry point *)

    withtype labtrace = label * trace

    and entrytrace = temp list * labtrace * bool (* true: exn hdlr *)
end
