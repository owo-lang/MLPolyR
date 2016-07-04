(* bbtree.sml
 *
 *   Basic Block Trees.
 *   (This code is based on Andrew Appel's book "Modern Compiler
 *    Implementation in ML", but it has been modified to capture
 *    the invariants of basic blocks in ML types.)
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure BBTree = struct

    type temp = LVar.lvar
    type label = Label.label

    datatype exp =
	FETCH of lexp
      | BINOP of TreeOps.binop * exp * exp
      | NAME of label
      | CONST of LiteralData.integer

    and lexp =
	MEM of exp
      | TEMP of temp
      | ALLOCPTR
      | STACKPTR

    datatype preblock =
	JUMP of label		(* unconditional jump *)
      | TCALL of exp * exp list	(* tail call *)
      | RETURN of exp list	(* return from function call *)
      | CJUMP of TreeOps.relop * exp * exp * label * label (* conditional j. *)
      | CALL of lexp list * exp * exp list * preblock (* call w/ multi-result *)
      | MOVE of lexp * exp * preblock (* assignment *)
      | DOEXP of exp * preblock (* evaluate expression for effect *)
      | DOCALL of exp * exp list * preblock (* evaluate call for effect *)
      | GCTEST of exp * preblock (* confirm availability of a number of bytes *)
      | ALLOCWRITE of exp * preblock
		   (* allocate one word, bump alloc ptr.
		    *   ALLOCWRITE (e, b) is roughly equivalent to
		    *   MOVE (ALLOCPTR, BINOP (PLUS, FETCH ALLOCPTR, CONST 4),
		    *    MOVE (MEM (FETCH ALLOCPTR), exp,
		    *     preblock))
		    * It is guaranteed to be recognized by the code
		    * generator and turned into a single instruction.
		    *)
      | ALLOCCOPY of exp * exp * preblock
		   (* ALLOCCOPY (frombase, len, b):
		    *    allocate len bytes, bump alloc ptr., copy contents
		    *    from region starting at frombase *)

    type block = label * preblock
    type entryblock = temp list * block * bool
    (* true: exception handler entry point *)

    type cluster = { entryblocks: entryblock list,
		     labelblocks: block list }
end
