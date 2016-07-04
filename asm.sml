(* asm.sml
 *
 *   Generic machine instruction.
 *   This module is based on Andrew Appel's book
 *   "Modern Compiler Implementation in ML"
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Asm = struct

    type reg = string
    type temp = LVar.lvar
    type label = Label.label

    datatype jumpinfo =
	RETURN			(* instruction ends current function *)
      | JUMP of label list	(* instruction jumps to one of the labels *)
      | NOJUMP			(* instruction falls through (no jump) *)

    datatype instr =
	OPER of { asm : string,	   (* template string *)
		  dst : temp list, (* all temps defined by this operation *)
		  src : temp list, (* all temps used by this operation *)
		  jmp : jumpinfo }
      | LABEL of label
      | MOVE of { asm : string,	(* template string *)
		  dst : temp,	(* destination of move *)
		  src : temp }	(* source of move *)
      | REGSAVE	        (* runs AFTER the stack frame has been created *)
      | REGRESTORE	(* runs BEFORE the stack frame has been deleted *)
      | NOSTACK			(* marks point where stack is not usable *)

    (* The template string must refer to source temps
     * using the `sN syntax (where N is the position of
     * the temp in the src list of OPER or 0 in the case of MOVE).
     * Numbering is 0-based: the first source temp is `s0, the second `s1
     * and so on.
     * Likewise, destination temps must be referred to using `dN.
     * For convenience, in the case of OPER one can refer to a label
     * name that appears in the jump info using `jN.
     *
     * Given a function for mapping temps to the name (a string) of
     * their respective machine register, the following function
     * formats instructions for output in an assembly code file: *)
    fun format (saytemp, regsave, regrestore) = let
	val oz = Char.ord #"0"
	fun dig c = Char.ord c - oz
	fun nth (l, c) = List.nth (l, dig c)
	val saylab = Label.escname
	fun out (asm, dst, src, jmp) = let
	    fun elem (#"s", i) = saytemp (nth (src, i))
	      | elem (#"d", i) = saytemp (nth (dst, i))
	      | elem (#"j", i) = saylab (nth (jmp, i))
	      | elem _ = ErrorMsg.impossible "Asm: bad Asm format"
	    fun f (#"`" :: l :: i :: rest) =
		  String.explode (elem (l, i)) @ f rest
	      | f (c :: rest) = c :: f rest
	      | f [] = []
	in
	    String.implode (f (explode asm))
	end
    in fn OPER { asm, dst, src, jmp } =>
	    let val ll = case jmp of JUMP ll => ll | _ => []
	    in ["\t" ^ out (asm, dst, src, ll)]
	    end
        | LABEL lab =>
	    [saylab lab ^ ":"]
	| MOVE { asm, dst, src } => 
	    ["\t" ^ out (asm, [dst], [src], [])]
	| REGSAVE => regsave
	| REGRESTORE => regrestore
	| NOSTACK => ["\t; nostack"]
    end

end
