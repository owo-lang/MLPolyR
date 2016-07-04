(* rewrite.sml
 *
 *   Instruction rewriting (to account for spills produced by the
 *   register allocator).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Rewrite : sig

    val rewrite : Frame.frame * LVar.lvar list ->
		  Asm.instr * Asm.instr list -> Asm.instr list

end = struct

    structure M = LVar.Map
    structure A = Asm

      (* Given the frame data structure for the current cluster and
       * a list of spilled lvars, construct function that
       * maps an instruction to an equivalent list of instructions
       * that implement spilling.  The constructed function
       * also takes the "remaining" instructions as an argument
       * so that it can be used in a "fold": *)
    fun rewrite (frame, spills) = let
	(* figure out stack offsets for the spills: *)
	val offsetmap =
	    foldl (fn (t, m) => M.insert (m, t, Frame.allocSpill frame))
		  M.empty spills

	fun offset t = Option.map (Frame.spillOff frame) (M.find (offsetmap, t))

	(* storing into the stack frame *)
	fun store (tmp, off) =
	    A.OPER { asm = concat ["\tstw `s0,", off, "(`s1)"],
		     src = [tmp, Frame.sp], dst = [], jmp = A.NOJUMP }

	(* loading from the stack frame *)
	fun load (tmp, off) =
	    A.OPER { asm = concat ["\tlwz `d0,", off, "(`s0)"],
		     src = [Frame.sp], dst = [tmp], jmp = A.NOJUMP }

	(* utility functions for dealing with spilled destinations
	 * and sources: *)
	fun spillDst dst =
	    case offset dst of
		NONE => (dst, [])
	      | SOME off =>
		  let val t = LVar.clone dst
		  in (t, [store (t, off)])
		  end

	fun spillDst' (dst, (rl, il)) =
	    let val (dst', il') = spillDst dst
	    in (dst' :: rl, il' @ il)
	    end

	fun spillSrc src =
	    case offset src of
		NONE => (src, [])
	      | SOME off =>
		  let val t = LVar.clone src
		  in (t, [load (t, off)])
		  end

	fun spillSrc' (src, (rl, il)) =
	    let val (src', il') = spillSrc src
	    in
		(src' :: rl, il' @ il)
	    end

	(* do it for one instruction: *)
	fun rw (i as (A.LABEL _ |
		      A.REGSAVE |
		      A.REGRESTORE |
		      A.NOSTACK), il) = i :: il
	  | rw (A.MOVE { src, dst, asm }, il) =
	      let val (src', il1) = spillSrc src
		  val (dst', il2) = spillDst dst
	      in il1 @ A.MOVE { src = src', dst = dst', asm = asm } ::
		 il2 @ il
	      end
	  | rw (i as A.OPER { src, dst, asm = a, jmp = j }, il) =
	      let val (src', il1) = foldr spillSrc' ([], []) src
		  val (dst', il2) = foldr spillDst' ([], []) dst
	      in il1 @ A.OPER { asm = a, src = src', dst = dst', jmp = j } ::
		 il2 @ il
	      end
    in rw
    end
end
