(* frame.sml
 *
 *   Information about PowerPC registers and stack frames.
 *   There is one frame per cluster.  The layout of these
 *   frames and register conventions are compatible with
 *   the Mach-O conventions used by Apple's Mac OS X operating
 *   system.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Frame = struct

    datatype frame =
	FRAME of { argAreaTop : int ref, (* keep track of largest call *)
		   nextSpill : int ref,	 (* keep track of all spills *)
		   szName : string,
		   spillName : string
		 }

    type register = int
    type allocation = register LVar.Map.map

    fun showTemp allocation t =
	case LVar.Map.find (allocation, t) of
	    SOME n => "r" ^ Int.toString n
	  | NONE => LVar.toString t

    local fun s i = LVar.special (i, "r" ^ Int.toString i)
	  fun s8 i = (s i, s (i + 1), s (i + 2), s (i + 3),
		      s (i + 4), s (i + 5), s (i + 6), s (i + 7))
    in
        (* temporaries representing all physical registers *)
        val (r0, r1, r2, r3, r4, r5, r6, r7) = s8 0
        val (r8, r9, r10, r11, r12, r13, r14, r15) = s8 8
        val (r16, r17, r18, r19, r20, r21, r22, r23) = s8 16
        val (r24, r25, r26, r27, r28, r29, r30, r31) = s8 24
    end

    val boguscolor = ~1
    val sp = r1				(* stack pointer *)
    val indirfunptr = r12		(* function ptr for indirect calls *)
    val untagscratch = r12		(* Scratch register for holding
					 * untagged (GC-unsafe) ints
					 * temporarily.  These values must
					 * not be spilled or otherwise
					 * be stored on the stack or in the
					 * heap. *)
    val arg1 = r3			(* first argument register *)
    (* temporaries representing caller-save, callee-save, and argument-regs *)
    val callersaves = [r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
    val calleesaves = [r15, r16, r17, r18, r19, r20, r21, r22, r23, r24,
		       r25, r26, r27, r28, r29, r30, r31]
    val args = [r3, r4, r5, r6, r7, r8, r9, r10]
    val nargs = length args
    val results = args		(* function result registers *)
    val nresults = length results

    val allocptr = r13
    val limitptr = r14

    val specialVars = [sp, allocptr, limitptr]

    (* the initial coloring (or "precoloring") which maps temporaries
     * representing physical registers to their respective hard-wired
     * color *)
    val precoloring =
	ListPair.foldl
	    (fn (t, r, m) => LVar.Map.insert (m, t, r))
	    LVar.Map.empty
	    ([r0, r1, r2, r3, r4, r5, r6, r7,
	      r8, r9, r10, r11, r12, r13, r14, r15,
	      r16, r17, r18, r19, r20, r21, r22, r23,
	      r24, r25, r26, r27, r28, r29, r30, r31],
	     [0, 1, 2, 3, 4, 5, 6, 7,
	      8, 9, 10, 11, 12, 13, 14, 15,
	      16, 17, 18, 19, 20, 21, 22, 23,
	      24, 25, 26, 27, 28, 29, 30, 31])

    local
	fun t2r t = valOf (LVar.Map.find (precoloring, t))
    in
        (* registers corresponding to "callersaves" and "calleesaves" *)
        val callersaveRegs = map t2r callersaves
	val calleesaveRegs = rev (map t2r calleesaves)
	val specialRegs = map t2r specialVars
	(* all registers available for coloring *)
	val registers = callersaveRegs @ calleesaveRegs @ specialRegs
    end

    (* offset of argument area from stack pointer *)
    val argAreaBottom = 24

    (* keep track of largest call, adjust argAreaTop accordingly *)
    fun recordArgAreaTop (FRAME { argAreaTop, ... }, t) =
	if t > !argAreaTop then argAreaTop := t else ()

    fun frameSzName (FRAME f) = #szName f
    fun frameSpillName (FRAME f) = #spillName f

    fun hasSpills (FRAME { nextSpill, ... }) = !nextSpill <> 0

    fun new l =
	let val szl = Label.external (Label.name l ^ "_FRAMESIZE")
	    val spl = Label.external (Label.name l ^ "_SPILL")
	in FRAME { argAreaTop = ref argAreaBottom,
		   nextSpill = ref 0,
		   szName = Label.escname szl,
		   spillName = Label.escname spl }
	end

    val gclab = Label.external "mlpr_gc"
    val gcstublab = Label.external "mlpr_gc_stub"
    val gcstublabname = Label.escname gcstublab

    (* allocate slot in stack frame for a spilled temporary *)
    fun allocSpill (FRAME { nextSpill, ... }) =
	let val off = !nextSpill + 4
	in nextSpill := off;
	   off
	end

    fun spillOff (FRAME { spillName, ... }) off =
	concat [spillName, "-", Int.toString off]

    fun regSaveRestoreInfo (FRAME f, allocation) =
	let fun one (t, i, min) =
		if not (LVar.Map.inDomain (precoloring, t))
		   andalso i >= 15 andalso i < min
		then i
		else min
	    val low = LVar.Map.foldli one 32 allocation
	    val sz_lower = !(#argAreaTop f)
	    val n_regsave = 32 - low
	    val sz_regsave = n_regsave * 4
	    val sz_spills = !(#nextSpill f)
	    val sz_upper = sz_regsave + sz_spills
	    val sz_unpadded = sz_lower + sz_upper
	    val sz =
		case sz_unpadded mod 16 of
		    0 => sz_unpadded
		  | odd => sz_unpadded + 16 - odd
	    (* Spill locations on the stack get initialized so that
	     * they do not contain random stuff which would confuse
	     * the GC: *)
	    val spillinit =
		if hasSpills (FRAME f) then
		    let fun loop (i, a) =
			    if i > 0 then
				loop (i-4, concat ["\tstw r0,",
						   #spillName f, "-",
						   Int.toString i,
						   "(r1)"]
					   :: a)
			    else a
		    in "\tli r0,0" :: loop (sz_spills, [])
		    end
		else []
	    val (stmw, lmw) =
		if sz_regsave > 0 then
		    let val tail =
			    concat [" r", Int.toString low, ",",
				    #szName f, "-",
				    Int.toString sz_regsave, "(r1)"]
		    in
			(["\tstmw" ^ tail], ["\tlmw" ^ tail])
		    end
		else ([], [])
	in { save = spillinit @ stmw, restore = lmw,
	     size = sz, sz_regsave = sz_regsave, sz_upper = sz_upper }
	end
end
