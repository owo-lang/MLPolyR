(* cg.sml
 *
 * Code generation (instruction selection) for the PowerPC.
 *
 *   A "compilation" is used to keep track of data- and function stubs
 *   for external linkage across multiple methods.  (There cannot be
 *   more than one stub of any kind for a given external name per
 *   compilation unit.)
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure PPCCodeGen :> sig

    (* A "compilation" is used to keep track of data- and function stubs
     * for external linkage across multiple methods.  (There cannot be
     * more than one stub of any kind for a given external name per
     * compilation unit.)  It also remembers if GC might be called
     * so that the corresponding GC stub can be generated. *)
    type compilation

    val new : unit -> compilation

    val codegen : Frame.frame * compilation * TraceTree.entrytrace ->
		  Asm.instr list

    val getstubs : compilation ->
		   { datastubs: string list,
		     funstubs: string list,
		     needgc: bool }

end = struct

    structure T = TraceTree
    structure TO = TreeOps
    structure A = Asm
    structure L = Label
    structure M = L.Map

    fun bug m = ErrorMsg.impossible ("PPCCodeGen: " ^ m)

    type temp = LVar.lvar

    type compilation = { datastubs : string list M.map ref,
			 funstubs : string list M.map ref,
			 needgc : bool ref }

    fun new () : compilation = { datastubs = ref M.empty,
				 funstubs = ref M.empty,
				 needgc = ref false }

    (* We frequently need fresh temps... *)
    fun newtmp () = LVar.new "tmp"

    fun getstubs { datastubs, funstubs, needgc } =
	{ datastubs = M.foldr (op @) [] (!datastubs),
	  funstubs = M.foldr (op @) [] (!funstubs),
	  needgc = !needgc }

    fun codegen (frame, { datastubs, funstubs, needgc }, entry) = let

	(* here we accumulate the list of instructions (in reverse order) *)
	val ilist = ref []

	(* "emit" one instruction *)
	fun emit x = ilist := x :: !ilist

	(* generate stub for data linkage (non-lazy) *)
	fun gendatastub (l, n, n') =
	    if M.inDomain (!datastubs, l) then ()
	    else
		datastubs := M.insert
				 (!datastubs, l,
				  [".non_lazy_symbol_pointer\n",
				   n', ":\n",
				   "\t.indirect_symbol ", n, "\n",
				   "\t.long\t0\n"])

	(* generate stubs for function linkage (lazy) *)
	fun genfunstub (l, n, n_stub, n_lptr) =
	    if M.inDomain (!funstubs, l) then ()
	    else
		(funstubs := M.insert
				 (!funstubs, l,
				  ["\t.align 2\n",
				   n_stub, ":\n",
				   "\t.indirect_symbol ", n, "\n",
				   "\tlis r11,ha16(", n_lptr, ")\n",
				   "\tlwzu r12,lo16(", n_lptr, ")(r11)\n",
				   "\tmtctr r12\n",
				   "\tbctr\n"]);
		 datastubs := M.insert
				  (!datastubs, l,
				   [".lazy_symbol_pointer\n",
				    n_lptr, ":\n",
				    "\t.indirect_symbol ", n, "\n",
				    "\t.long dyld_stub_binding_helper\n"]))

	(* generate GC stub if necessary *)
	fun gengcstub () =
	    if !needgc then ()
	    else
		let val n_gc = L.escname Frame.gclab
		    val n_gc_stub = concat ["L", n_gc, "$stub"]
		    val n_gc_lptr = concat ["L", n_gc, "$lazy_ptr"]
		in needgc := true;
		   genfunstub (Frame.gclab, n_gc, n_gc_stub, n_gc_lptr)
		end

	(* for convenience: emit a "move register" instruction *)
	fun emitMove (dst, src) =
	    emit (A.MOVE { asm = "mr `d0,`s0", dst = dst, src = src })

	(* convert int to corresponding string
	 * (we need to pay attention to the syntax of signed numbers,
	 *  SML syntax is different from that used by the assembler!) *)
	fun i2s i =
	    if i < 0 then "-" ^ LiteralData.toString (~i)
	    else LiteralData.toString i

	(* convert integer literal to corresponding string *)
	fun int2s i =
	    if i < 0 then "-" ^ Int.toString (~i) else Int.toString i

	(* issue instruction(s) to load an immediate value into a temporary *)
	fun const i =
	    let val t =
		    if i mod 2 = 0 then LVar.new "const"
		    else Frame.untagscratch
	    in if i < 0x8000 andalso i >= ~0x8000 then
		   emit (A.OPER { asm = "li `d0," ^ i2s i,
				  dst = [t], src = [], jmp = A.NOJUMP })
	       else
		   let val w = Word32.fromLargeInt (LiteralData.toLarge i)
		       val h = Word32.>> (w, 0w16)
		       val l = Word32.andb (w, 0wxffff)
		   in emit (A.OPER { asm = "lis `d0,0x" ^ Word32.toString h,
				     src = [], dst = [t], jmp = A.NOJUMP });
		      if l <> 0w0 then
			  emit (A.OPER { asm = "ori `d0,`s0,0x" ^
					         Word32.toString l,
					 src = [t], dst = [t],
					 jmp = A.NOJUMP })
		      else ()
		   end;
	       t
	    end

	(* emit instruction for typical binary operation *)
	fun binInst0 (oc, e1, e2, t) =
	    emit (A.OPER { asm = oc ^ " `d0,`s0,`s1",
			   dst = [t], src = [e1, e2], jmp = A.NOJUMP })

	fun binInst (oc, e1, e2) =
	    let val t = newtmp () in binInst0 (oc, e1, e2, t); t end

	(* binary op that produces untagged int *)
	fun binInstU (oc, e1, e2) = binInst0 (oc, e1, e2, Frame.untagscratch)

	(* generic code for issuing instruction that involves a constant *)
	fun gConInst0 (low, high) (oc, altoc, e, i, t) =
	    if i >= low andalso i < high then
		emit (A.OPER { asm = concat [oc, " `d0,`s0,", i2s i],
			       dst = [t], src = [e], jmp = A.NOJUMP })
	    else 
		emit (A.OPER { asm = altoc ^ " `d0,`s0,`s1",
			       dst = [t], src = [e, const i],
			       jmp = A.NOJUMP })

	(* typical binary ops involving 16-bit signed immediates *)
	val conInst0 = gConInst0 (~0x8000, 0x8000)
	(* shift ops where range is [0,32) *)
	val conSInst0 = gConInst0 (0, 32)

	fun conInst (oc, altoc, e, i) =
	    let val t = newtmp () in conInst0 (oc, altoc, e, i, t); t end

	fun conSInst (oc, altoc, e, i) =
	    let val t = newtmp () in conSInst0 (oc, altoc, e, i, t); t end

	fun conSInstU (oc, altoc, e, i) =
	    conSInst0 (oc, altoc, e, i, Frame.untagscratch)

	(* binary ops involving 16-bit unsigned immediates *)
	fun conLInst (oc, altoc, e, i) =
	    let val w = Word32.fromLargeInt (LiteralData.toLarge i)
		val t = newtmp ()
	    in
		if w >= 0wx10000 then
		    emit (A.OPER { asm = altoc ^ " `d0,`s0,`s1",
				   dst = [t], src = [e, const i],
				   jmp = A.NOJUMP })
		else
		    emit (A.OPER { asm = concat [oc, " `d0,`s0,0x",
						 Word32.toString w],
				   dst = [t], src = [e], jmp = A.NOJUMP });
		t
	    end

	fun unboxInt t =
	    (emit (A.OPER { asm = "srawi `d0,`s0,1",
			    src = [t], dst = [Frame.untagscratch],
			    jmp = A.NOJUMP });
	     Frame.untagscratch)

	fun boxInt () =
	    let val t = newtmp ()
	    in emit (A.OPER { asm = "slwi `d0,`s0,1",
			      src = [Frame.untagscratch], dst = [t],
			      jmp = A.NOJUMP });
	       t
	    end

	(* representation of the result of "munchIndex" *)
	datatype memindex =
	    (* optional base register + displacement *)
	    BaseDisp of temp option * LiteralData.integer
	    (* indexed access (addr = sum of two temps) *)
	  | Indexed of temp * temp

	(* maximal munch on expression trees: *)
	fun munchExp (T.FETCH (T.TEMP t)) = t
	  | munchExp (T.FETCH T.ALLOCPTR) = Frame.allocptr
	  | munchExp (T.FETCH T.STACKPTR) =
	      let val t = newtmp () in emitMove (t, Frame.sp); t end
		  
	  | munchExp (T.FETCH (T.MEM (T.NAME l))) =
	    (* contents at address given by label *)
	    let val t = newtmp ()
		val tmp = newtmp ()
		val n = L.escname l
	    in if L.isExternal l then
		   (* external label *)
		   let val n' = concat ["L", n, "$non_lazy_ptr"]
		       val tmp2 = newtmp ()
		   in emit (A.OPER { asm = concat ["lis `d0,ha16(", n', ")"],
				     dst = [tmp], src = [],
				     jmp = A.NOJUMP });
		      emit (A.OPER { asm = concat ["lwz `d0,lo16(", n',
						   ")(`s0)"],
				     dst = [tmp2], src = [tmp],
				     jmp = A.NOJUMP });
		      emit (A.OPER { asm = "lwz `d0,0(`s0)",
				     src = [tmp2], dst = [t],
				     jmp = A.NOJUMP });
		      gendatastub (l, n, n')
		   end
	       else
		   (* local label *)
		   (emit (A.OPER { asm = concat ["lis `d0,ha16(", n, ")"],
				   src = [], dst = [tmp], jmp = A.NOJUMP });
		    emit (A.OPER { asm = concat ["lwz `d0,lo16(", n,
						 ")(`s0)"],
				   src = [tmp], dst = [t],
				   jmp = A.NOJUMP }));
	       t
	    end
	  | munchExp (T.FETCH (T.MEM e)) =
	      (* contents at address given by arbitrary expression *)
	      let val t = newtmp ()
		  fun off i = i2s (i-1)
	      in case munchIndex e of
		     BaseDisp (SOME base, disp) =>
		       emit (A.OPER { asm =
				        concat ["lwz `d0,", off disp, "(`s0)"],
				      src = [base], dst = [t],
				      jmp = A.NOJUMP })
		   | BaseDisp (NONE, disp) =>
		       emit (A.OPER { asm =
				        concat ["lwz `d0,", off disp, "(0)"],
				      src = [], dst = [t],
				      jmp = A.NOJUMP })
		   | Indexed (t1, t2) =>
		       let val t' = newtmp ()
		       in emit (A.OPER { asm = "add `d0,`s0,`s1",
					 src = [t1, t2], dst = [t'],
					 jmp = A.NOJUMP });
			  emit (A.OPER { asm = "lwz `d0,-1(`s0)",
					 src = [t'], dst = [t],
					 jmp = A.NOJUMP })
		       end;
		 t
	      end
	  | munchExp (T.NAME l) =
	    (* address of a label *)
	    let val tmp = newtmp ()
		val t = newtmp ()
		val n = L.escname l
	    in
		if L.isExternal l then
		    (* external label *)
		    let val n' = concat ["L", n, "$non_lazy_ptr"]
		    in
			emit (A.OPER { asm = concat ["lis `d0,ha16(", n', ")"],
				       dst = [tmp], src = [],
				       jmp = A.NOJUMP });
			emit (A.OPER { asm = concat ["lwz `d0,lo16(", n',
						     ")(`s0)"],
				       dst = [t], src = [tmp],
				       jmp = A.NOJUMP });
			gendatastub (l, n, n')
		    end
		else
		    (emit (A.OPER { asm = concat ["lis `d0,ha16(", n, ")"],
				    src = [], dst = [tmp], jmp = A.NOJUMP });
		     emit (A.OPER { asm = concat ["la `d0,lo16(", n,
						  ")(`s0)"],
				     dst = [t], src = [tmp], jmp = A.NOJUMP }));
		t
	    end
	  | munchExp (T.CONST i) = const i (* value of a constant *)

	  | munchExp (T.BINOP (TO.PLUS, T.CONST i, e) |
		      T.BINOP (TO.PLUS, e, T.CONST i)) =
	      conInst ("addi", "add", munchExp e, i)
	  | munchExp (T.BINOP (TO.PLUS, e1, e2)) =
	      binInst ("add", munchExp e1, munchExp e2)
	  | munchExp (T.BINOP (TO.MINUS, T.CONST i, e)) =
	      conInst ("subfic", "subf", munchExp e, i)
	  | munchExp (T.BINOP (TO.MINUS, e, T.CONST i)) =
	      conInst ("addi", "add", munchExp e, ~i)
	  | munchExp (T.BINOP (TO.MINUS, e1, e2)) =
	      binInst { 1 = "subf", 3 = munchExp e1, 2 = munchExp e2 }
	  | munchExp (T.BINOP (TO.MUL, e, T.CONST i) |
	              T.BINOP (TO.MUL, T.CONST i, e)) =
	      conInst ("mulli", "mullw", munchExp e, i div 2)
	  | munchExp (T.BINOP (TO.MUL, e1, e2)) =
	      binInst ("mullw", munchExp e1, unboxInt (munchExp e2))
	  | munchExp (T.BINOP (TO.DIV, e1, e2)) =
	      (* don't worry about constant operands for now;
	       * also: what should we do about division by zero?
	       * Notice that this implements round-to-0 semantics! *)
	      (binInstU ("divw", munchExp e1, munchExp e2);
	       boxInt ())
	  | munchExp (T.BINOP (TO.MOD, e1, e2)) =
	      (* Again, using round-to-0 semantics... *)
	      let val a = munchExp e1
		  val b = munchExp e2
		  val q = binInst ("divw", a, b)
		  val (p, r) = (newtmp (), newtmp ())
	      in emit (A.OPER { asm = "mullw `d0,`s0,`s1",
				src = [b, q], dst = [p], jmp = A.NOJUMP });
		 emit (A.OPER { asm = "subf `d0,`s0,`s1",
				src = [p, a], dst = [r], jmp = A.NOJUMP });
		 r
	      end
	  | munchExp (T.BINOP (TO.AND, T.CONST i, e) |
		      T.BINOP (TO.AND, e, T.CONST i)) =
	      conLInst ("andi", "and", munchExp e, i)
	  | munchExp (T.BINOP (TO.AND, e1, e2)) =
	      binInst ("and", munchExp e1, munchExp e2)
	  | munchExp (T.BINOP (TO.OR, T.CONST i, e) |
		      T.BINOP (TO.OR, e, T.CONST i)) =
	      conLInst ("ori", "or", munchExp e, i)
	  | munchExp (T.BINOP (TO.OR, e1, e2)) =
	      binInst ("or", munchExp e1, munchExp e2)
	  | munchExp (T.BINOP (TO.LSHIFT, e, T.CONST i)) =
	      conSInst ("slwi", "slw", munchExp e, i div 2)
	  | munchExp (T.BINOP (TO.LSHIFT, e1, e2)) =
	      binInst ("slw", munchExp e1, unboxInt (munchExp e2))
	  | munchExp (T.BINOP (TO.RSHIFT, e, T.CONST i)) =
	      (* need to clear the lsb... *)
	      (conSInstU ("srwi", "srw", munchExp e, i div 2 + 1);
	       boxInt ())
	  | munchExp (T.BINOP (TO.RSHIFT, e1, e2)) =
	      (binInstU ("srw", munchExp e1, unboxInt (munchExp e2));
	       (* clumsy! *)
	       ignore (unboxInt Frame.untagscratch);
	       boxInt ())
	  | munchExp (T.BINOP (TO.ARSHIFT, e, T.CONST i)) =
	      (conSInstU ("srawi", "sraw", munchExp e, i div 2 + 1);
	       boxInt ())
	  | munchExp (T.BINOP (TO.ARSHIFT, e1, e2)) =
	      (* clumsy! *)
	      (binInst ("sraw", munchExp e1, unboxInt (munchExp e2));
	       ignore (unboxInt Frame.untagscratch);
	       boxInt ())
	  | munchExp (T.BINOP (TO.XOR, e, T.CONST i) |
		      T.BINOP (TO.XOR, T.CONST i, e)) =
	      conLInst ("xori", "xor", munchExp e, i)
	  | munchExp (T.BINOP (TO.XOR, e1, e2)) =
	      binInst ("xor", munchExp e1, munchExp e2)

	(* munchIndex munches an expression representing a memory address;
	 * its result is to indicate which form of load/store instruction
	 * is to be used (lwz vs. lwzx, stw vs. stwx) and what the
	 * operands should be *)
	and munchIndex e =
	    let fun addConst (e, i) =
		    if i >= ~0x8000 andalso i < 0x8000 then
			BaseDisp (SOME (munchExp e), i)
		    else Indexed (munchExp e, const i)
	    in case e of
		   (T.BINOP (TO.PLUS, e, T.CONST i) |
		    T.BINOP (TO.PLUS, T.CONST i, e)) =>
		     addConst (e, i)
		 | T.BINOP (TO.MINUS, e, T.CONST i) =>
		     addConst (e, ~i)
		 | T.BINOP (TO.PLUS, e1, e2) =>
		     Indexed (munchExp e1, munchExp e2)
		 | T.CONST i =>
		     if i >= ~0x8000 andalso i < 0x8000 then BaseDisp (NONE, i)
		     else BaseDisp (SOME (const i), 0)
		 | e => BaseDisp (SOME (munchExp e), 0)
	    end

	(* emit a function epiloge; an epiloge is needed at every
	 * return and at every tail call *)
	fun emitEpilogue () =
	    let val ssn = Frame.frameSzName frame
	    in emit (A.OPER { asm = "lwz `d0,(" ^ ssn ^ "+8)(`s0)",
			      src = [Frame.sp],
			      dst = [Frame.r0],
			      jmp = A.NOJUMP });
	       emit A.REGRESTORE;
	       emit (A.OPER { asm = "addi `d0,`s0," ^ ssn,
			      src = [Frame.sp],
			      dst = [Frame.sp],
			      jmp = A.NOJUMP });
	       emit (A.OPER { asm = "mtlr `s0",
			      src = [Frame.r0],
			      dst = [],
			      jmp = A.NOJUMP })
	    end

	(* walk over the trace and munch it: *)
	fun munchTrace (T.LABEL lt) = munchLabTrace lt
	  | munchTrace (T.JUMP (l, ns)) =
	      (emit (A.OPER { asm = "b `j0",
			      src = [], dst = [], jmp = A.JUMP [l] });
	       munchNewStart ns)
	  | munchTrace (T.TCALL (e, el, ns)) =
	      (call (NONE, e, el, true);
	       munchNewStart ns)
	  | munchTrace (T.RETURN (el, ns)) =
	      let val tl = map munchExp el
		  fun movethem (_, [], l) = l
		    | movethem ([], _, _) =
		        bug "too many return values provided"
		    | movethem (d :: ds, s :: ss, l) =
		        (emitMove (d, s); movethem (ds, ss, d :: l))
		  val usedresults = movethem (Frame.results, tl, [])
	      in emitEpilogue ();
		 emit (A.OPER { asm = "blr",
				src = Frame.sp :: Frame.allocptr ::
				      Frame.limitptr :: Frame.calleesaves @
				      usedresults,
				dst = [],
				jmp = A.RETURN });
		 munchNewStart ns
	      end
	  | munchTrace (T.CJUMP (rop, e1, e2, l, lt as (l', _))) =
	      let fun operators TO.EQ = ("cmpw", "beq")
		    | operators TO.NE = ("cmpw", "bne")
		    | operators TO.LT = ("cmpw", "blt")
		    | operators TO.GT = ("cmpw", "bgt")
		    | operators TO.LE = ("cmpw", "ble")
		    | operators TO.GE = ("cmpw", "bge")
		    | operators TO.ULT = ("cmplw", "blt")
		    | operators TO.UGT = ("cmplw", "bgt")
		    | operators TO.ULE = ("cmplw", "ble")
		    | operators TO.UGE = ("cmplw", "bge")
		  fun generic_cmp () = let
		      val s1 = munchExp e1
		      val s2 = munchExp e2
		      val (cop, bop) = operators rop
		  in emit (A.OPER { asm = cop ^ " `s0,`s1",
				    src = [s1, s2], dst = [], jmp = A.NOJUMP });
		     emit (A.OPER { asm = bop ^ " `j0",
				    src = [], dst = [],
				    jmp = A.JUMP [l, l'] })
		  end
		  fun cmpi (rop, e, i) =
		      if i < ~0xfffff orelse i >= 0xffff then
			  generic_cmp ()
		      else
			  let val s = munchExp e
			      val (cop, bop) = operators rop
			  in emit (A.OPER { asm = concat [cop, "i `s0,", i2s i],
					    src = [s], dst = [],
					    jmp = A.NOJUMP });
			     emit (A.OPER { asm = bop ^ " `j0",
					    src = [], dst = [],
					    jmp = A.JUMP [l, l'] })
			  end
	      in case (e1, e2) of
		     (T.CONST i, e) => cmpi (TO.commute rop, e, i)
		   | (e, T.CONST i) => cmpi (rop, e, i)
		   | _ => generic_cmp ();
		 munchLabTrace lt
	      end
	  | munchTrace (T.CALL (lel, f, el, t)) =
	      (movel (lel, fn dl => call (SOME dl, f, el, false));
	       munchTrace t)
	  | munchTrace (T.MOVE (le, e, t)) =
	      (move (le, fn d => emitMove (d, munchExp e));
	       munchTrace t)
	  | munchTrace (T.DOCALL (f, el, t)) =
	      (call (NONE, f, el, false);
	       munchTrace t)
	  | munchTrace (T.DOEXP (e, t)) =
	      (ignore (munchExp e);
	       munchTrace t)
	  | munchTrace (T.GCTEST (e, t)) =
	      (* GC test:
	       *   - load amount into argument register 1 (r3)
	       *   - compare sum of r3 and alloc ptr with limit ptr
	       *   - if sum is greater, call the GC stub
	       *)
	      let val tmp = newtmp ()
	      in gengcstub ();
		 emitMove (Frame.arg1, munchExp e);
		 emit (A.OPER { asm = "add `d0,`s0,`s1",
				dst = [tmp], src = [Frame.arg1, Frame.allocptr],
				jmp = A.NOJUMP });
		 emit (A.OPER { asm = "cmplw `s0,`s1", dst = [], jmp = A.NOJUMP,
				src = [tmp, Frame.limitptr] });
		 emit (A.OPER { asm = "bgel " ^ Frame.gcstublabname,
				src = [Frame.arg1, Frame.allocptr,
				       Frame.limitptr, Frame.sp],
				(* these are the registers the GC stub
				 * is permitted to clobber: *)
				dst = Frame.allocptr :: Frame.limitptr ::
				      Frame.callersaves,
				jmp = A.NOJUMP });
		 munchTrace t
	      end
	  | munchTrace (T.ALLOCWRITE (e, t)) =
	      let val x = munchExp e
	      in emit (A.OPER { asm = "stwu `s0,4(`s1)", jmp = A.NOJUMP,
				src = [x, Frame.allocptr],
				dst = [Frame.allocptr] });
		 munchTrace t
	      end
	  | munchTrace (T.ALLOCCOPY (frombase, length, t)) =
	      let val (fv, lv, tmp) = (newtmp (), newtmp (), newtmp ())
		  val (startlab, exitlab) = (L.new NONE, L.new NONE)
	      in emitMove (fv, munchExp frombase);
		 emitMove (lv, munchExp length);
		 (* adjust fv to be aligned and pointing one word
		  * before the actual region *)
		 emit (A.OPER { asm = "addi `d0,`s0,-5",
				src = [fv], dst = [fv], jmp = A.NOJUMP });
		 (* convert length to wordlength (from bytelength),
		  * test for 0 *)
		 emit (A.OPER { asm = "srwi. `d0,`s0,2",
				src = [lv], dst = [lv], jmp = A.NOJUMP });
		 (* load the count register with word length *)
		 emit (A.OPER { asm = "mtctr `s0", dst = [], jmp = A.NOJUMP,
				src = [lv] });
		 (* jump around loop if zero *)
		 emit (A.OPER { asm = "beq `j0", src = [], dst = [],
				jmp = A.JUMP [exitlab, startlab ] });
		 (* here is the start of the loop *)
		 emit (A.LABEL startlab);
		 (* load word and increment pointer *)
		 emit (A.OPER { asm = "lwzu `d0,4(`s0)", jmp = A.NOJUMP,
				src = [fv], dst = [tmp, fv] });
		 (* store word and increment alloc ptr *)
		 emit (A.OPER { asm = "stwu `s0,4(`s1)", jmp = A.NOJUMP,
				src = [tmp, Frame.allocptr],
				dst = [Frame.allocptr] });
		 (* count down and branch if not yet zero *)
		 emit (A.OPER { asm = "bdnz `j0", src = [], dst = [],
				jmp = A.JUMP [startlab, exitlab] });
		 (* here is the exit of the loop *)
		 emit (A.LABEL exitlab);
		 (* continue *)
		 munchTrace t
	      end

	and movel ([], thunk) = thunk []
	  | movel (h :: t, thunk) =
	      move (h, fn d => movel (t, fn dl => thunk (d :: dl)))

      (* The move function takes the destination lexp (the LHS) and
       * a thunk for the RHS which expects a temp to write its result to.
       * If the real LHS is a memory location, then a store instruction
       * must be generated. *)
	and move (T.TEMP t, thunk) = thunk t
	  | move (T.ALLOCPTR, thunk) = thunk Frame.allocptr
	  | move (T.STACKPTR, thunk) =
	      (* TODO: make sure there are no live data on the stack
	       * at this point! *)
	      (thunk Frame.sp;
	       emit A.NOSTACK)	(* indicate that the old stack is
				 * no longer with us here *)
	  | move (T.MEM e, thunk) =
  	      let val t = newtmp ()
		  fun off i = i2s (i-1)
	      in case munchIndex e before thunk t of
		     BaseDisp (SOME base, disp) =>
		       emit (A.OPER { asm =
				        concat ["stw `s0,", off disp, "(`s1)"],
				      src = [t, base], dst = [],
				      jmp = A.NOJUMP })
		  | BaseDisp (NONE, disp) =>
		       emit (A.OPER { asm =
				        concat ["stw `s0,", off disp, "(0)"],
				      src = [t], dst = [], jmp = A.NOJUMP })
		  | Indexed (t1, t2) =>
		      let val t' = newtmp ()
		      in emit (A.OPER { asm = "add `d0,`s0,`s1",
					src = [t1, t2], dst = [t'],
					jmp = A.NOJUMP });
			 emit (A.OPER { asm = "stw `s0,-1(`s1)",
					src = [t', t], dst = [],
					jmp = A.NOJUMP })
		      end
	      end

	(* Generate code for call of functino given by f with arguments
	 * given by el.  Move result to the optional destination dopt.
	 * If "istcall" is true, then this is a tail-call. *)
	and call (dlopt, f, el, istcall) =
	    let val tcall_disabled = ref false
		fun prepareArgs () =
		    let fun moveToArg ([], _, rargs, k) =
			      (Frame.recordArgAreaTop (frame, k);
			       rev rargs)
			  | moveToArg (t :: ts, r :: rs, rargs, k) =
			      (emitMove (r, t);
			       moveToArg (ts, rs, r :: rargs, k + 4))
			  | moveToArg (t :: ts, [], rargs, k) =
			      (* more than 8 arguments;
			       * move argument to stack location.
			       * (If istcall, then we must give
			       * up on this being a real tail call!) *)
			      (tcall_disabled := true;
			       emit (A.OPER { asm = concat ["stw `s0,",
							    int2s k,
							    "(`s1)"],
					      src = [t, Frame.sp],
					      dst = [], jmp = A.NOJUMP });
			       moveToArg (ts, [], rargs, k + 4))
		    in moveToArg (map munchExp el,
				  Frame.args, [], Frame.argAreaBottom)
		    end
		(* Deal with the istcall flag; generate direct and indirect
		 * branch instruction opcodes, the jump info, sources,
		 * and destinations: *)
		fun do_tc () =
		    if istcall andalso not (!tcall_disabled) then
			(emitEpilogue ();
			 ("b", "bctr", A.RETURN,
			  Frame.sp :: Frame.allocptr :: Frame.limitptr ::
			  Frame.calleesaves,
			  []))
		    else ("bl", "bctrl", A.NOJUMP,
			  [],
			  Frame.callersaves)
	    in case f of
		   T.NAME l =>
		     (* direct call of named function *)
		     let val n = L.escname l
			 val args = prepareArgs ()
			 val (opcode, _, ji, extra_src, dst) = do_tc ()
		     in if L.isExternal l then
			    (* invocation of external function goes through
			     * linkage stub *)
			    let val n_stub = concat ["L", n, "$stub"]
				val n_lptr = concat ["L", n, "$lazy_ptr"]
			    in emit (A.OPER { asm = opcode ^ " " ^ n_stub,
					      src = args @ extra_src,
					      dst = dst,
					      jmp = ji });
			       genfunstub (l, n, n_stub, n_lptr)
			    end
			else
			    (* local function call *)
			    emit (A.OPER { asm = opcode ^ " " ^ n,
					   src = args @ extra_src,
					   dst = dst,
					   jmp = ji })
		     end
		  | f =>
		      (* indirect function call; invocation goes through
		       * count register; function pointer must also be
		       * in r12 (= Frame.indirfunptr) *)
		      let val ft = munchExp f
			  val args = prepareArgs ()
			  val _ = emitMove (Frame.indirfunptr, ft);
			  val (_, opcode, ji, extra_src, dst) = do_tc ()
		      in emit (A.OPER { asm = "mtctr `s0",
					dst = [], src = [Frame.indirfunptr],
					jmp = A.NOJUMP });
			 emit (A.OPER { asm = opcode,
					src = Frame.indirfunptr ::
					      args @ extra_src,
					dst = dst,
					jmp = ji })
		      end;
	       case dlopt of
		   SOME tl =>
		     let fun movethem ([], _) = ()
			   | movethem (_, []) = bug "too many results"
			   | movethem (t :: ts, r :: rs) =
			       (emitMove (t, r); movethem (ts, rs))
		     in movethem (tl, Frame.results)
		     end
		 | NONE =>
		     if istcall andalso !tcall_disabled then
			 (* this was supposed to be a tail call,
			  * but because of too many arguments we
			  * had to do an ordinary call.  Now the results
			  * are were they are supposed to be, so we just
			  * have to issue a return *)
			 (emitEpilogue ();
			  emit (A.OPER { asm = "blr",
					 src = Frame.sp :: Frame.allocptr ::
					       Frame.limitptr ::
					       Frame.calleesaves @
					       Frame.results,
					 dst = [],
					 jmp = A.RETURN }))
		     else ()
	    end

	(* process a labeled trace *)
	and munchLabTrace (l, t) = (emit (A.LABEL l); munchTrace t)

	(* process a "new start" *)
	and munchNewStart T.END = ()
	  | munchNewStart (T.JTARGET lt) = munchLabTrace lt
	  | munchNewStart (T.ENTRY e) = munchEntry e

	(* process a function entry point *)
	and munchEntry (vl, (l, t), false) =
	    let (* the size of the stack frame is still unknown, so
		 * we use a symbolic name to refer to it: *)
		val ssn = Frame.frameSzName frame
		(* move arguments into the temps in vl: *)
		fun moveFromArg ([], _, _) = ()
		  | moveFromArg (v :: vl, r :: rs, k) =
		      (emitMove (v, r);
		       moveFromArg (vl, rs, k + 4))
		  | moveFromArg (v :: vl, [], k) =
		      (* more than 8 arguments: get values from stack;
		       * (the stack frame has already been extended at
		       * this point) *)
		      (emit (A.OPER { asm = concat ["lwz `d0,",
						    int2s k,
						    "+", ssn,
						    "(`s0)"],
				      src = [Frame.sp], dst = [v],
				      jmp = A.NOJUMP });
		       moveFromArg (vl, [], k + 4))
	    in emit (A.LABEL l);
	       (* get return address from link register into r0 *)
	       emit (A.OPER { asm = "mflr `d0",
			      src = [], dst = [Frame.r0], jmp = A.NOJUMP });
	       (* store return address into stack frame *)
	       emit (A.OPER { asm = "stw `s0,8(`s1)",
			      src = [Frame.r0, Frame.sp],
			      dst = [], jmp = A.NOJUMP });
	       (* extend stack frame and establish dynamic link *)
	       emit (A.OPER { asm = "stwu `d0,-" ^ ssn ^ "(`s0)",
			      src = [Frame.sp], dst = [Frame.sp],
			      jmp = A.NOJUMP });
	       (* save callee-save registers if necessary *)
	       emit A.REGSAVE;
	       (* move arguments into their temps *)
	       moveFromArg (vl, Frame.args, Frame.argAreaBottom);
	       (* process rest of the code *)
	       munchTrace t
	    end
	  | munchEntry (vl, (l, t), true) = (* exception handler entry point *)
	      let fun moveFromArg ([], _, _) = ()
		    | moveFromArg (v :: vl, r :: rs, k) =
		        (emitMove (v, r);
			 moveFromArg (vl, rs, k + 4))
		    | moveFromArg (v :: vl, [], k) =
		        (emit (A.OPER { asm = concat ["lwz `d0,",
						      int2s k, "(`s0)"],
					src = [Frame.sp], dst = [v],
					jmp = A.NOJUMP });
			 moveFromArg (vl, [], k + 4))
	      in emit (A.LABEL l);
		 moveFromArg (vl, Frame.args, Frame.argAreaBottom);
		 munchTrace t
	      end

    in munchEntry entry;
       rev (!ilist)
    end
end
