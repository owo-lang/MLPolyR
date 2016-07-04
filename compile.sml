(* compile.sml
 *
 *   This module contains the driver code for all passes
 *   after parsing of the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Compile : sig

    val compile :
	{ pclust: bool, pbbt: bool, pigraph: bool, no_ra: bool, pdefs: bool } ->
	Ast.program * Source.inputSource * TextIO.outstream -> bool

end = struct

    fun compile { pclust, pbbt, pigraph, no_ra, pdefs }
		(ast, source, asm_s) = let

	val _ = LVar.reset ()
	val _ = Label.reset ()
	val _ = TVar.reset ()

	val limit_ptr_lab = Label.external "mlpr_limit_ptr"
	val main_stack_ptr_lab = Label.external "mlpr_main_stack_ptr"
	val frame_info_table_lab = Label.external "mlpr_frame_info_table"

	fun emit s = TextIO.output (asm_s, s)

	fun label l =
	    let val n = Label.name l
	    in if Char.contains n #"'" then emit (concat ["\"", n, "\":\n"])
	       else emit (n ^ ":\n")
	    end
	fun wordalign () = emit "\t.align 2\n"
	fun stubsection () =
	    emit ".section __TEXT,__symbol_stub1,symbol_stubs,\
		 \pure_instructions,16\n"
	fun textsection () =
	    emit ".section __TEXT,__text,regular,pure_instructions\n"
	fun datasection () = emit ".data\n";

	fun gvarheader lab =
	    (emit (concat ["\n\n\t.globl ", Label.name lab, "\n"]);
	     datasection();
	     wordalign();
	     label lab)

	val absyn = Elaborate.elaborate (source, BaseEnv.elabBase, pdefs) ast

	val { lambda, strings } =
	    Translate.translate (absyn, BaseEnv.transBase)

	val anf = LambdaToANF.convert lambda

(*
	val _ = PrintANF.function print anf
*)

	val anf = ANFOpt.optimize anf
	val anf = ANFOpt.optimize anf

	val anf = Flatten.transform anf
	val anf = ANFOpt.optimize anf
	val anf = ANFOpt.optimize anf

(*
	val _ = PrintANF.function print anf
*)

	val anf = Uncurry.transform anf
(*
        val _ = PrintANF.function print anf
*)
	val anf = ANFOpt.optimize anf
	val anf = ANFOpt.optimize anf
	val anf = ANFOpt.optimize anf
(*
        val _ = PrintANF.function print anf
*)
	val anf = Flatten.transform anf
	val anf = ANFOpt.optimize anf
	val anf = ANFOpt.optimize anf

(*
	val _ = PrintANF.function print anf
*)

	val closed = Closure.convert anf
	val fc as { entrylabel, clusters } = FunctionClusters.clusterify closed

	val _ = if pclust then
		    PrintClusters.print print fc
		else ()

	val clusters = map ValueNumbering.cluster_cse clusters
	val bbt_clusters = map Treeify.treeify clusters

	val _ = if pbbt then
		    app (PrintBBTree.prcluster print) bbt_clusters
		else ()

	val traces = map TraceSchedule.schedule bbt_clusters

	val compilation = PPCCodeGen.new ()

	fun dotrace (et as (_, (l, _), _)) =
	    let val frame = Frame.new l
		val il = PPCCodeGen.codegen (frame, compilation, et)
		val (il_a, allocation) =
		    RegAlloc.alloc { showigraph = pigraph }
				   (il, frame, Frame.registers)
		val (il', allocation') =
		    if no_ra then (il, Frame.precoloring)
		    else (il_a, allocation)
		val { save, restore, size, sz_regsave, sz_upper } =
		    Frame.regSaveRestoreInfo (frame, allocation)
		val i2sl = Asm.format (Frame.showTemp allocation',
				       save, restore)
		fun withnl s = s ^ "\n"
		fun emiti i = app (emit o withnl) (i2sl i)

		val (l_start, l_end) = (Label.new NONE, Label.new NONE)

	    in textsection ();
	       wordalign ();
		
	       label l_start;

	       emit (concat [Frame.frameSzName frame, "=",
			     Int.toString size, "\n"]);
	       if Frame.hasSpills frame then
		   emit (concat [Frame.frameSpillName frame, "=",
				 Int.toString (size - sz_regsave), "\n"])
	       else ();
	       
	       app emiti il';

	       label l_end;

	       (* return table entry for GC *)
	       (l_start, l_end, sz_upper)
	    end

	fun dotable entries =
	    let fun emit1 (l1, l2, size) =
		    (emit (concat ["\t.long ", Label.name l1, "\n"]);
		     emit (concat ["\t.long ", Label.name l2, "\n"]);
		     emit (concat ["\t.long ", Int.toString size, "\n"]))
	    in gvarheader frame_info_table_lab;
	       app emit1 entries;
	       emit "\t.long 0\n"
	    end

	fun dostring (s, l) =
	    (datasection ();
	     emit ".cstring\n";
	     wordalign ();
	     label l;
	     emit (concat ["\t.asciz \"", String.toCString s, "\"\n"]))

	fun dostubs () =
	    let val { funstubs, datastubs, needgc } =
		    PPCCodeGen.getstubs compilation
	    in stubsection ();
	       app emit funstubs;
	       datasection ();
	       app emit datastubs;
	       if needgc then
		 (textsection ();
		  (* emit gc stub label *) 
		  label Frame.gcstublab;
		  (* Get return address into r0 *)
		  emit("\tmflr r0\n");
		  (* Save the return address *)
		  emit("\tstw r0,8(r1)\n");
		  (* Allocate the stack frame *)
		  emit("\tstwu r1,-128(r1)\n");
		  (* Save all the callee saved registers *)
		  emit("\tstmw r15,60(r1)\n");
		  (* Move amount, alloc_ptr, limit_ptr, and  
		     stack_ptr into argument registers.
		     Note: r3 already contains amount.
		     Note: while in ML, allocptr and limitptr
		           point to the last word written and
		           the last word available, resp.
		   *)
		  emit("\taddi r4,r13,4\n");
		  emit("\taddi r5,r14,4\n");
		  emit("\tmr r6,r1\n");

		  (* Invoke the GC function *)
		  emit ("\tbl L" ^ Label.escname Frame.gclab ^ "$stub\n");

		  (* Store the returned values (alloc_ptr and limit_ptr)
		     into r13 and r14.  Restore the invariants with
		     respect to alloc_ptr and limit_ptr while in ML
		     while in ML (see Note above).
		   *)
		  emit("\taddi r13,r3,-4\n");

		  emit(concat["\tlis r14,ha16(", Label.name limit_ptr_lab,
			      ")\n"]);
		  emit(concat["\tlwz r14,lo16(", Label.name limit_ptr_lab,
			      ") (r14)\n"]);
		  emit(concat["\taddi r14,r14,-4\n"]);

                  (* Restore all callee saved registers. *)
		  emit("\tlmw r15,60(r1)\n");

		  (* Return to ml code *)
		  emit("\taddi r1,r1,128\n");
		  emit("\tlwz r0,8(r1)\n");
		  emit("\tmtlr r0\n");
		  emit("\tblr\n"))
	       else ()
	    end

	val eplab = Label.external "mlpr_entrypoint"

	fun load_zero (from, to) =
	    if from <= to then
		(emit (concat ["\tli r", Int.toString from, ",0\n"]);
		 load_zero (from+1, to))
	    else ()

	fun dosetup () =
	    (textsection ();
	     wordalign ();
	     label eplab;
             (* Get return address into r0 *)
             emit("\tmflr r0\n");
             (* Save the return address *)
             emit("\tstw r0,8(r1)\n");
             (* Allocate the stack frame *)
             emit("\tstwu r1,-128(r1)\n"); 	
 	     (* Save all the callee saved registers *)
             emit("\tstmw r15,60(r1)\n");

	     load_zero(15,30);

	     emit "\taddi r13,r5,-4\n";
	     emit "\taddi r14,r6,-4\n";

	     emit (concat ["\tlis r5,ha16(", Label.name main_stack_ptr_lab,
			   ")\n"]);
	     emit (concat ["\tstw r1,lo16(", Label.name main_stack_ptr_lab,
			   ")(r5)\n"]);

	     emit (concat ["\tbl ", Label.name entrylabel, "\n"]);

	     (* Restore all callee saved registers. *)
             emit("\tlmw r15,60(r1)\n");

	     (* Return to ml code *)
             emit("\taddi r1,r1,128\n");
             emit("\tlwz r0,8(r1)\n");
             emit("\tmtlr r0\n");
             emit("\tblr\n"))


    in if ErrorMsg.anyErrors (ErrorMsg.errors source) then false
       else let val _  = emit (concat ["\t.globl ", Label.name eplab, "\n"])
		val _ = dosetup ()
		val pctable = map dotrace traces
	    in app dostring strings;
	       dostubs ();

	       gvarheader main_stack_ptr_lab;
	       emit "\t.long 0\n";
	       gvarheader limit_ptr_lab;
	       emit "\t.long 0\n";

	       dotable pctable;

	       true
	    end
    end
end
