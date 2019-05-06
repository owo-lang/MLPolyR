(* main.sml
 *
 *   Driver routine for MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Main : sig

    val compile :
	{ pclust: bool, pbbt: bool, pigraph: bool, no_ra: bool, pdefs: bool } ->
	string * string -> bool

    val main : string * string list -> OS.Process.status

end = struct

    datatype state = ToAsm | ToTC | ToObj | ToExe

    val rts = "rt/mlpr-rt.o"

    fun remove file =
	OS.FileSys.remove file handle _ => ()

    fun typecheck { pclust, pbbt, pigraph, no_ra, pdefs } file =
	let val (ast, source) = Parse.parse file
	in if ErrorMsg.anyErrors (ErrorMsg.errors source) then false
	   else let val absyn = Elaborate.elaborate (source, BaseEnv.elabBase, pdefs) ast
		in true
		end
	end

    fun compile cflags (file, asmfile) =
	let val (ast, source) = Parse.parse file
	in if ErrorMsg.anyErrors (ErrorMsg.errors source) then false
	   else let val asm_s = TextIO.openOut asmfile
		in Compile.compile cflags (ast, source, asm_s)
		   before TextIO.closeOut asm_s
		end
	end

    fun main (self, args) = let

	fun complain msg =
	    TextIO.output (TextIO.stdErr, concat (self :: ": " :: msg))

	fun system cmd =
	    if OS.Process.system cmd = OS.Process.success then true
	    else (complain ["command `", cmd, "' failed\n"];
		  false)

	fun assemble (asmfile, objfile) =
	    system (concat ["as -o ", objfile, " ", asmfile])

	fun link (objfile, executable) =
	    system (concat ["cc -o ", executable, " ",
			    objfile, " ", rts])

	fun onefile (flags, state, target, file) = let
	    fun aoe base =
		(OS.Path.joinBaseExt { base = base, ext = SOME "s" },
		 OS.Path.joinBaseExt { base = base, ext = SOME "o" },
		 base)
	    val (asmfile, objfile, executable) =
		case OS.Path.splitBaseExt file of
		    { base, ext = SOME "mlpr" } => aoe base
		  | _ => aoe file
	in case state of
	       ToAsm => compile flags (file, getOpt (target, asmfile))
	     | ToTC => typecheck flags file
	     | ToObj =>
	         ((compile flags (file, asmfile) andalso
		   assemble (asmfile, getOpt (target, objfile)))
		  before remove asmfile)
	     | ToExe =>
	         ((((compile flags (file, asmfile) andalso
		     assemble (asmfile, objfile))
		    before remove asmfile) andalso
		   link (objfile, getOpt (target, executable)))
		  before remove objfile)
	end

	fun setPC { pclust, pbbt, pigraph, no_ra, pdefs } =
	    { pclust = true, pbbt = pbbt, pigraph = pigraph,
	      no_ra = no_ra, pdefs = pdefs }
	fun setPT { pclust, pbbt, pigraph, no_ra, pdefs } =
	    { pclust = pclust, pbbt = true, pigraph = pigraph,
	      no_ra = no_ra, pdefs = pdefs }
	fun setSG { pclust, pbbt, pigraph, no_ra, pdefs } =
	    { pclust = pclust, pbbt = pbbt, pigraph = true,
	      no_ra = no_ra, pdefs = pdefs }
	fun setNORA { pclust, pbbt, pigraph, no_ra, pdefs } =
	    { pclust = pclust, pbbt = pbbt, pigraph = pigraph,
	      no_ra = true, pdefs = pdefs }
	fun setPD { pclust, pbbt, pigraph, no_ra, pdefs } =
	    { pclust = pclust, pbbt = pbbt, pigraph = pigraph,
	      no_ra = no_ra, pdefs = true }
	val noflags = 
	    { pclust = false, pbbt = false, pigraph = false,
	      no_ra = false, pdefs = false }

	fun process (flags, state, _, "-o" :: target :: rest) =
	      process (flags, state, SOME target, rest)
	  | process (_, _, _, ["-o"]) =
	      (complain ["option -o given without argument\n"];
	       OS.Process.failure)
	  | process (flags, _, target, "-S" :: rest) =
	      process (flags, ToAsm, target, rest)
	  | process (flags, _, target, "-t" :: rest) =
	      process (flags, ToTC, target, rest)
	  | process (flags, _, target, "-c" :: rest) =
	      process (flags, ToObj, target, rest)
	  | process (flags, state, target, "-PC" :: rest) =
	      process (setPC flags, state, target, rest)
	  | process (flags, state, target, "-PT" :: rest) =
	      process (setPT flags, state, target, rest)
	  | process (flags, state, target, "-SG" :: rest) =
	      process (setSG flags, state, target, rest)
	  | process (flags, state, target, "-NORA" :: rest) =
	      process (setNORA flags, state, target, rest)
	  | process (flags, state, target, "-PD" :: rest) =
	      process (setPD flags, state, target, rest)
	  | process (flags, state, target, file :: rest) =
	      if onefile (flags, state, target, file)
	      then process (flags, state, target, rest)
	      else OS.Process.failure
	  | process (_, _, _, []) = OS.Process.success
    in process (noflags, ToExe, NONE, args)
    end handle e =>
	       (TextIO.output (TextIO.stdErr, General.exnMessage e ^ "\n");
		OS.Process.failure)
end
