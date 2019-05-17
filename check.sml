use "load.sml";

structure Cmd = CommandLine

fun main() =
	  let val [file] = Cmd.arguments()
        val (ast, source) = Parse.parse file
	      val _ = if ErrorMsg.anyErrors source then false
	              else let val asyn = Elaborate.elaborate
				                                (source, BaseEnv.elabBase, false) ast
		                 in true
                     end
    in ()
	  end
