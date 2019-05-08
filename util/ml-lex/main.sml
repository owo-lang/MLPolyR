val () = use "lexgen.sml";

structure Cmd = CommandLine

fun usage s = let val name = Cmd.name()
              in
                  (print name;
                   print ": file.lex ...\n";
                   print s)
              end

fun main () = let val args = Cmd.arguments()
              in
                  case args of
                      [] => usage "no files\n"
                    | ("-h" :: _) => usage ""
                    | xs => List.app LexGen.lexGen xs
              end

