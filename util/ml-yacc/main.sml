val () = use "poly_mlyacc.sml";

structure Cmd = CommandLine

fun usage s = let val name = Cmd.name()
              in
                  (print name;
                   print ": file.grm ...\n";
                   print s)
              end
fun main () = let val args = Cmd.arguments()
              in
                  case args of
                      [] => usage "no files\n"
                    | ("-h" :: _) => usage ""
                    | [f] => ParseGen.parseGen f
                    | _ => usage "too many files"
              end
