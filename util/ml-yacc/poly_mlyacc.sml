local
val yacc_lib = [
"base.sig",
"join.sml",
"lrtable.sml",
"stream.sml",
"parser2.sml",
""]
val yacc_src = [
    "utils.sig",
    "utils.sml",
    "sigs.sml",
    "hdr.sml",
    "yacc.grm.sig",
    "yacc.grm.sml",
    "yacc.lex.sml",
    "parse.sml",
    "grammar.sml",
    "core.sml",
    "coreutils.sml",
    "graph.sml",
    "look.sml",
    "lalr.sml",
    "mklrtable.sml",
    "mkprstruct.sml",
    "shrink.sml",
    "verbose.sml",
    "absyn.sig",
    "absyn.sml",
    "yacc.sml",
    "link.sml",
    ""]
fun load (p,l) = List.app (fn "" => () | s => use (p^s)) l
in
val () = load ("lib/", yacc_lib)
val () =  load ("src/", yacc_src)
end
