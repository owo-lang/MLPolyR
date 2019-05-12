local
val yacc_lib = [
    "base.sig",
    "join.sml",
    "lrtable.sml",
    "stream.sml",
    "parser2.sml",
    ""]
fun load (p,l) = List.app (fn "" => () | s => use (p^s)) l
in
val () = load ("util/ml-yacc/lib/", yacc_lib)
end
