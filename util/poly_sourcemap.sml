local
val yacc_lib = [
    "sourcemap.sig",
    "sourcemap.sml",
    "source.sig",
    "source.sml",
    ""]
fun load (p,l) = List.app (fn "" => () | s => use (p^s)) l
in
val () = load ("util/sourcemap/", yacc_lib)
end
