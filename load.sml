val source =
    ["litdata",
     "oper",
     "purity",
     "util/poly_smlnj-lib",
     "symbol",
     "util/errormsg/errormsg.sml",
     "lvar",
     "label",
     "reclab",
     "ast",
     "util/poly_mlyacc.sml",
     "mlpolyr.grm.sig",
     "mlpolyr.grm.sml",
     "mlpolyr.lex.sml",

     "util/poly_sourcemap",
     "parse"

    ]

val () = List.app use source;

