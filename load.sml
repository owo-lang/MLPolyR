val source =
    ["litdata",
     "machspec",

     "oper",

     "purity",

     "notyet",

     "util/poly_smlnj-lib",

     "symbol",

     "util/poly_sourcemap",
     "util/errormsg/errormsg.sml",

     "lvar",
     "label",
     "lambda",
     "lambda-interpreter",
     "treeops",
     "bbtree",

     "reclab",

     "ast",
     "anf",
     "anf-opt",
     "anf-interpreter",
     "lambda2anf",
     "pranf",
     "tvar",
     "types",
     "typesutil",
     "env",
     "extacc",
     "baseenv",


     "util/poly_mlyacc.sml",
     "mlpolyr.grm.sig",
     "mlpolyr.grm.sml",
     "mlpolyr.lex.sml",

     "parse",

     "absyn",
     "unify",
     "elaborate"
    ]

val () = List.app use source;
