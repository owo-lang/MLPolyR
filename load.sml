val source =
    ["litdata",
     "machspec",

     "oper",

     "purity",

     "notyet",

     "util/poly_smlnj-lib",

     "symbol",

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

     "util/poly_sourcemap"

    ]

val () = List.app use source;

structure L = Lambda

fun intv i = L.VALUE (L.INT i);
fun varv i = L.VALUE (L.VAR i);
fun stub _ = raise Fail "This is a stub";
val program : L.exp = L.ARITH (Oper.PLUS, intv 1, intv 12);

fun main() = let val (LambdaInterpreter.INTv res) = LambdaInterpreter.eval stub program
             in
                 print (LiteralData.toString res)
             end
