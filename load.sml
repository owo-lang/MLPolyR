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

     "reclab",

     "ast",
     "anf",
     "anf-interpreter",
     "lambda2anf",
     "pranf",
     "tvar",
     "types",

     "util/poly_mlyacc.sml",
     "mlpolyr.grm.sig",
     "mlpolyr.grm.sml"
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
