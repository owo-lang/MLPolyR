local
val source = ["litdata",
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

              "ast"]

in

val _ = List.app use source

end

fun main() = print "Check!\n"
