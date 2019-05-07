(*
 * Lambda representation based interpreter.
 * Copyright (c) 2019 by LdBeth
 *)

structure Interpreter : sig

              val runtime : Label.label -> LambdaInterpreter.value
              val makeProgram : Lambda.function -> Lambda.exp
	      val printResult : LambdaInterpreter.value -> unit

          end = struct

structure L = Lambda

(* stub runtime *)
fun runtime label = let val _ = print "Called label: "
                        val _ = print (Label.name label)
                        val _ = print "\n"
                    in
                        raise Fail "I/O is still a stub"
                    end

(* helpers *)
fun intv i = L.VALUE (L.INT i)
fun varv i = L.VALUE (L.VAR i)

(* stub eh function *)
val ehfun : L.function = (LVar.new "eh", [], intv 255 ,false)

fun makeProgram def =
    let val (fname, _, _, _) = def
        val (eh, _, _, _) = ehfun
    in
        L.FIX ([def,ehfun], L.APP (Purity.Impure, varv fname, [varv eh]))
    end

fun printResult (LambdaInterpreter.INTv i) =
    (print "Result is: ";
     print (LiteralData.toString (i div 2)); (* MLPolyR use even num for int *)
     print "\n")
  | printResult _ = raise Fail "Panic!"
	
end
