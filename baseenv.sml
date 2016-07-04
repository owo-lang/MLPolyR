(*  baseenv.sml
 *
 *   The "basis environment" with bindings for built-in values
 *   for MLPolyR.  The actual implementation of these values
 *   resides in the runtime system (which is written in C).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure BaseEnv : sig

    val elabBase  : Types.typschema Env.env
    val transBase : Lambda.exp Env.env
end = struct

    structure T = Types
    structure TU = TypesUtil

    val r = (0, 0)

    infix --> fun t1 --> t2 = let val rt = TU.freshrty0 (0, r)
			      in T.FUNty (t1, t2, rt, r)
			      end
    val int = T.INTty r
    val string = T.STRINGty r
    val unit = T.UNITty r
    fun tuple tl = T.TUPLEty (map (fn t => (t, r)) tl, r)
    fun list t = T.LISTty (t, r)

    val srecsym = Symbol.atom "String"
    val sreclabstring = "builtin_mlpr_String"
    val srecty =
	TU.mkRecordTyp
	    ([("toInt", string --> int, r),
	      ("fromInt", int --> string, r),
	      ("inputLine", unit --> string, r),
	      ("size", string --> int, r),
	      ("output", string --> unit, r),
	      ("sub", tuple [string, int] --> int, r),
	      ("concat", list string --> string, r),
	      ("substring", tuple [string, int, int] --> string, r),
	      ("compare", tuple [string, string] --> int, r),
	      ("cmdline_args", list string, r),
	      ("cmdline_pgm", string, r)],
	     r)

    val srectys : Types.typschema = #1 (TU.generalize 0 srecty)

    val srecexp = ExternalAccess.access sreclabstring

    val elabBase = Env.bind (srecsym, srectys, Env.empty)
    val transBase = Env.bind (srecsym, srecexp, Env.empty)
end
