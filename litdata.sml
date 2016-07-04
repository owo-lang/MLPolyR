(* litdata.sml
 *
 *   Literal data (32-bit integers) in the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure LiteralData = struct

    type integer = Int32.int

    val fromInt = Int32.fromInt
    val toInt = Int32.toInt

    val fromString = Int32.fromString
    val toString = Int32.toString

    val compare = Int32.compare

    val toLarge = Int32.toLarge
end
