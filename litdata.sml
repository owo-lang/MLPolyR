(* litdata.sml
 *
 *   Literal data (32-bit integers) in the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure LiteralData = struct

    type integer = Int.int

    val fromInt = Int.fromInt
    val toInt = Int.toInt

    val fromString = Int.fromString
    val toString = Int.toString

    val compare = Int.compare

    val toLarge = Int.toLarge
end
