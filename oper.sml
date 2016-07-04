(* oper.sml
 *
 *   (Source-level) arithmetic- and comparison operators for MLPolyR.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Oper = struct

    datatype cmpop =
	EQ
      | LTEQ
      | LT
      | GTEQ
      | GT
      | NEQ

    datatype arithop =
	PLUS
      | MINUS
      | TIMES
      | DIV
      | MOD

    fun purearith PLUS = true
      | purearith MINUS = true
      | purearith TIMES = true
      | purearith DIV = false
      | purearith MOD = false

    fun commutative PLUS = true
      | commutative MINUS = false
      | commutative TIMES = true
      | commutative DIV = false
      | commutative MOD = false

    fun doarith (PLUS, x: LiteralData.integer, y) = x + y
      | doarith (MINUS, x, y) = x - y
      | doarith (TIMES, x, y) = x * y
      | doarith (DIV, x, y) = x div y
      | doarith (MOD, x, y) = x mod y

    fun astring PLUS = "+"
      | astring MINUS = "-"
      | astring TIMES = "*"
      | astring DIV = "/"
      | astring MOD = "%"

    fun docmp (EQ, x: LiteralData.integer, y) = x = y
      | docmp (LTEQ, x, y) = x <= y
      | docmp (LT, x, y) = x < y
      | docmp (GTEQ, x, y) = x >= y
      | docmp (GT, x, y) = x > y
      | docmp (NEQ, x, y) = x <> y

    fun cstring EQ = "=="
      | cstring LTEQ = "<="
      | cstring LT = "<"
      | cstring GTEQ = ">="
      | cstring GT = ">"
      | cstring NEQ = "<>"
end
