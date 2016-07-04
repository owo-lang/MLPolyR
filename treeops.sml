(* treeops.sml
 *
 *   Arithmetic and relational operations used in trees.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure TreeOps = struct

    datatype binop =
	PLUS | MINUS | MUL | DIV | MOD
      | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR

    datatype relop =
	EQ | NE | LT | GT | LE | GE 
      | ULT | ULE | UGT | UGE

    fun binop2string PLUS = "+"
      | binop2string MINUS = "-"
      | binop2string MUL = "*"
      | binop2string DIV = "/"
      | binop2string MOD = "%"
      | binop2string AND = "&"
      | binop2string OR = "|"
      | binop2string LSHIFT = "<<"
      | binop2string RSHIFT = ">>"
      | binop2string ARSHIFT = "~>>"
      | binop2string XOR = "^"

    fun relop2string EQ = "=="
      | relop2string NE = "<>"
      | relop2string LT = "<"
      | relop2string GT = ">"
      | relop2string LE = "<="
      | relop2string GE = ">="
      | relop2string ULT = "!<"
      | relop2string UGT = "!>"
      | relop2string ULE = "!<="
      | relop2string UGE = "!>="

    fun notRel EQ = NE
      | notRel NE = EQ
      | notRel LT = GE
      | notRel GE = LT
      | notRel LE = GT
      | notRel GT = LE
      | notRel ULT = UGE
      | notRel UGE = ULT
      | notRel ULE = UGT
      | notRel UGT = ULE

    fun commute EQ = EQ
      | commute NE = NE
      | commute LT = GT
      | commute GT = LT
      | commute LE = GE
      | commute GE = LE
      | commute ULT = UGT
      | commute UGT = ULE
      | commute ULE = UGE
      | commute UGE = ULE
end
