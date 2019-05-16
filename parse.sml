(* parse.sml
 *
 *   Driver code for MLPolyR's ML-Yacc/ML-Lex-based parser.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Parse : sig
          end = struct
structure MLPolyRLrVals =
MLPolyRLrValsFun (structure Token = LrParser.Token)
structure Lex =
MLPolyRLexFun (structure Tokens = MLPolyRLrVals.Tokens)
structure MLPolyRP =
JoinWithArg (structure ParserData = MLPolyRLrVals.ParserData
             structure Lex=Lex
		         structure LrParser = LrParser)


end
