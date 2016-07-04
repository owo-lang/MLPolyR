(* parse.sml
 *
 *   Driver code for MLPolyR's ML-Yacc/ML-Lex-based parser.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Parse : sig
    val parse : string -> Ast.program * Source.inputSource
end = struct 
    structure MLPolyRLrVals =
        MLPolyRLrValsFun (structure Token = LrParser.Token)
    structure Lex =
        MLPolyRLexFun (structure Tokens = MLPolyRLrVals.Tokens)
    structure MLPolyRP =
        JoinWithArg (structure ParserData = MLPolyRLrVals.ParserData
                     structure Lex=Lex
		     structure LrParser = LrParser)

    val errcons = ErrorMsg.defaultConsumer ()

    fun parse filename =
	let val _ = LVar.reset ()
	    val _ = Label.reset ()
	    val file = TextIO.openIn filename
	    val source = Source.newSource (filename, 1, file, false, errcons)
	    val sm = #sourceMap source
	    fun error r m =
		ErrorMsg.error source r ErrorMsg.COMPLAIN m
			       ErrorMsg.nullErrorBody
	    val depth = ref 0
	    fun enterC () = depth := !depth + 1
	    fun leaveC () = let val d = !depth - 1 in depth := d; d = 0 end
	    fun newline pos = SourceMap.newline sm pos

	    val curstring = ref []
	    val startpos = ref 0
	    val instring = ref false
	    fun newS sp = (startpos := sp; curstring := []; instring := true)
	    fun addS c = curstring := c :: !curstring
	    fun getS ep = (instring := false;
			   (String.implode (rev (!curstring)), !startpos, ep))

	    fun handleEof () = let
		val pos = SourceMap.lastChange sm
	    in if !depth > 0 then
		   error (pos, pos) "unexpected end of input in comment"
	       else if !instring then
		   error (pos, pos) "unexpected end of input in string literal"
	       else ();
	       Source.closeSource source;
	       pos
	    end
	    fun get _ = TextIO.input file
	    val lexarg =
		{ enterC = enterC, leaveC = leaveC,
		  newS = newS, addS = addS, getS = getS,
		  handleEof = handleEof,
		  newline = newline,
		  error = error }
	    val lexer = MLPolyRP.makeLexer get lexarg
	    val (ast, _) = MLPolyRP.parse
			       (30,lexer,
			        fn (s, p, p') => error (p, p') s,
				())
	in (ast, source)
	end handle LrParser.ParseError => raise ErrorMsg.Error
end
