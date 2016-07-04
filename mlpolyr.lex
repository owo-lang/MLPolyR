(* -*- sml-lex -*-
 * mlpolyr.lex
 *
 *   The lexer for the MLPolyR compiler (as ML-Lex specification).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)

structure T = Tokens
structure E = ErrorMsg

type pos            = int
type svalue         = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult      = (svalue,pos) token

type lexarg         = { enterC : unit -> unit,
			leaveC : unit -> bool,
			newS : pos -> unit,
			addS : char -> unit,
			getS : pos -> string * pos * pos,
			handleEof : unit -> pos,
			newline : pos -> unit,
			error : pos * pos -> string -> unit }

type arg = lexarg

fun eof (arg: lexarg) =
    let val pos = #handleEof arg ()
    in T.EOF (pos, pos)
    end

local
    val idlist = [("andalso", T.KW_andalso),
		  ("orelse", T.KW_orelse),
		  ("if", T.KW_if),
		  ("then", T.KW_then),
		  ("else", T.KW_else),
		  ("false", T.KW_false),
		  ("true", T.KW_true),
		  ("let", T.KW_let),
		  ("in", T.KW_in),
		  ("end", T.KW_end),
		  ("fun", T.KW_fun),
		  ("and", T.KW_and),
		  ("val", T.KW_val),
		  ("fn", T.KW_fn),
		  ("match", T.KW_match),
		  ("with", T.KW_with),
		  ("cases", T.KW_cases),
		  ("default", T.KW_default),
		  ("nocases", T.KW_nocases),
		  ("as", T.KW_as),
		  ("where", T.KW_where),
		  ("case", T.KW_case),
		  ("of", T.KW_of),
		  ("handling", T.KW_handling),
		  ("rehandling", T.KW_rehandling),
		  ("try", T.KW_try),
		  ("raise", T.KW_raise),
		  ("isnull", T.KW_isnull),
		  ("not", T.KW_not)]
		  
in
    fun idToken (t, p) =
	case List.find (fn (id, _) => id = t) idlist of
	    NONE => T.NAME (Symbol.atom t, p, p + size t)
	  | SOME (_, tok) => tok (p, p + size t)
end

val maxsmallnum = LiteralData.fromInt (getOpt (Int.maxInt, 0xffff))

%%
%s COMMENT STRING;
%header (functor MLPolyRLexFun (structure Tokens: MLPolyR_TOKENS));
%arg ({ enterC, leaveC, newS, addS, getS, handleEof, newline, error });

letter=[a-zA-Z];
letdig=[a-zA-Z0-9_'];
digit=[0-9];
white=[\ \t\r\f];


%%

<COMMENT>"(*"    =>  (enterC (); continue ());
<COMMENT>"*)"    =>  (if leaveC () then YYBEGIN INITIAL else (); continue ());
<COMMENT>"\n"    =>  (newline yypos; continue ());
<COMMENT>.       =>  (continue ());
<INITIAL>"(*"    => (YYBEGIN COMMENT; enterC (); continue ());
<INITIAL>"*)"    => (error (yypos, yypos + 2) "unmatched comment delimiter";
		     continue ());
<INITIAL>{letter}{letdig}* => (idToken (yytext, yypos));
<INITIAL>"_"     => (T.WILD (yypos, yypos + 1));
<INITIAL>"("     => (T.LP (yypos, yypos + 1));
<INITIAL>")"     => (T.RP (yypos, yypos + 1));
<INITIAL>"{"     => (T.LCB (yypos, yypos + 1));
<INITIAL>"}"     => (T.RCB (yypos, yypos + 1));
<INITIAL>"["     => (T.LSB (yypos, yypos + 1));
<INITIAL>"]"     => (T.RSB (yypos, yypos + 1));
<INITIAL>"{|"    => (T.LCBB (yypos, yypos + 2));
<INITIAL>"|}"    => (T.RCBB (yypos, yypos + 2));
<INITIAL>"=="    => (T.DEQ (yypos, yypos + 2));
<INITIAL>"<="    => (T.LTEQ (yypos, yypos + 2));
<INITIAL>"<"     => (T.LT (yypos, yypos + 1));
<INITIAL>">="    => (T.GTEQ (yypos, yypos + 2));
<INITIAL>">"     => (T.GT (yypos, yypos + 1));
<INITIAL>"<>"    => (T.NEQ (yypos, yypos + 2));
<INITIAL>"::"    => (T.DCOLON (yypos, yypos + 1));
<INITIAL>"+"     => (T.PLUS (yypos, yypos + 1));
<INITIAL>"-"     => (T.MINUS (yypos, yypos + 1));
<INITIAL>"*"     => (T.TIMES (yypos, yypos + 1));
<INITIAL>"/"     => (T.DIV (yypos, yypos + 1));
<INITIAL>"%"     => (T.MOD (yypos, yypos + 1));
<INITIAL>"="     => (T.EQ (yypos, yypos + 1));
<INITIAL>"."     => (T.DOT (yypos, yypos + 1));
<INITIAL>","     => (T.COMMA (yypos, yypos + 1));
<INITIAL>";"     => (T.SEMI (yypos, yypos + 1));
<INITIAL>"!"     => (T.EXCLAM (yypos, yypos + 1));
<INITIAL>"`"     => (T.BQ (yypos, yypos + 1));
<INITIAL>"++"    => (T.PLUSPLUS (yypos, yypos + 2));
<INITIAL>":="    => (T.ASSIGN (yypos, yypos + 2));
<INITIAL>"|"     => (T.BAR (yypos, yypos + 1));
<INITIAL>"=>"    => (T.DARROW (yypos, yypos + 2));
<INITIAL>":"     => (T.COLON (yypos, yypos + 1));
<INITIAL>"..."   => (T.DOTDOTDOT (yypos, yypos + 3));
<INITIAL>{digit}+ => (let val n = valOf (LiteralData.fromString yytext)
			  val st = yypos val en = yypos + size yytext
		      in if 1 <= n andalso n <= maxsmallnum then
			     T.SMALLNUM (LiteralData.toInt n, st, en)
			 else T.NUMBER (n, st, en)
		      end
		      handle _ => (error (yypos, yypos + size yytext)
					 "integer literal too large";
				   continue ()));
<INITIAL>\n      => (newline yypos; continue ());
<INITIAL>{white} => (continue ());
<INITIAL>"\""    => (YYBEGIN STRING; newS yypos; continue ());
<STRING>"\\n"    =>  (addS #"\n"; continue ());
<STRING>"\\t"    =>  (addS #"\t"; continue ());
<STRING>"\\\""   =>  (addS #"\""; continue ());
<STRING>"\\\\"   =>  (addS #"\\"; continue ());
<STRING>"\\".    => (error (yypos, yypos+1)
		      ("illegal escape character in STRING " ^ yytext);
		     continue ());
<STRING>"\""     => (YYBEGIN INITIAL; T.STRING (getS yypos));
<STRING>\n       => (error (yypos, yypos+1) "illegal linebreak in STRING";
		     continue ());
<STRING>.        => (addS (String.sub (yytext, 0)); continue ());
<INITIAL>.       => (error (yypos, yypos)
		      ("illegal character " ^ yytext);
		      continue ());
