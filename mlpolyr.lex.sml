(*#line 75.10 "mlpolyr.lex"*)functor MLPolyRLexFun (structure Tokens: MLPolyR_TOKENS)(*#line 1.1 "mlpolyr.lex.sml"*)
=
   struct
    structure UserDeclarations =
      struct
(*#line 1.1 "mlpolyr.lex"*)(* -*- sml-lex -*-
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

(*#line 78.1 "mlpolyr.lex.sml"*)
end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\007\007\007\007\007\007\007\007\007\050\051\007\007\050\007\007\
\\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\
\\050\049\048\007\007\047\007\007\045\044\042\040\039\038\035\034\
\\032\032\032\032\032\032\032\032\032\032\029\028\025\022\020\007\
\\007\013\013\013\013\013\013\013\013\013\013\013\013\013\013\013\
\\013\013\013\013\013\013\013\013\013\013\013\019\007\018\007\017\
\\016\013\013\013\013\013\015\013\013\013\013\013\013\013\013\013\
\\013\013\013\013\013\013\013\013\013\013\013\011\009\008\007\007\
\\007"
),
 (3, 
"\052\052\052\052\052\052\052\052\052\052\057\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\055\052\053\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\052\
\\052"
),
 (5, 
"\058\058\058\058\058\058\058\058\058\058\066\058\058\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058\058\065\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\059\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\058\
\\058"
),
 (9, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\000\
\\000"
),
 (11, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\012\000\000\000\
\\000"
),
 (13, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\014\000\000\000\000\000\000\000\000\
\\014\014\014\014\014\014\014\014\014\014\000\000\000\000\000\000\
\\000\014\014\014\014\014\014\014\014\014\014\014\014\014\014\014\
\\014\014\014\014\014\014\014\014\014\014\014\000\000\000\000\014\
\\000\014\014\014\014\014\014\014\014\014\014\014\014\014\014\014\
\\014\014\014\014\014\014\014\014\014\014\014\000\000\000\000\000\
\\000"
),
 (20, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\021\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (22, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\024\023\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (25, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\027\026\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (29, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\031\000\000\030\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (32, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\033\033\033\033\033\033\033\033\033\033\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (35, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\036\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (36, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\037\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (40, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\041\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (42, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\043\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (45, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (53, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\054\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (55, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\056\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (59, 
"\060\060\060\060\060\060\060\060\060\060\000\060\060\060\060\060\
\\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\
\\060\060\064\060\060\060\060\060\060\060\060\060\060\060\060\060\
\\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\
\\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\060\
\\060\060\060\060\060\060\060\060\060\060\060\060\063\060\060\060\
\\060\060\060\060\060\060\060\060\060\060\060\060\060\060\062\060\
\\060\060\060\060\061\060\060\060\060\060\060\060\060\060\060\060\
\\060"
),
(0, "")]
fun f x = x 
val s = List.map f (List.rev (tl (List.rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i: int) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(List.map g 
[{fin = [], trans = 0},
{fin = [], trans = 1},
{fin = [], trans = 1},
{fin = [], trans = 3},
{fin = [], trans = 3},
{fin = [], trans = 5},
{fin = [], trans = 5},
{fin = [(N 128)], trans = 0},
{fin = [(N 28),(N 128)], trans = 0},
{fin = [(N 87),(N 128)], trans = 9},
{fin = [(N 38)], trans = 0},
{fin = [(N 26),(N 128)], trans = 11},
{fin = [(N 35)], trans = 0},
{fin = [(N 18),(N 128)], trans = 13},
{fin = [(N 18)], trans = 13},
{fin = [(N 18),(N 103),(N 128)], trans = 13},
{fin = [(N 79),(N 128)], trans = 0},
{fin = [(N 20),(N 128)], trans = 0},
{fin = [(N 32),(N 128)], trans = 0},
{fin = [(N 30),(N 128)], trans = 0},
{fin = [(N 51),(N 128)], trans = 20},
{fin = [(N 49)], trans = 0},
{fin = [(N 69),(N 128)], trans = 22},
{fin = [(N 90)], trans = 0},
{fin = [(N 41)], trans = 0},
{fin = [(N 46),(N 128)], trans = 25},
{fin = [(N 54)], trans = 0},
{fin = [(N 44)], trans = 0},
{fin = [(N 75),(N 128)], trans = 0},
{fin = [(N 92),(N 128)], trans = 29},
{fin = [(N 85)], trans = 0},
{fin = [(N 57)], trans = 0},
{fin = [(N 99),(N 128)], trans = 32},
{fin = [(N 99)], trans = 32},
{fin = [(N 65),(N 128)], trans = 0},
{fin = [(N 71),(N 128)], trans = 35},
{fin = [], trans = 36},
{fin = [(N 96)], trans = 0},
{fin = [(N 61),(N 128)], trans = 0},
{fin = [(N 73),(N 128)], trans = 0},
{fin = [(N 59),(N 128)], trans = 40},
{fin = [(N 82)], trans = 0},
{fin = [(N 63),(N 128)], trans = 42},
{fin = [(N 15)], trans = 0},
{fin = [(N 24),(N 128)], trans = 0},
{fin = [(N 22),(N 128)], trans = 45},
{fin = [(N 12)], trans = 0},
{fin = [(N 67),(N 128)], trans = 0},
{fin = [(N 105),(N 128)], trans = 0},
{fin = [(N 77),(N 128)], trans = 0},
{fin = [(N 103),(N 128)], trans = 0},
{fin = [(N 101)], trans = 0},
{fin = [(N 9)], trans = 0},
{fin = [(N 9)], trans = 53},
{fin = [(N 5)], trans = 0},
{fin = [(N 9)], trans = 55},
{fin = [(N 2)], trans = 0},
{fin = [(N 7)], trans = 0},
{fin = [(N 126)], trans = 0},
{fin = [(N 126)], trans = 59},
{fin = [(N 120)], trans = 0},
{fin = [(N 111),(N 120)], trans = 0},
{fin = [(N 108),(N 120)], trans = 0},
{fin = [(N 117),(N 120)], trans = 0},
{fin = [(N 114),(N 120)], trans = 0},
{fin = [(N 122),(N 126)], trans = 0},
{fin = [(N 124)], trans = 0}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val COMMENT = STARTSTATE 3;
val INITIAL = STARTSTATE 1;
val STRING = STARTSTATE 5;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

structure YYPosInt : INTEGER = Int
fun makeLexer yyinput =
let	val yygone0= YYPosInt.fromInt ~1
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex (yyarg as ((*#line 76.7 "mlpolyr.lex"*){ enterC, leaveC, newS, addS, getS, handleEof, newline, error }(*#line 413.1 "mlpolyr.lex.sml"*)
)) =
let fun continue() : Internal.result = 
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = String.substring(!yyb,i0,i-i0)
			     val yypos = YYPosInt.+(YYPosInt.fromInt i0, !yygone)
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  101 => ((*#line 136.22 "mlpolyr.lex"*)newline yypos; continue ()(*#line 429.1 "mlpolyr.lex.sml"*)
)
| 103 => ((*#line 137.22 "mlpolyr.lex"*)continue ()(*#line 431.1 "mlpolyr.lex.sml"*)
)
| 105 => ((*#line 138.22 "mlpolyr.lex"*)YYBEGIN STRING; newS yypos; continue ()(*#line 433.1 "mlpolyr.lex.sml"*)
)
| 108 => ((*#line 139.23 "mlpolyr.lex"*)addS #"\n"; continue ()(*#line 435.1 "mlpolyr.lex.sml"*)
)
| 111 => ((*#line 140.23 "mlpolyr.lex"*)addS #"\t"; continue ()(*#line 437.1 "mlpolyr.lex.sml"*)
)
| 114 => ((*#line 141.23 "mlpolyr.lex"*)addS #"\""; continue ()(*#line 439.1 "mlpolyr.lex.sml"*)
)
| 117 => ((*#line 142.23 "mlpolyr.lex"*)addS #"\\"; continue ()(*#line 441.1 "mlpolyr.lex.sml"*)
)
| 12 => ((*#line 90.22 "mlpolyr.lex"*)YYBEGIN COMMENT; enterC (); continue ()(*#line 443.1 "mlpolyr.lex.sml"*)
)
| 120 => let val yytext=yymktext() in (*#line 143.22 "mlpolyr.lex"*)error (yypos, yypos+1)
		      ("illegal escape character in STRING " ^ yytext);
		     continue ()(*#line 447.1 "mlpolyr.lex.sml"*)
 end
| 122 => ((*#line 146.22 "mlpolyr.lex"*)YYBEGIN INITIAL; T.STRING (getS yypos)(*#line 449.1 "mlpolyr.lex.sml"*)
)
| 124 => ((*#line 147.22 "mlpolyr.lex"*)error (yypos, yypos+1) "illegal linebreak in STRING";
		     continue ()(*#line 452.1 "mlpolyr.lex.sml"*)
)
| 126 => let val yytext=yymktext() in (*#line 149.22 "mlpolyr.lex"*)addS (String.sub (yytext, 0)); continue ()(*#line 454.1 "mlpolyr.lex.sml"*)
 end
| 128 => let val yytext=yymktext() in (*#line 150.22 "mlpolyr.lex"*)error (yypos, yypos)
		      ("illegal character " ^ yytext);
		      continue ()(*#line 458.1 "mlpolyr.lex.sml"*)
 end
| 15 => ((*#line 91.22 "mlpolyr.lex"*)error (yypos, yypos + 2) "unmatched comment delimiter";
		     continue ()(*#line 461.1 "mlpolyr.lex.sml"*)
)
| 18 => let val yytext=yymktext() in (*#line 93.32 "mlpolyr.lex"*)idToken (yytext, yypos)(*#line 463.1 "mlpolyr.lex.sml"*)
 end
| 2 => ((*#line 86.23 "mlpolyr.lex"*)enterC (); continue ()(*#line 465.1 "mlpolyr.lex.sml"*)
)
| 20 => ((*#line 94.22 "mlpolyr.lex"*)T.WILD (yypos, yypos + 1)(*#line 467.1 "mlpolyr.lex.sml"*)
)
| 22 => ((*#line 95.22 "mlpolyr.lex"*)T.LP (yypos, yypos + 1)(*#line 469.1 "mlpolyr.lex.sml"*)
)
| 24 => ((*#line 96.22 "mlpolyr.lex"*)T.RP (yypos, yypos + 1)(*#line 471.1 "mlpolyr.lex.sml"*)
)
| 26 => ((*#line 97.22 "mlpolyr.lex"*)T.LCB (yypos, yypos + 1)(*#line 473.1 "mlpolyr.lex.sml"*)
)
| 28 => ((*#line 98.22 "mlpolyr.lex"*)T.RCB (yypos, yypos + 1)(*#line 475.1 "mlpolyr.lex.sml"*)
)
| 30 => ((*#line 99.22 "mlpolyr.lex"*)T.LSB (yypos, yypos + 1)(*#line 477.1 "mlpolyr.lex.sml"*)
)
| 32 => ((*#line 100.22 "mlpolyr.lex"*)T.RSB (yypos, yypos + 1)(*#line 479.1 "mlpolyr.lex.sml"*)
)
| 35 => ((*#line 101.22 "mlpolyr.lex"*)T.LCBB (yypos, yypos + 2)(*#line 481.1 "mlpolyr.lex.sml"*)
)
| 38 => ((*#line 102.22 "mlpolyr.lex"*)T.RCBB (yypos, yypos + 2)(*#line 483.1 "mlpolyr.lex.sml"*)
)
| 41 => ((*#line 103.22 "mlpolyr.lex"*)T.DEQ (yypos, yypos + 2)(*#line 485.1 "mlpolyr.lex.sml"*)
)
| 44 => ((*#line 104.22 "mlpolyr.lex"*)T.LTEQ (yypos, yypos + 2)(*#line 487.1 "mlpolyr.lex.sml"*)
)
| 46 => ((*#line 105.22 "mlpolyr.lex"*)T.LT (yypos, yypos + 1)(*#line 489.1 "mlpolyr.lex.sml"*)
)
| 49 => ((*#line 106.22 "mlpolyr.lex"*)T.GTEQ (yypos, yypos + 2)(*#line 491.1 "mlpolyr.lex.sml"*)
)
| 5 => ((*#line 87.23 "mlpolyr.lex"*)if leaveC () then YYBEGIN INITIAL else (); continue ()(*#line 493.1 "mlpolyr.lex.sml"*)
)
| 51 => ((*#line 107.22 "mlpolyr.lex"*)T.GT (yypos, yypos + 1)(*#line 495.1 "mlpolyr.lex.sml"*)
)
| 54 => ((*#line 108.22 "mlpolyr.lex"*)T.NEQ (yypos, yypos + 2)(*#line 497.1 "mlpolyr.lex.sml"*)
)
| 57 => ((*#line 109.22 "mlpolyr.lex"*)T.DCOLON (yypos, yypos + 1)(*#line 499.1 "mlpolyr.lex.sml"*)
)
| 59 => ((*#line 110.22 "mlpolyr.lex"*)T.PLUS (yypos, yypos + 1)(*#line 501.1 "mlpolyr.lex.sml"*)
)
| 61 => ((*#line 111.22 "mlpolyr.lex"*)T.MINUS (yypos, yypos + 1)(*#line 503.1 "mlpolyr.lex.sml"*)
)
| 63 => ((*#line 112.22 "mlpolyr.lex"*)T.TIMES (yypos, yypos + 1)(*#line 505.1 "mlpolyr.lex.sml"*)
)
| 65 => ((*#line 113.22 "mlpolyr.lex"*)T.DIV (yypos, yypos + 1)(*#line 507.1 "mlpolyr.lex.sml"*)
)
| 67 => ((*#line 114.22 "mlpolyr.lex"*)T.MOD (yypos, yypos + 1)(*#line 509.1 "mlpolyr.lex.sml"*)
)
| 69 => ((*#line 115.22 "mlpolyr.lex"*)T.EQ (yypos, yypos + 1)(*#line 511.1 "mlpolyr.lex.sml"*)
)
| 7 => ((*#line 88.23 "mlpolyr.lex"*)newline yypos; continue ()(*#line 513.1 "mlpolyr.lex.sml"*)
)
| 71 => ((*#line 116.22 "mlpolyr.lex"*)T.DOT (yypos, yypos + 1)(*#line 515.1 "mlpolyr.lex.sml"*)
)
| 73 => ((*#line 117.22 "mlpolyr.lex"*)T.COMMA (yypos, yypos + 1)(*#line 517.1 "mlpolyr.lex.sml"*)
)
| 75 => ((*#line 118.22 "mlpolyr.lex"*)T.SEMI (yypos, yypos + 1)(*#line 519.1 "mlpolyr.lex.sml"*)
)
| 77 => ((*#line 119.22 "mlpolyr.lex"*)T.EXCLAM (yypos, yypos + 1)(*#line 521.1 "mlpolyr.lex.sml"*)
)
| 79 => ((*#line 120.22 "mlpolyr.lex"*)T.BQ (yypos, yypos + 1)(*#line 523.1 "mlpolyr.lex.sml"*)
)
| 82 => ((*#line 121.22 "mlpolyr.lex"*)T.PLUSPLUS (yypos, yypos + 2)(*#line 525.1 "mlpolyr.lex.sml"*)
)
| 85 => ((*#line 122.22 "mlpolyr.lex"*)T.ASSIGN (yypos, yypos + 2)(*#line 527.1 "mlpolyr.lex.sml"*)
)
| 87 => ((*#line 123.22 "mlpolyr.lex"*)T.BAR (yypos, yypos + 1)(*#line 529.1 "mlpolyr.lex.sml"*)
)
| 9 => ((*#line 89.23 "mlpolyr.lex"*)continue ()(*#line 531.1 "mlpolyr.lex.sml"*)
)
| 90 => ((*#line 124.22 "mlpolyr.lex"*)T.DARROW (yypos, yypos + 2)(*#line 533.1 "mlpolyr.lex.sml"*)
)
| 92 => ((*#line 125.22 "mlpolyr.lex"*)T.COLON (yypos, yypos + 1)(*#line 535.1 "mlpolyr.lex.sml"*)
)
| 96 => ((*#line 126.22 "mlpolyr.lex"*)T.DOTDOTDOT (yypos, yypos + 3)(*#line 537.1 "mlpolyr.lex.sml"*)
)
| 99 => let val yytext=yymktext() in (*#line 127.23 "mlpolyr.lex"*)let val n = valOf (LiteralData.fromString yytext)
			  val st = yypos val en = yypos + size yytext
		      in if 1 <= n andalso n <= maxsmallnum then
			     T.SMALLNUM (LiteralData.toInt n, st, en)
			 else T.NUMBER (n, st, en)
		      end
		      handle _ => (error (yypos, yypos + size yytext)
					 "integer literal too large";
				   continue ())(*#line 547.1 "mlpolyr.lex.sml"*)
 end
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (String.size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof yyarg
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := String.substring(!yyb,i0,l-i0)^newchars;
		     yygone := YYPosInt.+(!yygone, YYPosInt.fromInt i0);
		     yybl := String.size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord(CharVector.sub(!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord(CharVector.sub(trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if String.substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
in continue end
  in lex
  end
end
