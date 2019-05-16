signature MLPolyR_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val PLUSPLUS:  'a * 'a -> (svalue,'a) token
val BQ:  'a * 'a -> (svalue,'a) token
val DOTDOTDOT:  'a * 'a -> (svalue,'a) token
val WILD:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val DARROW:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val ASSIGN:  'a * 'a -> (svalue,'a) token
val EXCLAM:  'a * 'a -> (svalue,'a) token
val SEMI:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val DOT:  'a * 'a -> (svalue,'a) token
val EQ:  'a * 'a -> (svalue,'a) token
val MOD:  'a * 'a -> (svalue,'a) token
val DIV:  'a * 'a -> (svalue,'a) token
val TIMES:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val DCOLON:  'a * 'a -> (svalue,'a) token
val NEQ:  'a * 'a -> (svalue,'a) token
val GT:  'a * 'a -> (svalue,'a) token
val GTEQ:  'a * 'a -> (svalue,'a) token
val LT:  'a * 'a -> (svalue,'a) token
val LTEQ:  'a * 'a -> (svalue,'a) token
val DEQ:  'a * 'a -> (svalue,'a) token
val RSB:  'a * 'a -> (svalue,'a) token
val LSB:  'a * 'a -> (svalue,'a) token
val RCBB:  'a * 'a -> (svalue,'a) token
val LCBB:  'a * 'a -> (svalue,'a) token
val RCB:  'a * 'a -> (svalue,'a) token
val LCB:  'a * 'a -> (svalue,'a) token
val RP:  'a * 'a -> (svalue,'a) token
val LP:  'a * 'a -> (svalue,'a) token
val KW_not:  'a * 'a -> (svalue,'a) token
val KW_isnull:  'a * 'a -> (svalue,'a) token
val KW_raise:  'a * 'a -> (svalue,'a) token
val KW_rehandling:  'a * 'a -> (svalue,'a) token
val KW_handling:  'a * 'a -> (svalue,'a) token
val KW_try:  'a * 'a -> (svalue,'a) token
val KW_of:  'a * 'a -> (svalue,'a) token
val KW_case:  'a * 'a -> (svalue,'a) token
val KW_where:  'a * 'a -> (svalue,'a) token
val KW_as:  'a * 'a -> (svalue,'a) token
val KW_nocases:  'a * 'a -> (svalue,'a) token
val KW_default:  'a * 'a -> (svalue,'a) token
val KW_cases:  'a * 'a -> (svalue,'a) token
val KW_with:  'a * 'a -> (svalue,'a) token
val KW_match:  'a * 'a -> (svalue,'a) token
val KW_fn:  'a * 'a -> (svalue,'a) token
val KW_val:  'a * 'a -> (svalue,'a) token
val KW_and:  'a * 'a -> (svalue,'a) token
val KW_fun:  'a * 'a -> (svalue,'a) token
val KW_end:  'a * 'a -> (svalue,'a) token
val KW_in:  'a * 'a -> (svalue,'a) token
val KW_let:  'a * 'a -> (svalue,'a) token
val KW_true:  'a * 'a -> (svalue,'a) token
val KW_false:  'a * 'a -> (svalue,'a) token
val KW_else:  'a * 'a -> (svalue,'a) token
val KW_then:  'a * 'a -> (svalue,'a) token
val KW_if:  'a * 'a -> (svalue,'a) token
val KW_orelse:  'a * 'a -> (svalue,'a) token
val KW_andalso:  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val SMALLNUM: (int) *  'a * 'a -> (svalue,'a) token
val NUMBER: (Ast.integer) *  'a * 'a -> (svalue,'a) token
val NAME: (Ast.symbol) *  'a * 'a -> (svalue,'a) token
end
signature MLPolyR_LRVALS=
sig
structure Tokens : MLPolyR_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
