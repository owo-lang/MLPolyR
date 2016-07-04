(* absyn.sml
 *
 *   MLPolyR Abstract Syntax (AST with type information).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Absyn = struct

    type symbol = Ast.symbol
    type integer = LiteralData.integer
    type typ = Types.typ
    type rtyp = Types.rtyp
    type prepolytype = Types.prepolytype
    type binop = Ast.binop
    type uop = Ast.uop
    type region = Ast.region

    datatype exp =
        LETexp of (def * Types.depth) list * exp
      | IFexp of exp * exp * exp * typ
      | LCASEexp of exp * exp * pat * pat * exp * typ
      | WHEREexp of Purity.purity * exp * typ * exp field list * typ
      | BINOPexp of binop * exp * exp * typ
      | UOPexp of uop * exp * typ
      | APPexp of exp * exp * typ
      | ASSIGNexp of exp * typ * RecordLabel.label * exp
      | SELexp of Purity.purity * exp * typ * RecordLabel.label * typ
      | BOOLexp of bool
      | NUMBERexp of integer
      | STRINGexp of string
      | UNITexp
      | VARexp of symbol * typ * Types.pri (* after generalization *)
      | SEQexp of exp * exp
      | LISTexp of exp list * typ
      | RECORDexp of Purity.purity * exp field list *
		     (exp * typ * exp field list) option * typ
      | CONexp of exp field * typ
      | SWIDENexp of exp * typ * RecordLabel.label * typ
      | PSCASEexp of exp * exp * typ
      | FNexp of pat * exp * typ
      | RAISEexp of exp * typ	(* type is "result" type *)
      | TRYexp of { scrutinee: exp, ert: rtyp,
		    success: pat * exp,
		    handling: (RecordLabel.label * pat * exp) list,
		    rehandling: (RecordLabel.label * pat * exp) list,
		    catchall: (pat * exp) option }
      | MARKexp of exp * region

    and def =
	VALdef of pat * Symbol.Set.set * exp
      | FUNdef of function list * Types.pri (* before gen. *) * reccases list

    and pat' =
	WILDpat
      | VARpat of symbol
      | RECORDpat of Purity.purity * pat field list * pat option * Types.pri
      | ANDpat of pat' * pat'
      | MARKpat of pat' * region

    withtype 'a field = RecordLabel.label * 'a

    and pat = pat' * prepolytype

    and function = { f: symbol, params: pat list, body: exp }

    and reccases = { c: symbol, ct: typ, rhs: exp }

    and rule = pat field * exp

    type program = exp

    fun TUPLEexp (el, t) =
	let fun loop ([], _, rfl) = RECORDexp (Purity.Pure, rev rfl, NONE, t)
	      | loop (e :: es, i, rfl) =
		  loop (es, i+1, (RecordLabel.NUMlab i, e) :: rfl)
	in loop (el, 1, [])
	end
end
