(* ast.sml
 *
 *   MLPolyR's Abstract Syntax Trees.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Ast = struct

    type symbol = Symbol.atom
    type integer = LiteralData.integer
    type cmpop = Oper.cmpop
    type arithop = Oper.arithop

    type pos = int
    type region = pos * pos

    type mlabel = RecordLabel.label * region (* marked label *)

    datatype boolconn =
	ANDALSO
      | ORELSE

    datatype binop =
	BOOLCONN of boolconn
      | CMP of cmpop
      | ARITH of arithop
      | CONS

    datatype uop =
	UMINUS
      | ISNULL
      | NOT

    datatype exp =
	LETexp of def list * exp
      | IFexp of exp * exp * exp
      | CASEexp of exp * dtmatch
      | WHEREexp of Purity.purity * exp * exp field list
      | BINOPexp of binop * exp * exp
      | UOPexp of uop * exp
      | APPexp of exp * exp
      | ASSIGNexp of exp * mlabel * exp
      | SELexp of Purity.purity * exp * mlabel
      | BOOLexp of bool
      | NUMBERexp of integer
      | STRINGexp of string
      | VARexp of symbol
      | SEQexp of exp list
      | LISTexp of exp list
      | RECORDexp of Purity.purity * exp field list
      | TUPLEexp of exp list
      | MATCHexp of mrule list * exp option
      | CONexp of mlabel * exp
      | SWIDENexp of exp * mlabel
      | PSCASEexp of exp * exp	(* polymorphic sum case *)
      | FNexp of lambda
      | RAISEexp of exp
      | TRYexp of { scrutinee: exp, success: lambda,
		    handling: mrule list,
		    rehandling: mrule list,
		    (* nothandling: mlabel list,
		     *     -- rely on encoding via catchall, widen, and raise *)
		    catchall: lambda option }
      | MARKexp of exp * region

    and def =
	VALdef of pat * exp
      | FUNdef of function list * reccases list * region

    and function = FUN of symbol * pat list * exp * region

    and reccases = RC of symbol * exp * region

    and pat =
	WILDpat
      | VARpat of symbol
      | TUPLEpat of pat list
      | RECORDpat of Purity.purity * pat field list
      | MATCHpat of pat field list
      | ANDpat of pat * pat
      | MARKpat of pat * region

    withtype 'a field = (* NONE means "..." *)
	mlabel option * 'a

    and lambda = pat * exp

    and dtmatch = { nilcase: exp, conscase: pat * pat * exp }

    and mrule = mlabel * lambda * region

    type program = exp * region

    fun isSynVal (LETexp (dl, e)) = List.all isSynDef dl andalso isSynVal e
      | isSynVal (IFexp (e, e', e'')) =
	  isSynVal e andalso isSynVal e' andalso isSynVal e''
      | isSynVal (WHEREexp (Purity.Pure, e, fl)) =
	  isSynVal e andalso List.all isSynField fl
      | isSynVal (WHEREexp (Purity.Impure, _, _)) = false
      | isSynVal (BINOPexp (BOOLCONN _, e, e')) = isSynVal e andalso isSynVal e'
      | isSynVal (BINOPexp (CMP _, e, e')) = isSynVal e andalso isSynVal e'
      | isSynVal (BINOPexp (ARITH _, _, _)) = false
      | isSynVal (BINOPexp (CONS, e, e')) = isSynVal e andalso isSynVal e'
      | isSynVal (UOPexp ((ISNULL | NOT), e)) = isSynVal e
      | isSynVal (UOPexp (UMINUS, _)) = false
      | isSynVal (APPexp _) = false
      | isSynVal (ASSIGNexp _) = false
      | isSynVal (SELexp (Purity.Pure, e, _)) = isSynVal e
      | isSynVal (SELexp (Purity.Impure, _, _)) = false
      | isSynVal (BOOLexp _) = true
      | isSynVal (NUMBERexp _) = true
      | isSynVal (STRINGexp _) = true
      | isSynVal (VARexp _) = true
      | isSynVal (SEQexp el) = List.all isSynVal el
      | isSynVal (LISTexp el) = List.all isSynVal el
      | isSynVal (RECORDexp (Purity.Pure, fl)) = List.all isSynField fl
      | isSynVal (RECORDexp (Purity.Impure, _)) = false
      | isSynVal (MATCHexp (_, NONE)) = true
      | isSynVal (MATCHexp (_, SOME e)) = isSynVal e
      | isSynVal (TUPLEexp el) = List.all isSynVal el
      | isSynVal (CASEexp (e, { nilcase, conscase = (_, _, cc) })) =
	  isSynVal e andalso isSynVal nilcase andalso isSynVal cc
      | isSynVal (CONexp (_, e)) = isSynVal e
      | isSynVal (SWIDENexp (e, _)) = isSynVal e
      | isSynVal (FNexp _) = true
      | isSynVal (PSCASEexp _) = false
      | isSynVal (TRYexp _) = false
      | isSynVal (RAISEexp _) = false
      | isSynVal (MARKexp (e, _)) = isSynVal e

    and isSynDef (VALdef (_, e)) = isSynVal e
      | isSynDef (FUNdef _) = true

    and isSynField (_, e) = isSynVal e
end
