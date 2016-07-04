(* types.sml
 *
 *   ML types of data structures representing MLPolyR types.
 *
 * Copyright (c) 2006 by Matthias Blume (blume@tti-c.org)
 *)
structure Types = struct

    type region = Ast.region

    type label = RecordLabel.label
    type depth = int

    type exclusion = region RecordLabel.Map.map

    datatype tycon =
	INTtyc
      | BOOLtyc
      | STRINGtyc
      | FUNtyc
      | MATCHtyc
      | LISTtyc
      | RECORDtyc of Purity.purity
      | SUMtyc

    (* fields: *)

    type 'a field = label * ('a * region)

    (* types: *)

    datatype typ =
	VARty of tyvar
      | CONty of tycon * typ list * rtyp list * region

    and tyvarval =
	INST of typ
      | OPEN of depth * region

    and rtyp =
	VARrty of rtyvar
      | EMPTYrty of region
      | FIELDrty of typ field * rtyp

    and rtyvarval =
	RINST of rtyp
      |	ROPEN of depth * rtyvarkind * region

    withtype tyvar = tyvarval TVar.tvar
    and rtyvar = rtyvarval TVar.rvar

    and rtyvarkind = exclusion

    (* type schemas: *)

    type tsvar = int		(* bound type in type schemas *)
    type rtsvar = int		(* bound row type variable in type schema *)

    datatype typs =
	PLAINtys of typ
      | CONtys of tycon * typs list * rtyps list * region
      | MUtys of tsvar * typs * region
      | REFtys of tsvar

    and rtyps =
	VARrtys of rtyvar
      | EMPTYrtys of region
      | FIELDrtys of typs field * rtyps
      | REFrtys of rtsvar

    type typschema = { targs: int, rargs: rtyvarkind list, body: typs }


    (* sets and maps of row variables: *)

    (* TSet and TMap do not work across TVar.link operations
     * on their keys! *)
    structure TSet = RedBlackSetFn (type ord_key = tyvar
                                    val compare = TVar.tcompare)
    structure TMap = RedBlackMapFn (type ord_key = tyvar
                                    val compare = TVar.tcompare)
    structure RTSet = RedBlackSetFn (type ord_key = rtyvar
                                     val compare = TVar.rcompare)
    structure RTMap = RedBlackMapFn (type ord_key = rtyvar
                                     val compare = TVar.rcompare)

    (* poly row info: *)

    type pri_rtyvarkind = RecordLabel.Set.set
    type pri = (rtyvar * pri_rtyvarkind) list (* polymorphic row info *)

    type prepolytype = typ * pri	(* old row type vars *)

    (* utility functions: *) 

    fun INTty r = CONty (INTtyc, [], [], r)
    fun BOOLty r = CONty (BOOLtyc, [], [], r)
    fun STRINGty r = CONty (STRINGtyc, [], [], r)
    fun FUNty (t1, t2, ert, r) = CONty (FUNtyc, [t1, t2], [ert], r)
    fun FUNtys (ts1, ts2, erts, r) = CONtys (FUNtyc, [ts1, ts2], [erts], r)
    fun MATCHty (rt, t, ert, r) = CONty (MATCHtyc, [t], [rt, ert], r)
    fun LISTty (t, r) = CONty (LISTtyc, [t], [], r)
    fun RECORDty (p, rt, r) = CONty (RECORDtyc p, [], [rt], r)
    fun SUMty (rt, r) = CONty (SUMtyc, [], [rt], r)
    fun UNITty r = RECORDty (Purity.Pure, EMPTYrty r, r)

    fun TUPLEty (tl, r) =
	RECORDty (Purity.Pure,
		  #1 (foldl (fn ((t, fr), (rt, i)) =>
				(FIELDrty ((RecordLabel.NUMlab i, (t, r)),
					   rt),
				 i+1))
			    (EMPTYrty r, 1)
			    tl),
		  r)

    fun sameTyc (t: tycon, t') = t = t'

    fun regionOf (VARty v) =
	  (case TVar.tget v of
	       INST t => regionOf t
	     | OPEN (_, r) => r)
      | regionOf (CONty (_, _, _, r)) = r

    fun rregionOf (VARrty v) =
	  (case TVar.rget v of
	       RINST rt => rregionOf rt
	     | ROPEN (_, _, r) => r)
      | rregionOf (EMPTYrty r) = r
      | rregionOf (FIELDrty ((_, (_, r)), _)) = r

    val unconstrained : rtyvarkind = RecordLabel.Map.empty
end
