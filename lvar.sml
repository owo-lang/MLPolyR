(* lvar.sml
 *
 *   "Lambda Variables" -- generic temporaries used by Lamda-
 *   ANF-, and Tree-languages and also as Pseudo-registers in
 *   ASM code before register allocation.
 *
 *   Where possible we maintain a mapping from lvars to meaningful
 *   names (wrt. source code).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure LVar :> sig

    eqtype lvar
    type ord_key = lvar

    val compare : lvar * lvar -> order

    structure Set : ORD_SET where type Key.ord_key = ord_key
    structure Map : ORD_MAP where type Key.ord_key = ord_key

    val new : string -> lvar
    val clone : lvar -> lvar
    val toString : lvar -> string
    val baseName : lvar -> string
    val special : int * string -> lvar

    val dummy : lvar

    val reset : unit -> unit

end = struct

    fun bug m = ErrorMsg.impossible ("LVar: " ^ m)

    type lvar = int

    structure Set = IntRedBlackSet
    structure Map = IntRedBlackMap

    type ord_key = lvar
    val compare = Int.compare

    val minvar = 32

    val next = ref minvar
    val info : string Map.map ref = ref Map.empty

    fun reset () = (next := minvar; info := Map.empty)

    fun fresh () = let val n = !next in next := n+1; n end

    fun new name =
	let val v = fresh ()
	in info := Map.insert (!info, v, name); v end

    fun clone v =
	let val v' = fresh ()
	in case Map.find (!info, v) of
	       SOME name => info := Map.insert (!info, v', name)
	     | NONE => bug "no name recorded";
	   v'
	end

    fun baseName v =
	case Map.find (!info, v) of
	    SOME name => name
	  | NONE => bug "no name recorded"

    fun toString v = concat [baseName v, "_", Int.toString v]

    fun special (i, name) =
	if i >= 0 andalso i < minvar then
	    (info := Map.insert (!info, i, name); i)
	else raise bug ("bad special: " ^ Int.toString i)

    val dummy = ~1
end
