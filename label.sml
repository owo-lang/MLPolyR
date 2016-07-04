(* label.sml
 *
 *   Representing assembly labels in the MLPolyR compiler.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Label :> sig

    structure Atom : ATOM

    type label = Atom.atom

    structure Set : ORD_SET where type Key.ord_key = label
    structure Map : ORD_MAP where type Key.ord_key = label

    val new : LVar.lvar option -> label
    val external : string -> label
    val stringlabel : unit -> label

    val reset : unit -> unit

    val isExternal : label -> bool

    val name : label -> string
    val escname : label -> string

    val compare : label * label -> order

end = struct

    structure Atom = Atom

    structure Set = AtomRedBlackSet
    structure Map = AtomRedBlackMap

    type label = Atom.atom

    val next = ref 0
    val externals = ref Set.empty
    fun reset () = next := 0

    fun freshid () = let val n = !next in next := n+1; n end

    fun new NONE = Atom.atom ("l_" ^ Int.toString (freshid ()))
      | new (SOME v) = Atom.atom ("l_" ^ Int.toString (freshid ())
				  ^ "_" ^ LVar.baseName v)

    fun stringlabel () =
	Atom.atom ("l_mlpr_string_" ^ Int.toString (freshid ()))

    fun external s =
	let val l = Atom.atom ("_" ^ s)
	in externals := Set.add (!externals, l);
	   l
	end

    fun isExternal l = Set.member (!externals, l)

    val name = Atom.toString
    fun escname l =
	let val n = name l
	in if Char.contains n #"'" then concat ["\"", n, "\""] else n
	end

    val compare = Atom.compare
end
