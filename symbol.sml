(* symbol.sml
 *
 *   Using atoms as symbols (but don't confuse the symbol type with
 *   the atom type).
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Symbol :> sig
    include ATOM
    structure Map : ORD_MAP where type Key.ord_key = atom
    structure Set : ORD_SET where type Key.ord_key = atom
end = struct
    open Atom
    structure Set = AtomRedBlackSet
    structure Map = AtomRedBlackMap
end
