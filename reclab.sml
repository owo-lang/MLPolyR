(* reclab.sml
 *
 *   Representing MLPolyR record labels.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure RecordLabel = struct

    type symbol = Symbol.atom

    datatype label =
	SYMlab of symbol
      | NUMlab of int
      | LENlab

    fun compare (NUMlab i, NUMlab i') = Int.compare (i, i')
      | compare (LENlab, LENlab) = EQUAL
      | compare (_, LENlab) = LESS
      | compare (LENlab, _) = GREATER
      | compare (NUMlab _, SYMlab _) = LESS
      | compare (SYMlab _, NUMlab _) = GREATER
      | compare (SYMlab s, SYMlab s') = Symbol.lexCompare (s, s')

    fun same (NUMlab i, NUMlab i') = i = i'
      | same (SYMlab s, SYMlab s') = Symbol.sameAtom (s, s')
      | same (LENlab, LENlab) = true
      | same _ = false

    fun sameField ((l, _), (l', _)) = same (l, l')

    fun gt (l, l') = compare (l, l') = GREATER

    fun sameAs l l' = same (l, l')
    fun sameFieldAs f f' = sameField (f, f')
    fun hasLab l (l', _) = same (l, l')

    fun toString (NUMlab i) = Int.toString i
      | toString (SYMlab s) = Symbol.toString s
      | toString LENlab = "$len"

    structure Set = RedBlackSetFn
			(type ord_key = label val compare = compare)

    fun toSet sel l = Set.addList (Set.empty, map sel l)
    fun sortBy sel l = ListMergeSort.sort (fn (x, y) => gt (sel x, sel y)) l

    structure Map = RedBlackMapFn
			(type ord_key = label val compare = compare)

    fun map2set m =
	Map.foldli (fn (l, _, s) => Set.add (s, l)) Set.empty m

    fun toMap (ksel, rsel) l =
	foldl (fn (x, m) => Map.insert (m, ksel x, rsel x)) Map.empty l
end
