(* tvar.sml
 *
 * A "ref" type with an ordering relation (so that one can define
 * maps and sets of refs) for representing type- and rowtype variables.
 * 
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure TVar :> sig

    type 'a tvar
    type 'a rvar

    val tvar : 'a -> 'a tvar
    val rvar : 'a -> 'a rvar

    val tget : 'a tvar -> 'a
    val rget : 'a rvar -> 'a

    val tset : 'a tvar * 'a -> unit
    val rset : 'a rvar * 'a -> unit

    val teq : 'a tvar * 'a tvar -> bool
    val req : 'a rvar * 'a rvar -> bool

    val tcompare : 'a tvar * 'a tvar -> order (* not stable across link *)
    val rcompare : 'a rvar * 'a rvar -> order

    val reset : unit -> unit

    val link : 'a tvar * 'a tvar -> bool (* false if they were already equqal *)

end = struct

    type 'a tvar = ('a * int) URef.uref
    type 'a rvar = 'a ref * int

    val tnext = ref 0
    val rnext = ref 0

    fun reset () = (tnext := 0; rnext := 0)

    fun tvar x =
	let val i = !tnext
	in tnext := i+1;
	   URef.uRef (x, i)
	end
    fun rvar x =
	let val i = !rnext
	in rnext := i+1;
	   (ref x, i)
	end

    fun tget (v: 'a tvar) = #1 (URef.!! v)
    fun rget (rv: 'a rvar) = !(#1 rv)

    fun tid (v: 'a tvar) = #2 (URef.!! v)

    fun tset (v, x) = URef.update (v, (x, tid v))
    fun rset ((r, _), x) = r := x

    fun teq (v, w) = URef.equal (v, w)
    fun req ((_, i): 'a rvar, (_, j)) = i = j

    fun tcompare (v, w) = Int.compare (tid v, tid w)
    fun rcompare ((_, i), (_, j)) = Int.compare (i, j)

    fun link (v, w) = URef.link (v, w)
end
