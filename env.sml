(* env.sml
 *
 *   The functional environment data structure used by the elaborator.
 *
 * Copyright (c) 2005 by Matthias Blume (blume@tti-c.org)
 *)
structure Env :> sig

    type 'a env

    val empty : 'a env
    val bind : Symbol.atom * 'a * 'a env -> 'a env
    val find : 'a env * Symbol.atom -> 'a option
    val map : ('a -> 'b) -> 'a env -> 'b env

end = struct

    structure M = Symbol.Map

    type 'a env = 'a M.map

    val empty = M.empty
    fun bind (v, x, e) = M.insert (e, v, x)
    fun find (e, v) = M.find (e, v)
    fun map f e = M.map f e

end
