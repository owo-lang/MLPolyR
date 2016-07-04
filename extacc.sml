(* extacc.sml
 *
 *   Generating code that facilitates access to run-time system
 *   functionality.
 *
 * Copyright (C) 2006 by Matthias Blume (blume@tti-c.org)
 *)
structure ExternalAccess : sig

    val access : string -> Lambda.exp

end = struct

    fun access s =
	let val lab = Label.external s
	in Lambda.ARITH (Oper.PLUS, Lambda.VALUE (Lambda.LABEL lab),
			            Lambda.VALUE (Lambda.INT 1))
	end
end
