(*  uncurry.sml
 *
 *   ...
 *
 * Copyright (c) 2005 Matthias Blume (blume@tti-c.org)
 *)

(*

 FIX ([(f0, vl0,
	FIX ([(f1, vl1,
	       FIX ([(f2, vl2,
		      ...
			  FIX ([(fk, vlk,
				 e)],
			       fk) ...)],
		    f2))],
	     f1)),
       ...],
      ...)

=>

FIX ([(f, vl0 @ vl1 @ vl2 @ ... @ vlk,
       FIX ([header(1..k)],
	    FIX ([header(2..k)],
		 ...
		     FIX ([header(k..k)],
			  e) ...))),
      header(0..k),
      ...],
     ...)

  where

    header(i..k) =
       (fi, vli',
	    FIX ([(f{i+1}', vl{i+1}',
		   ...
		       FIX ([(fk', vlk',
			      f (vl0 @ ... @ vl{i-1} @
				 vli' @ vl{i+1}' @ ... @ vlk'))],
			    fk') ...)],
		 f{i+1}'))

*)
structure Uncurry : sig

    val transform : ANF.function -> ANF.function

end = struct

    structure A = ANF

    (* We don't attempt to uncurry exception handlers. *)
    fun transform { f = (f, vl, e), inl, hdlr } =
	let fun function ({ f = (f0, vl0, e0), inl = inl0, hdlr = false }, fl) =
		let fun build (rl, (f0, vl0, inl0), e) =
			let val l = rev rl
			    val f0' = LVar.clone f0
			    val inl0' = inl0 andalso List.all #3 l
			    val vl0_k =
				vl0 @ foldr (fn ((_, vl, _), avl) => vl @ avl)
					    [] l
			    fun header (pfx, (f, vl, inl), l) =
				  let fun gen (pfx, []) =
					    A.JUMP (Purity.Impure,
						    (A.VAR f0', map A.VAR pfx))
					| gen (pfx, (f, vl, inl) :: l) =
					    let val f' = LVar.clone f
						val vl' = map LVar.clone vl
						val h = gen (pfx @ vl', l)
					    in A.FIX ([{ f = (f', vl', h),
							 inl = true,
							 hdlr = false }],
						      A.VALUES [A.VAR f'])
					    end
				      val vl' = map LVar.clone vl
				  in { f = (f, vl', gen (pfx @ vl', l)),
				       inl = true, hdlr = false }
				  end
			    fun withHeaders (pfx, []) = e
			      | withHeaders (pfx, h :: t) =
				  A.FIX ([header (pfx, h, t)],
					 withHeaders (pfx @ #2 h, t))
			    val fu0' = { f = (f0', vl0_k, withHeaders (vl0, l)),
					 inl = inl0', hdlr = false }
			    val h0 = header ([], (f0, vl0, inl0), l)
			in fu0' :: h0 :: fl
			end
		    fun dump ([], (f0, vl0, inl0), e) =
			  { f = (f0, vl0, e), inl = inl0, hdlr = false } :: fl
		      | dump ((f, vl, inl) :: rl, i0, e) =
			  dump (rl, i0, 
				A.FIX ([{ f = (f, vl, e),
					  inl = inl,
					  hdlr = false }],
				       A.VALUES [A.VAR f]))
		    fun uncurry (rl, i0,
				 e as A.FIX ([{ f = (f, vl, b), inl, hdlr }],
					     A.VALUES [A.VAR v])) =
			  if not hdlr andalso f = v then
			      uncurry ((f, vl, inl) :: rl, i0, b)
			  else build (rl, i0, exp e)
		      | uncurry (rl, i0, e as (A.VALUES _ | A.JUMP _)) =
			  dump (rl, i0, e)
		      | uncurry (rl, i0, e) =
			  build (rl, i0, exp e)

		in case e0 of
		       A.FIX ([{ f = (f1, vl1, e1), inl = inl1, hdlr = false }],
			      A.VALUES [A.VAR v]) =>
		         if f1 = v then
			     uncurry ([(f1, vl1, inl1)], (f0, vl0, inl0), e1)
			 else { f = (f0, vl0, exp e0),
				inl = inl0, hdlr = false } :: fl
		     | _ => { f = (f0, vl0, exp e0),
			      inl = inl0, hdlr = false } :: fl
		end
	      | function (f, fl) = f :: fl

	    and exp (e as A.VALUES _) = e
	      | exp (A.BIND (v, x, e)) = A.BIND (v, x, exp e)
	      | exp (A.CALL (p, vl, xxl, e)) = A.CALL (p, vl, xxl, exp e)
	      | exp (A.FIX (fl, e)) = A.FIX (foldr function [] fl, exp e)
	      | exp (A.ARITH (a, x, y, v, e)) = A.ARITH (a, x, y, v, exp e)
	      | exp (A.RECORD (p, x, sl, v, e)) = A.RECORD (p, x, sl, v, exp e)
	      | exp (A.SELECT (x, y, p, v, e)) = A.SELECT (x, y, p, v, exp e)
	      | exp (A.UPDATE (x, y, z, e)) = A.UPDATE (x, y, z, exp e)
	      | exp (A.CMP (c, x, y, et, ef)) = A.CMP (c, x, y, exp et, exp ef)
	      | exp (A.GETSP (v, e)) = A.GETSP (v, exp e)
	      | exp (A.SETSP (x, e)) = A.SETSP (x, exp e)
	      | exp (A.MAYJUMP (v, e)) = A.MAYJUMP (v, exp e)
	      | exp (e as A.JUMP _) = e
	in { f = (f, vl, exp e), inl = inl, hdlr = hdlr }
	end
end
