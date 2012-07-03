structure Uncurry = 
struct

   exception Uncurry

   (* uncurry_unsafe
    * 
    * Form of uncurrying that is not necessarily correct w.r.t. logic
    * programming if there are upshifts in any of the premises of a
    * negative atomic proposition; it tries to move all the ordered
    * premises "up front" ahead of the linear and persistent premises,
    * so the proposition a >-> !b >-> c >-> $d >-> {...}, for
    * instance, will become c * a * !b * $d >-> {...}. 
    *
    * If an downshift (the inclusion of a negative proposition in a
    * positive one) is encountered, or if negative conjunction A & B
    * is encountered, or if the negative proposition is not a
    * concurrent rule, then Uncurry will be raised.
    *
    * It is possible for this to "do the wrong thing": a rule of the
    * form a X * !foo X (\z. Y z) * b (Y X) >-> {...}  will be
    * rewritten as a X * b (Y X) * !foo X (\z. Y z) >-> {...}, which
    * (if foo is moded (foo + -)) turns pattern-fragment matching
    * problems into non-pattern-fragment matching problems: the first
    * program is natural for moded proof search and the second is not.
    * 
    * The behavior of doing the wrong thing without warning should be
    * understood as a bug! It's just a documented bug. *)

   val uncurry_unsafe = 
   let 
      fun foldfuse [] = PosProp.One
        | foldfuse [ x ] = x
        | foldfuse (x :: xs) = PosProp.Fuse (x, foldfuse xs)

      (* handlepos
       *
       * It would be great if handlepos handled existentials, bringing
       * them closer to the outside, but that would break the somewhat
       * hackinsh invariants we have about uniquely named
       * variables. Specifically, (Exists x. a x) * (Exists x. b x)
       * would turn into Alli x. Alli x. a x * b x, which is
       * completely bogus. *)
      fun handlepos pprop = 
         case pprop of
            PosProp.PAtom (Perm.Ord, a, spi) => ([pprop], [])
          | PosProp.PAtom _ => ([], [pprop])
          | PosProp.Down (Perm.Ord, _) => raise Uncurry
          | PosProp.Down _ => ([], [pprop])
          | PosProp.One => ([], [])
          | PosProp.Fuse (pprop1, pprop2) =>
            let 
               val (ord1, notord1) = handlepos pprop1
               val (ord2, notord2) = handlepos pprop2
            in
               (ord1 @ ord2, notord1 @ notord2)
            end
          | PosProp.Exists _ => raise Uncurry
          | PosProp.Unif (t1, t2) => ([], [pprop])

      fun uncurry ctx ord notord nprop = 
         case nprop of 
            NegProp.NAtom (a, spi) => raise Uncurry
          | NegProp.Lax pprop => 
            let val premises = foldfuse (ord @ notord)
            in Context.wrapi ctx (NegProp.Lefti (premises, nprop))
            end
          | NegProp.Lefti (pprop, nprop) => 
            let val (ordL, notord') = handlepos pprop
            in uncurry ctx (ordL @ ord) (notord @ notord') nprop
            end
          | NegProp.Righti (pprop, nprop) => 
            let val (ordR, notord') = handlepos pprop
            in uncurry ctx (ord @ ordR) (notord @ notord') nprop
            end
          | NegProp.With _ => raise Uncurry  

          (* Turn all universal quantifiers implicit, which may or may
           * not be a reasonable behavior. *)
          | NegProp.All (x, t, nprop) =>
               uncurry ((x, t) :: ctx) ord notord nprop
          | NegProp.Alli (x, t, nprop) => 
               uncurry ((x, t) :: ctx) ord notord nprop
   in 
      fn nprop => uncurry [] [] [] nprop
   end
end
