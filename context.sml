structure Context = 
struct
    (* Turns a context into a series of bindings *)
    fun wrap [] nprop = nprop
      | wrap ((x, t) :: ctx) nprop = wrap ctx (NegProp.All (x, t, nprop))

    (* Turns a context into a series of implicit forall-bindings *)
    fun wrapi [] nprop = nprop
      | wrapi ((x, t) :: ctx) nprop = wrapi ctx (NegProp.Alli (x, t, nprop))

   (* Partitions a context according to membership in a set: parts of 
    * the context that are in the set, and parts of the context that
    * are not in the set. XXX get this to handle dependencies correctly. *)
   fun partition ctx fv = 
      List.partition (fn (x, t) => StringRedBlackSet.member fv x) ctx

   (* We want reconstructed terms to have unique variable names; the
    * unique function creates a version of x that does not appear in
    * the context. If x isn't in the context, unique will always be
    * the identity; otherwise it will add a numerical postfix to x (or
    * change the existing numerical postfix to x) *)
   fun unique ctx x = 
   let
      fun uniqueInCtx x = 
         not (List.exists (fn NONE => false | SOME (y, _) => x = y) ctx)

      fun loop x' n =
      let val y = x'^Int.toString n 
      in if uniqueInCtx y then y else loop x' (n+1) end

      fun removeNumberPostfix n = 
         if n<=0 then "x"
         else if Char.isDigit (String.sub (x, n-1)) 
         then removeNumberPostfix (n-1)
         else String.substring (x, 0, n)
   in
      if uniqueInCtx x then x
      else loop (removeNumberPostfix (size x)) 1
   end
end
