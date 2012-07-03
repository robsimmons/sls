structure Defunctionalize =
struct
   val db = Syntax.empty (* Caching *)

   val forwardChain: (Symbol.symbol * Symbol.symbol) 
                     SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty

   val file: TextIO.outstream option ref = ref NONE

   fun print' s = Option.app (fn f => TextIO.output (f, s)) (!file)

   val cont_ord: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_lin: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_aff: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_pers: (Symbol.symbol * Symbol.symbol) option ref = ref NONE

   fun defunctionalize rule_root frame_root nprop = 
   let 
      exception CannotDefunctionalize

      fun pprocess ctx n pprop =  
         case pprop of 
            PosProp.PAtom (perm, a, spi) => (n, pprop)
          | PosProp.Down (perm, a, spi) =>
           (let 
               val x = 
                  case perm of
                     Perm.Ord => valOf (!cont_ord)
                   | Perm.Lin => valOf (!cont_lin)
                   | Perm.Aff => valOf (!cont_aff)
                   | Perm.Pers => valOf (!cont_pers)
            in 
               
            end handle Option => (n, pprop))
          | PosProp.One => (n, PosProp.One)
          | PosProp.Fuse (pprop1, pprop2) => 
            let 
               val (n1, pprop1') = pprocess ctx n pprop1
               val (n2, pprop2') = pprocess ctx n1 pprop2
            in 
               (n2, PosProp.Fuse (pprop1', pprop2'))
            end
          | PosProp.Exists (x, t, pprop) =>
            let val (n', pprop') = pprocess ((x, t) :: ctx) n pprop
            in 
               (n', PosProp.Exists (x, t, pprop')
            end
          | PosProp.Unif (t, s) => (n, ppor


      fun nprocess ctx n nprop = 
         case nprop of 
            NegProp.NAtom => raise CannotDefunctionalize
          | NegProp.Lax pprop => 
            let val (n', pprop') = pprocess ctx n pprop
            in (n', NegProp.Lax pprop) end
          | NegProp.Lefti (pprop, nprop) = 
            let val (n', nprop') = nprocess ctx n nprop
            in (n', NegProp.Lefti (pprop, nprop') end
          | NegProp.Righti (pprop, nprop) = 
            let val (n', nprop') = nprocess ctx n nprop
            in (n', NegProp.Righti (pprop, nprop') end
          | NegProp.With (nprop1, nprop2) = 
            raise CannotDefunctionalize (* Uncurry doesn't handle this case *)
          | NegProp.All (x, t, nprop) = 
            let val (n', nprop') = nprop ((x, t) :: ctx) n nprop
            in (n', NegProp.All (x, t, ctx')) end
          | NegProp.Alli (x, t, nprop) = 
            let val (n', nprop') = nprop ((x, t) :: ctx) n nprop
            in (n', NegProp.Alli (x, t, ctx')) end
   in 
   end
end
