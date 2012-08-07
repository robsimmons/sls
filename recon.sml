(* Reconstruction handler (triggers the syntax/condec/rule handlers) *)

signature RECON =
sig
   (* Main handler interface *)
   val init: unit -> Handle.handler
end

structure Recon:> RECON =
struct
   val fake_coord = Coord.init "fake"
   val fake_pos = Pos.pos fake_coord fake_coord
   val r = Paths.Reg (0, 0) (* Fake Twelf region *)
   val l = Paths.Loc ("fake", r) (* Fake Twelf location *)



   (* Internal map from cids to symbols *)
   val cidLookup: Symbol.symbol IntRedBlackDict.dict ref = 
      ref IntRedBlackDict.empty
   fun getcid i = IntRedBlackDict.lookup (!cidLookup) i



   fun ctxToString ctx = 
      String.concatWith ", " (map (fn (SOME (x,t)) => x^":"^Exp.toString t
                                    | NONE => "_") ctx)
   fun getvar ctx n = 
      if n > length ctx 
      then raise Fail ("Cannot look up deBrujn index "^Int.toString n^" in ["
                       ^ctxToString ctx^"]")
      else if n < 1 then raise Fail ("Invalid de Bruijn index"^Int.toString n)
      else (case List.nth (ctx, n-1) of
               NONE => raise Fail ("De Bruijn "^Int.toString n^" not dependent")
             | SOME (x, t) => (x, t))



   (* Read intermediate SLS syntax into external Twelf syntax *)
   fun datToSyn (dat: (string, string) LDatum.t): ReconTerm.term = 
      case dat of
         LDatum.Atom ("_", pos) => ReconTerm.omitted r
       | LDatum.Atom (s, pos) => 
            if Char.isUpper (String.sub (s, 0)) 
            then ReconTerm.ucid ([], s, r)
            else ReconTerm.lcid ([], s, r) 
       | LDatum.Node ("type", [], pos) => ReconTerm.typ r
       | LDatum.Node ("prop", [], pos) => ReconTerm.typ r
       | LDatum.Node ("ord", [], pos) => ReconTerm.typ r
       | LDatum.Node ("lin", [], pos) => ReconTerm.typ r
       | LDatum.Node ("pers", [], pos) => ReconTerm.typ r
       | LDatum.Node ("arrow", [d1, d2], pos) => 
            ReconTerm.arrow (datToSyn d1, datToSyn d2)
       | LDatum.Node ("pi", [(LDatum.Atom (x, _)), d2], pos) => 
            ReconTerm.pi (ReconTerm.dec0 (SOME x, r), datToSyn d2)
       | LDatum.Node ("pi", [(LDatum.Atom (x, _)), d1, d2], pos) => 
            ReconTerm.pi (ReconTerm.dec (SOME x, datToSyn d1, r), 
                          datToSyn d2)
       | LDatum.Node ("lambda", [(LDatum.Atom (x, _)), d2], pos) => 
            ReconTerm.lam (ReconTerm.dec0 (SOME x, r), datToSyn d2)
       | LDatum.Node ("lambda", [(LDatum.Atom (x, _)), d1, d2], pos) => 
            ReconTerm.lam (ReconTerm.dec (SOME x, datToSyn d1, r), 
                           datToSyn d2)
       | LDatum.List (dat :: dats, pos) => datsToSyn (datToSyn dat) dats
       | _ => raise Fail ("Bad LF syntax: "^LDatum.toString dat^
                          ": "^Pos.toString (LDatum.pos dat))

   and datsToSyn inside [] = inside
     | datsToSyn inside (dat :: dats) =
          datsToSyn (ReconTerm.app (inside, datToSyn dat)) dats



   (* Read reconstructed Twelf syntax into the L10 LF representation *) 
   fun reconExp' replace n ctx exp: Exp.t = 
      case exp of 
         IntSyn.Uni (IntSyn.Kind) => 
           (if Option.isSome replace then raise Fail "Internal error"
            else Exp.Knd)
       | IntSyn.Uni (IntSyn.Type) => 
           (case replace of 
               NONE => Exp.Typ
             | SOME knd => knd) (* prop/propord/proppers/etc. *)
       | IntSyn.Pi ((IntSyn.Dec (NONE, exp1), IntSyn.No), exp2) => 
            Exp.Arrow (reconExp 0 ctx exp1, 
                       reconExp' replace n (NONE :: ctx) exp2)
       | IntSyn.Pi ((IntSyn.Dec (SOME x, exp1), IntSyn.Maybe), exp2) => 
         let
            val x = Context.unique ctx x 
            val t = reconExp 0 ctx exp1
         in if n=0
            then Exp.Pi (x, t, reconExp' replace n (SOME (x, t) :: ctx) exp2) 
            else Exp.Pii (x, t, 
                          reconExp' replace (n-1) (SOME (x, t) :: ctx) exp2)
         end
       | IntSyn.Root (IntSyn.BVar i, sp) =>
         let
            val (x, t) = getvar ctx i
            (* val () = print ("ROOT: "^x^"("^Int.toString i^")\n") *)
         in 
           (if Option.isSome replace then raise Fail "Internal error"
            else Exp.Var (x, IntInf.fromInt i-1, #1 (reconSpine ctx sp t)))
         end
       | IntSyn.Root (IntSyn.Const cid, sp) =>
         let 
            val cid' = getcid cid
            (* val () = print ("ROOT: "^Symbol.toValue cid'^"\n") *)
         in 
           (if Option.isSome replace then raise Fail "Internal error" 
            else Exp.Con (cid', #1 (reconSpine ctx sp (Signature.lookup cid'))))
         end
       | IntSyn.Lam (IntSyn.Dec (SOME x, exp1), exp2) =>
         let
            val x = Context.unique ctx x 
            val t = reconExp 0 ctx exp1
            (* val () = print ("LAMBDA: "^x^"\n") *)
         in Exp.Lam (x, reconExp' replace n (SOME (x, t) :: ctx) exp2)
         end
       | IntSyn.Lam (IntSyn.Dec (NONE, exp1), exp2) =>
         let
            val x = Context.unique ctx "x"
            val t = reconExp 0 ctx exp1
            (* val () = print ("LAMBDA: "^x^"\n") *)
         in Exp.Lam (x, reconExp' replace n (SOME (x, t) :: ctx) exp2)
         end
       | _ => raise Fail "Unexpected reconstruction term"

   and reconExp n ctx exp: Exp.t = reconExp' NONE n ctx exp

   and reconSpine ctx sp t: Spine.t * Exp.t = 
    ( case (sp, t) of 
         (IntSyn.Nil, Exp.Con _) => (Spine.Nil, t)
       | (IntSyn.Nil, Exp.Typ) => (Spine.Nil, t)
       | (IntSyn.Nil, Exp.NProp) => (Spine.Nil, t)
       | (IntSyn.Nil, Exp.PProp _) => (Spine.Nil, t)
       | (IntSyn.App (exp, sp), Exp.Pii (_, _, t)) => 
         let val (sp', t') = reconSpine ctx sp t
         in (Spine.Appi (reconExp 0 ctx exp, sp'), t') 
         end
       | (IntSyn.App (exp, sp), Exp.Pi (_, _, t)) => 
         let val (sp', t') = reconSpine ctx sp t
         in (Spine.App (reconExp 0 ctx exp, sp'), t')
         end
       | (IntSyn.App (exp, sp), Exp.Arrow (_, t)) => 
         let val (sp', t') = reconSpine ctx sp t
         in (Spine.App (reconExp 0 ctx exp, sp'), t')
         end
       | (IntSyn.SClo _, _) => raise Fail "Did not expect an SClo"
       | (IntSyn.App _, _) => raise Fail ("Type error in reconSpine, type [" 
                                          ^Exp.toString t^"] (internal)")
       | (IntSyn.Nil, _) => raise Fail ("Type error in reconSpine, type [" 
                                        ^Exp.toString t^"] (internal)"))



   (* Read a rule into external SLS syntax *)
   (* Removes -@, -o, and -> in favor of >-> *)
   fun datToRule dat: (string, ReconTerm.term) LDatum.t =
   let
      fun datExp name dat = 
         LDatum.Node (name, [datToRule dat], LDatum.pos dat) 
   in
      case dat of
         LDatum.Atom (_, pos) => LDatum.Atom (datToSyn dat, pos)
       | LDatum.List (_, pos) => LDatum.Atom (datToSyn dat, pos)

       | LDatum.Node ("monad", [dat], pos) => 
            LDatum.Node ("monad", [datToRule dat], pos)
       
       | LDatum.Node ("forall", [LDatum.Atom (x, posx), dat1], pos) => 
            LDatum.Node ("forall", 
                         [LDatum.Node (x, [], posx), 
                          datToRule dat1],
                         pos)
       | LDatum.Node ("forall", [LDatum.Atom (x, posx), dat1, dat2], pos) => 
            LDatum.Node ("forall", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (datToSyn dat1, LDatum.pos dat1),
                          datToRule dat2],
                         pos)
       | LDatum.Node ("exists", [LDatum.Atom (x, posx), dat1], pos) => 
            LDatum.Node ("exists", 
                         [LDatum.Node (x, [], posx), 
                          datToRule dat1],
                         pos)
       | LDatum.Node ("exists", [LDatum.Atom (x, posx), dat1, dat2], pos) => 
            LDatum.Node ("exists", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (datToSyn dat1, LDatum.pos dat1),
                          datToRule dat2],
                         pos)

       | LDatum.Node ("with", [dat1, dat2], pos) =>
            LDatum.Node ("with", [datToRule dat1,
                                  datToRule dat2], pos)
       | LDatum.Node ("lefti", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datToRule dat1,
                                   datToRule dat2], pos)
       | LDatum.Node ("righti", [dat1, dat2], pos) =>
            LDatum.Node ("righti", [datToRule dat1,
                                    datToRule dat2], pos)
       | LDatum.Node ("lolli", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datExp "mobile" dat1,
                                   datToRule dat2], pos)
       | LDatum.Node ("affi", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datExp "at" dat1,
                                   datToRule dat2], pos)
       | LDatum.Node ("arrow", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", 
                         [datExp "bang" dat1, datToRule dat2], pos)
       | LDatum.Node ("tensor", [dat1, dat2], pos) =>
            LDatum.Node ("tensor", [datToRule dat1,
                                    datToRule dat2], pos)
       | LDatum.Node ("unify", [dat1, dat2], pos) => 
            LDatum.Node ("unify", 
                         [LDatum.Atom (datToSyn dat1, LDatum.pos dat1),
                          LDatum.Atom (datToSyn dat2, LDatum.pos dat2)], 
                          pos)

       | LDatum.Node ("bang", [dat], pos) => 
            LDatum.Node ("bang", [datToRule dat], pos) 
       | LDatum.Node ("at", [dat], pos) =>
            LDatum.Node ("at", [datToRule dat], pos)
       | LDatum.Node ("mobile", [dat], pos) =>
            LDatum.Node ("mobile", [datToRule dat], pos) 
       | LDatum.Node ("one", [], pos) => LDatum.Node ("one", [], pos)
       | _ => raise Fail ("Bad SLS syntax: "^LDatum.toString dat^
                          ": "^Pos.toString (LDatum.pos dat))
   end

   (* Come up with a fake LF type to force Twelf to do dependent type 
    * reconstruction on a declaration in full. *)
   (* A weird type name "type" won't ever get in the way of anything, right? *)
   val fakeEnd = ReconTerm.ucid ([], "type", r)
   fun ruleToFakeLF (dat: (string, ReconTerm.term) LDatum.t) cont = 
      case dat of 
         LDatum.Atom (term, pos) => 
            ReconTerm.arrow (term, cont)

       | LDatum.Node ("forall", [LDatum.Node (x, [], posx), dat1], pos) => 
            ReconTerm.arrow 
               (ReconTerm.pi (ReconTerm.dec0 (SOME x, r),
                              ruleToFakeLF dat1 fakeEnd), cont)
       | LDatum.Node ("forall", [LDatum.Node (x, [], posx), 
                                 LDatum.Atom (typ, _), dat2], pos) =>
            ReconTerm.arrow
               (ReconTerm.pi (ReconTerm.dec (SOME x, typ, r), 
                              ruleToFakeLF dat2 fakeEnd), cont)
       | LDatum.Node ("exists", [LDatum.Node (x, [], posx), dat1], pos) => 
            ReconTerm.arrow 
               (ReconTerm.pi (ReconTerm.dec0 (SOME x, r),
                              ruleToFakeLF dat1 fakeEnd), cont)
       | LDatum.Node ("exists", [LDatum.Node (x, [], posx), 
                                 LDatum.Atom (typ, _), dat2], pos) =>
            ReconTerm.arrow
               (ReconTerm.pi (ReconTerm.dec (SOME x, typ, r), 
                              ruleToFakeLF dat2 fakeEnd), cont)

       | LDatum.Node ("with", [dat1, dat2], pos) => 
            ruleToFakeLF dat1 (ruleToFakeLF dat2 cont)
       | LDatum.Node ("lefti", [dat1, dat2], pos) => 
            ruleToFakeLF dat1 (ruleToFakeLF dat2 cont)
       | LDatum.Node ("righti", [dat1, dat2], pos) => 
            ruleToFakeLF dat1 (ruleToFakeLF dat2 cont)
       | LDatum.Node ("tensor", [dat1, dat2], pos) => 
            ruleToFakeLF dat1 (ruleToFakeLF dat2 cont)
       | LDatum.Node ("one", [], pos) => cont

       | LDatum.Node ("bang", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("at", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("mobile", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("monad", [dat], pos) => ruleToFakeLF dat cont

       | LDatum.Node ("unify", [LDatum.Atom (term1, _),
                                LDatum.Atom (term2, _)], pos) => 
            ReconTerm.unif (term1, term2, cont)
       | _ => raise Fail ("Impossible?")



   (* Read reconstructed fake-Twelf syntax along with unreconstructed
    * rule syntax into the L10 SLS representation *) 
   val cidFakeType = ref ~1
   (* datatype modalAtomicProps = EITHER_WAY
   val modalAtomicProps := ref EITHER_WAY *)

   fun requireArrow exp =
      case exp of 
         IntSyn.Pi ((IntSyn.Dec (NONE, exp), IntSyn.No), expcont) =>
            (exp, expcont)
       | _ => raise Fail "Internal error"

   fun requireType exp msg = 
      case exp of 
         IntSyn.Root (IntSyn.Const cid, IntSyn.Nil) =>
            if cid = !cidFakeType then ()
            else raise Fail ("Internal error (requireType/"^msg^")")
       | _ => raise Fail ("Internal error (requireType/"^msg^")")

   (* Get the implicitly bound variables from Twelf *)
   fun reconImplicit 0 ctx (dat: (string, ReconTerm.term) LDatum.t) exp = 
         let val (nprop, expcont, ctx) = reconNeg ctx dat exp
         in
          ( requireType expcont "outer implicit bindings"
          ; nprop)
         end
     | reconImplicit n ctx dat exp = 
         (case exp of  
             IntSyn.Pi ((IntSyn.Dec (SOME x, exp1), IntSyn.Maybe), exp2) => 
             let
                val x = Context.unique ctx x 
                val t = reconExp 0 ctx exp1
             in NegProp.Alli 
                   (x, t, reconImplicit (n-1) (SOME (x, t) :: ctx) dat exp2)
             end
           | _ => raise Fail "Unexpected implicit type structure")

   (* Reconstruct an atom, positive or negative *)
   and reconAtom ctx pos expcont = 
      let 
         val (exp0, expcont) = requireArrow expcont
         val (cid, sp) = 
            case exp0 of 
               IntSyn.Root (IntSyn.Const cid, sp) => (cid, sp)
             | IntSyn.Root (IntSyn.BVar i, sp) => 
                  raise Fail ("Variable '"^ #1 (getvar ctx i)
                              ^"' found where a predicate was expected")
             | _ => 
                  raise Fail ("Weird inclusion of LF syntax into an SLS \
                              \proposition (most likely a 'Pi x.' instead \
                              \of an 'All x.'): "^Pos.toString pos)
         val cid' = getcid cid
         (* val () = print ("PREDICATE: "^Symbol.toValue cid'^"\n") *)
         val (sp', t') = reconSpine ctx sp (Signature.lookup cid')
      in
         case t' of
            Exp.Con (a, _) => raise Fail "Internal error" (* Twelf TC *)
          | Exp.Typ => raise Fail ("Found LF type constructor where predicate \
                                   \was expected: "^Pos.toString pos)
          | Exp.NProp => (Sum.INL (cid', sp'), expcont)
          | Exp.PProp perm => (Sum.INR (perm, cid', sp'), expcont)
          | _ => raise Fail "Internal error"
      end 

   (* @X, $X, !X - X is a (affine, mobile, persistent) atomic proposition
    *    or a negative proposition.
    * X, where X is definitely not positive - X is some form of positive
    *    atomic proposition or it is a shifted positive atomic proposition. *)
   and reconModal ctx (dat: (string, ReconTerm.term) LDatum.t) perm expcont =
   let
      val compatible = 
         case perm of 
             Perm.Ord => (fn _ => ())
           | perm =>
               (fn (perm', _, _) => 
                  (if Perm.eq (perm, perm')
                      then ()
                   else raise Fail ("Permeability of positive atomic \
                                    \proposition doesn't match annotation. \
                                    \Expected: "^Perm.toString perm^", \
                                    \got: "^Perm.toString perm')))
   in
      case dat of 
         LDatum.Atom (_, pos) => 
         let
            val (atom, expcont) = reconAtom ctx pos expcont
         in case atom of
               Sum.INL x =>
                  (PosProp.Down (perm, NegProp.NAtom x), expcont, 
                   NONE :: ctx)
             | Sum.INR x =>
                ( compatible x (* Permeability has to match! *)
                ; (PosProp.PAtom x, expcont, NONE :: ctx))
         end
       | _ => 
         let val (nprop, expcont, ctx) = reconNeg ctx dat expcont
         in (PosProp.Down (perm, nprop), expcont, ctx)
         end
   end
         

   and reconPos ctx (dat: (string, ReconTerm.term) LDatum.t) expcont = 
      case dat of 
         LDatum.Node ("unify", [dat1, dat2], pos) => 
         let
            val (exp1, exp2, expcont') = 
               case expcont of 
                  IntSyn.Unif (exp1, exp2, exp3, expcont') => 
                     (exp1, exp2, expcont')
                | _ => raise Fail "Internal error"
            val t1 = reconExp 0 ctx exp1
            val t2 = reconExp 0 ctx exp2 
         in 
            (PosProp.Unif (t1, t2), expcont', ctx)
         end

       | LDatum.Node ("exists", dats, pos) =>
         let 
            val (exp0, expcont) = requireArrow expcont
            val (x, exp1, exp2) = 
               case exp0 of 
                  IntSyn.Pi ((IntSyn.Dec (SOME x, exp1), IntSyn.Maybe), exp2) =>
                     (x, exp1, exp2)
                | IntSyn.Pi _ => 
                     raise Fail ("Existentially quantified variable \
                                 \is not free in scope: "
                                 ^Pos.toString (LDatum.pos (hd dats)))
                | _ => raise Fail "Internal error"
            val x = Context.unique ctx x 
            val t = reconExp 0 ctx exp1 
            val (nprop1, expcont', ctx') = 
               reconPos (SOME (x, t) :: ctx) (List.last dats) exp2 
         in 
           ( requireType expcont' "exists"
           ; (PosProp.Exists (x, t, nprop1), expcont, NONE :: ctx))
         end

       | LDatum.Node ("tensor", [dat1, dat2], pos) =>
         let 
            val (pprop1, expcont, ctx) = reconPos ctx dat1 expcont
            val (pprop2, expcont, ctx) = reconPos ctx dat2 expcont
         in (PosProp.Fuse (pprop1, pprop2), expcont, ctx)
         end

       | LDatum.Node ("one", [], pos) =>
            (PosProp.One, expcont, ctx)
   
       | LDatum.Node ("bang", [dat], pos) =>
            reconModal ctx dat (Perm.Pers) expcont

       | LDatum.Node ("at", [dat], pos) =>
            reconModal ctx dat (Perm.Aff) expcont

       | LDatum.Node ("mobile", [dat], pos) =>
            reconModal ctx dat (Perm.Lin) expcont

       | _ => reconModal ctx dat (Perm.Ord) expcont

   and reconNeg ctx (dat: (string, ReconTerm.term) LDatum.t) expcont = 
      case dat of
         LDatum.Atom (_, pos) => 
         let val (atom, expcont) = reconAtom ctx pos expcont
         in case atom of 
               Sum.INL x => (NegProp.NAtom x, expcont, NONE :: ctx)
             | Sum.INR (_, cid, _) => 
                  raise Fail ("Constant '"^Symbol.toValue cid^"' constructs \
                              \positive atomic propositions, but a negative \
                              \atomic proposition was expected here.")
         end

       | LDatum.Node ("monad", [dat], pos) => 
         let 
            val (pprop, expcont, ctx) = reconPos ctx dat expcont
         in (NegProp.Lax pprop, expcont, ctx)
         end

       | LDatum.Node ("forall", dats, pos) =>
         let
            val (exp0, expcont) = requireArrow expcont
            val (x, exp1, exp2) = 
               case exp0 of 
                  IntSyn.Pi ((IntSyn.Dec (SOME x, exp1), IntSyn.Maybe), exp2) =>
                     (x, exp1, exp2)
                | IntSyn.Pi _ => 
                     raise Fail ("Universally quantified variable \
                                 \is not free in rule: "
                                 ^Pos.toString (LDatum.pos (hd dats)))
                | _ => raise Fail "Internal error"

            val x = Context.unique ctx x 
            val t = reconExp 0 ctx exp1 
            val (nprop1, expcont', ctx') = 
               reconNeg (SOME (x, t) :: ctx) (List.last dats) exp2 
         in 
           ( requireType expcont' "forall"
           ; (NegProp.All (x, t, nprop1), expcont, NONE :: ctx))
         end

       | LDatum.Node ("with", [dat1, dat2], pos) => 
         let
            val (nprop1, expcont, ctx) = reconNeg ctx dat1 expcont
            val (nprop2, expcont, ctx) = reconNeg ctx dat2 expcont
         in (NegProp.With (nprop1, nprop2), expcont, ctx)
         end

       | LDatum.Node ("lefti", [dat1, dat2], pos) => 
         let
            val (pprop1, expcont, ctx) = reconPos ctx dat1 expcont
            val (nprop2, expcont, ctx) = reconNeg ctx dat2 expcont
         in (NegProp.Lefti (pprop1, nprop2), expcont, ctx)
         end

       | LDatum.Node ("righti", [dat1, dat2], pos) => 
         let
            val (pprop1, expcont, ctx) = reconPos ctx dat1 expcont
            val (nprop2, expcont, ctx) = reconNeg ctx dat2 expcont
         in (NegProp.Righti (pprop1, nprop2), expcont, ctx)
         end

       | LDatum.Node (lab, _, pos) => 
            raise Fail ("Reconstruction error: unexpected '"^lab
                        ^"' where a negative proposition was expected: "
                        ^Pos.toString pos)

       

       | LDatum.List _ => raise Fail "Internal error"



   (* Effect: initializes Twelf's reconstruction facilities appropriately *)
   val cidProp = ref ~1
   val cidOrd = ref ~1
   val cidLin = ref ~1
   val cidPers = ref ~1


   (* (dat, INL NONE) <- reconstruct as a term constructor
    * (dat, INL (SOME knd)) <- reconstruct as a [knd] constructor
    * (dat, INR ()) <- reconstruct as a rule *)
   fun preprocess dats = 
   let 
      val dat = Fixity.resolve dats
      fun traverse dat = 
         case dat of 
            LDatum.Atom (s, pos) => 
              (case Signature.findClass (Symbol.fromValue s) of
                  NONE => raise Fail ("Unknown type family/predicate '"
                                      ^s^"'"^Pos.toString pos)
                | SOME Exp.Typ => Sum.INL NONE (* It's a term constant! *)
                | SOME Exp.NProp => Sum.INR () (* It's a rule \! *)
                | SOME exp => raise Fail ("The head of a constant or rule \
                                          \must be be a type or negative \ 
                                          \proposition: "^Pos.toString pos))
          | LDatum.Node ("type", [], pos) => Sum.INL (SOME Exp.Typ)
          | LDatum.Node ("prop", [], pos) => Sum.INL (SOME Exp.NProp)
          | LDatum.Node ("ord", [], pos) => Sum.INL (SOME (Exp.PProp Perm.Ord))
          | LDatum.Node ("lin", [], pos) => Sum.INL (SOME (Exp.PProp Perm.Lin))
          | LDatum.Node ("aff", [], pos) => Sum.INL (SOME (Exp.PProp Perm.Aff))
          | LDatum.Node ("pers", [], pos) => 
               Sum.INL (SOME (Exp.PProp Perm.Pers))
          | LDatum.Node ("arrow", [d1, d2], pos) => traverse d2
          | LDatum.Node ("pi", dats, pos) => traverse (List.last dats)
          | LDatum.Node ("lambda", dats, pos) => traverse (List.last dats)
          | LDatum.List (dat :: dats, pos) => traverse dat
          | _ => Sum.INR () (* Give up on LF, hopefully it's a rule *)
   in
      (dat, traverse dat)
   end

   fun handleCondec (s, dat, class, pos) = 
   let
      val s' = Symbol.fromValue s

      (* Install a condec into Twelf *)
      fun installTwelf NONE = raise Fail "Anonymous definition?"
        | installTwelf (SOME ConDec) =
          let
             val cid = IntSyn.sgnAdd ConDec
             val _ = Names.installConstName cid
             val _ = Origins.installOrigin (cid, ("", NONE))
             val _ = Index.install IntSyn.Ordinary (IntSyn.Const cid) 
             val _ = IndexSkolem.install IntSyn.Ordinary (IntSyn.Const cid)
             val _ = Compile.install IntSyn.Ordinary cid
             val _ = Subordinate.install cid
             val _ = Subordinate.installDef cid
          in
             cid
          end

      val syn = datToSyn dat
      val (condec, _) = ReconConDec.condecToConDec 
                           (ReconConDec.condec (s, syn), l, false)
      val cid = installTwelf condec
      val exp = 
         case condec of 
            (SOME (IntSyn.ConDec (_, NONE, i, IntSyn.Normal, exp, uni))) =>
               reconExp' class i [] exp
          | _ => raise Fail "Unexpected condec"
      val class = case class of NONE => Exp.Typ | SOME _ => Exp.Knd
   in
    ( cidLookup := IntRedBlackDict.insert (!cidLookup) cid s'
    ; Handle.condec (s', exp, class)
    (* ; print (s^": "^Exp.toString exp^".\n") *)
    ; cid)
   end

   fun handleRule (s, dat, pos) = 
   let
      val s' = Symbol.fromValue s

      val rule = datToRule dat
      val syn = ruleToFakeLF rule fakeEnd
      val (condec, _) = ReconConDec.condecToConDec
                           (ReconConDec.condec (".", syn), l, false)
      val rule = 
         case condec of 
            (SOME (IntSyn.ConDec (_, NONE, i, IntSyn.Normal, exp, uni))) =>
               reconImplicit i [] rule exp
          | _ => raise Fail "Unexpected condec"
   in
    ( Handle.rule (s', rule)
    (* ; print ("#rule "^s^": "^NegProp.toString rule^".\n") *))
   end

   fun set () = 
   let val ty = Fixity.resolve [PosDatum.List [("type", [], fake_pos)]]
   in
    ( cidProp := handleCondec ("prop", ty, NONE, fake_pos)
    ; cidOrd  := handleCondec ("ord", ty, NONE, fake_pos)
    ; cidLin  := handleCondec ("lin", ty, NONE, fake_pos)
    ; cidPers := handleCondec ("pers", ty, NONE, fake_pos)
    ; cidFakeType := handleCondec ("type", ty, NONE, fake_pos))
   end

   fun init () = 
    ( set ()
    ; {syntax = 
          (fn (PosDatum.List [("condec", [PosDatum.Atom (s, _)], pos1), 
                               (":", dats, pos2)]) =>
                ( Signature.register (Symbol.fromValue s) pos1
                ; case preprocess dats of
                    (dat, Sum.INL class) => 
                       (ignore o handleCondec) 
                          (s, dat, class, Pos.union pos1 pos2)
                  | (dat, Sum.INR ()) => 
                       handleRule (s, dat, Pos.union pos1 pos2))

            | (PosDatum.List [("rule", (PosDatum.Atom (s, _)
                                         :: PosDatum.Atom (":", _) 
                                         :: dats),
                                pos)]) => 
               ( Signature.register (Symbol.fromValue s) pos
               ; handleRule (s, Fixity.resolve dats, pos))

            | _ => ()),
       condec = ignore,
       rule = ignore,
       reset = fn () =>
                ( IntSyn.sgnReset ()
                ; Names.reset ()
                ; Origins.reset ()
                (* ; ModeTable.reset () *)
                (* ; UniqueTable.reset () (* -fp Wed Mar  9 20:24:45 2005 *) *)
                ; Index.reset ()
                ; IndexSkolem.reset ()
                ; Subordinate.reset ()
                (* ; Total.reset ()     (* -fp *) *)
                (* ; WorldSyn.reset ()  (* -fp *) *)
                (* ; Reduces.reset ()   (* -bp *) *)
                (* ; TabledSyn.reset () (* -bp *) *)
                (* ; FunSyn.labelReset () *)
                (* ; CompSyn.sProgReset () (* necessary? -fp; yes - bp*) *)
                (* ; CompSyn.detTableReset () (*  -bp *) *)
                ; Compile.sProgReset () (* resetting substitution trees *)

                (* ; ModSyn.reset () *)
                (* ; CSManager.resetSolvers () *)
                (* ; Twelf.reset () *)
                ; set ())})
end
