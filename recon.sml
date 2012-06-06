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
       | _ => raise Fail ("Bad LF syntax: "^LDatum.toString dat)

   and datsToSyn inside [] = inside
     | datsToSyn inside (dat :: dats) =
          datsToSyn (ReconTerm.app (inside, datToSyn dat)) dats



   (* We want reconstructed terms to have unique variable names *)
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



   (* Read reconstructed Twelf syntax into the L10 LF representation *) 
   fun reconExp n ctx exp: Exp.t = 
      case exp of 
         IntSyn.Uni (IntSyn.Kind) => Exp.Knd
       | IntSyn.Uni (IntSyn.Type) => Exp.Typ
       | IntSyn.Pi ((IntSyn.Dec (NONE, exp1), No), exp2) => 
            Exp.Arrow (reconExp 0 ctx exp1, reconExp n (NONE :: ctx) exp2)
       | IntSyn.Pi ((IntSyn.Dec (SOME x, exp1), Yes), exp2) => 
         let
            val x = unique ctx x 
            val t = reconExp 0 ctx exp1
         in if n=0
            then Exp.Pi (x, t, reconExp n (SOME (x, t) :: ctx) exp2) 
            else Exp.Pii (x, t, reconExp (n-1) (SOME (x, t) :: ctx) exp2)
         end
       | IntSyn.Root (IntSyn.BVar i, sp) =>
         let val (x, t) = valOf (List.nth (ctx, i-1))
         in Exp.Var (x, IntInf.fromInt i, reconSpine ctx sp t) 
         end
       | IntSyn.Root (IntSyn.Const cid, sp) =>
         let val cid' = IntRedBlackDict.lookup (!cidLookup) cid
         in Exp.Con (cid', reconSpine ctx sp (Signature.lookup cid')) 
         end
       | IntSyn.Lam (IntSyn.Dec (SOME x, exp1), exp2) =>
         let
            val x = unique ctx x 
            val t = reconExp 0 ctx exp1
         in Exp.Lam (x, reconExp n (SOME (x, t) :: ctx) exp2)
         end
       | _ => raise Fail "Unexpected reconstruction term"

   and reconSpine ctx sp t: Spine.t = 
      case (sp, t) of 
         (IntSyn.Nil, Exp.Con _) => Spine.Nil
       | (IntSyn.Nil, Exp.Typ) => Spine.Nil
       | (IntSyn.Nil, Exp.Nprop) => Spine.Nil
       | (IntSyn.Nil, Exp.Pprop _) => Spine.Nil
       | (IntSyn.App (exp, sp), Exp.Pii (_, _, t)) => 
            Spine.Appi (reconExp 0 ctx exp, reconSpine ctx sp t)
       | (IntSyn.App (exp, sp), Exp.Pi (_, _, t)) => 
            Spine.App (reconExp 0 ctx exp, reconSpine ctx sp t)
       | (IntSyn.App (exp, sp), Exp.Arrow (_, t)) => 
            Spine.App (reconExp 0 ctx exp, reconSpine ctx sp t)
       | (IntSyn.SClo _, _) => raise Fail "Did not expect an SClo"
       | _ => raise Fail ("Type error in reconSpine, type [" 
                          ^Exp.toString t^"]") 



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
       | _ => raise Fail ("Bad SLS syntax: "^LDatum.toString dat)
   end

   (* Come up with a fake LF type to force Twelf to do full dependent type 
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

       | LDatum.Node ("bang", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("at", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("mobile", [dat], pos) => ruleToFakeLF dat cont
       | LDatum.Node ("monad", [dat], pos) => ruleToFakeLF dat cont

       | LDatum.Node ("unify", _, _) => raise Fail "Can't handle unify"
       | _ => raise Fail ("Impossible?")


   (* Effect: initializes Twelf's reconstruction facilities appropriately *)
   val cidProp = ref ~1
   val cidOrd = ref ~1
   val cidLin = ref ~1
   val cidPers = ref ~1

   fun handleCondec (s, dats, pos) = 
   let
      val s' = Symbol.fromValue s

      (* Some of the things Twelf classifies as Type are SLS kinds *)
      fun classifier (IntSyn.Root (IntSyn.Const cid, _)) =
            (if cid = !cidProp
                orelse cid = !cidOrd
                orelse cid = !cidLin
                orelse cid = !cidPers
             then Exp.Knd
             else Exp.Typ)
        | classifier (IntSyn.Pi (_, exp)) = classifier exp
        | classifier _ = raise Fail "Unexpected classifier"

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

      val dat = Fixity.resolve dats
      val syn = datToSyn dat
      val (condec, _) = ReconConDec.condecToConDec 
                           (ReconConDec.condec (s, syn), l, false)
      val cid = installTwelf condec
      val (exp, class) = 
         case condec of 
            (SOME (IntSyn.ConDec (_, NONE, i, IntSyn.Normal, exp, uni))) =>
              (case uni of 
                  IntSyn.Kind => (* Definitely a type *)
                     (reconExp i [] exp, Exp.Knd)
                | IntSyn.Type => (* Might be a proposition! *) 
                     (reconExp i [] exp, classifier exp))
          | _ => raise Fail "Unexpected condec"
            
   in
    ( cidLookup := IntRedBlackDict.insert (!cidLookup) cid s'
    ; Handle.condec (s', exp, class)
    ; print (s^": "^Exp.toString exp^".\n")
    ; cid)
   end

   fun handleRule (s, dats, pos) = 
   let
      val dat = Fixity.resolve dats
      val rule = datToRule dat
      val syn = ruleToFakeLF rule fakeEnd
      val condec = ReconConDec.condecToConDec
                      (ReconConDec.condec (".", syn), l, false)
   in
    ( print ("#rule "^s^": ")
    ; print (LDatum.toString dat)
    ; print ".\n")
   end

   fun init () = 
   let val ty = [PosDatum.List [("type", [], fake_pos)]]
   in
    ( cidProp := handleCondec ("prop", ty, fake_pos)
    ; cidOrd  := handleCondec ("ord", ty, fake_pos)
    ; cidLin  := handleCondec ("lin", ty, fake_pos)
    ; cidPers := handleCondec ("pers", ty, fake_pos)
    ; handleCondec ("type", ty, fake_pos)
    ; {syntax = 
          (fn (PosDatum.List [("condec", [PosDatum.Atom (s, _)], pos1), 
                               (":", dats, pos2)]) =>
                 (ignore o handleCondec) (s, dats, Pos.union pos1 pos2)
            | (PosDatum.List [("rule", (PosDatum.Atom (s, _)
                                         :: PosDatum.Atom (":", _) 
                                         :: dats),
                                pos)]) => 
                 handleRule (s, dats, pos)
            | _ => ()),
       condec = ignore,
       rule = ignore})
   end
end
