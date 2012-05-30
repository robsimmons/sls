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

   (* Read syntax into Twelf's syntax *)
   fun datToSyn (dat: (string, string) LDatum.t): ReconTerm.term = 
      case dat of
         LDatum.Atom (s, pos) => 
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

   (* Slight abuse takes place with bound arguments *)
   (* This function removes -@, -o, and -> in favor of >-> *)
   fun datToRule dctx dat: (string, IntSyn.Exp) LDatum.t =
   let
      fun datExp name dat = 
         LDatum.Node (name, [datToRule dctx dat], LDatum.pos dat) 

      fun reconType dat = 
      let 
         val () = print ("Reconstructing type "^LDatum.toString dat^"\n")
         val syn = datToSyn dat
         val tau = 
            case ReconTerm.reconWithCtx (dctx, ReconTerm.jclass syn) of
               ReconTerm.JClass ((tau, _), IntSyn.Type) => tau
             | _ => raise Fail "Unexpected return from reconstruction"
      in tau end

      fun reconTerm dat tau = 
      let
         val () = print ("Reconstructing term "^LDatum.toString dat^"\n")
         val syn = datToSyn dat
         val t = 
            case ReconTerm.reconWithCtx (dctx, ReconTerm.jof' (syn, tau)) of
               ReconTerm.JOf ((t, _), _, _) => t
             | _ => raise Fail "Unexpected return from term reconstruction"
      in t end
             
      fun cons dctx x typ = IntSyn.Decl (dctx, IntSyn.Dec (SOME x, typ))
   in
      case dat of
         LDatum.Atom (_, pos) => LDatum.Atom (reconType dat, pos)
       | LDatum.List (_, pos) => LDatum.Atom (reconType dat, pos)

       | LDatum.Node ("monad", [dat], pos) => 
            LDatum.Node ("monad", [datToRule dctx dat], pos)
       
       | LDatum.Node ("forall", [LDatum.Atom (x, posx), dat1], pos) => 
         let val tau = IntSyn.newTypeVar dctx in 
            LDatum.Node ("forall", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (tau, posx),
                          datToRule (cons dctx x tau) dat1],
                         pos)
         end
       | LDatum.Node ("forall", [LDatum.Atom (x, posx), dat1, dat2], pos) => 
         let val tau = reconType dat1 in
            LDatum.Node ("forall", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (tau, LDatum.pos dat1),
                          datToRule (cons dctx x tau) dat2],
                         pos)
         end
       | LDatum.Node ("exists", [LDatum.Atom (x, posx), dat1], pos) => 
         let val tau = IntSyn.newTypeVar dctx in 
            LDatum.Node ("exists", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (tau, posx),
                          datToRule (cons dctx x tau) dat1],
                         pos)
         end
       | LDatum.Node ("exists", [LDatum.Atom (x, posx), dat1, dat2], pos) => 
         let val tau = reconType dat1 in
            LDatum.Node ("exists", 
                         [LDatum.Node (x, [], posx), 
                          LDatum.Atom (tau, LDatum.pos dat1),
                          datToRule (cons dctx x tau) dat2],
                         pos)
         end

       | LDatum.Node ("with", [dat1, dat2], pos) =>
            LDatum.Node ("with", [datToRule dctx dat1,
                                  datToRule dctx dat2], pos)
       | LDatum.Node ("lefti", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datToRule dctx dat1,
                                   datToRule dctx dat2], pos)
       | LDatum.Node ("righti", [dat1, dat2], pos) =>
            LDatum.Node ("righti", [datToRule dctx dat1,
                                    datToRule dctx dat2], pos)
       | LDatum.Node ("lolli", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datExp "mobile" dat1,
                                   datToRule dctx dat2], pos)
       | LDatum.Node ("affi", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", [datExp "at" dat1,
                                   datToRule dctx dat2], pos)
       | LDatum.Node ("arrow", [dat1, dat2], pos) =>
            LDatum.Node ("lefti", 
                         [datExp "bang" dat1, datToRule dctx dat2], pos)
       | LDatum.Node ("tensor", [dat1, dat2], pos) =>
            LDatum.Node ("tensor", [datToRule dctx dat1,
                                    datToRule dctx dat2], pos)
       | LDatum.Node ("unify", [dat1, dat2], pos) => 
         let val tau = IntSyn.newTypeVar dctx 
         in
            LDatum.Node ("unify", 
                         [LDatum.Atom (reconTerm dat1 tau, LDatum.pos dat1),
                          LDatum.Atom (reconTerm dat2 tau, LDatum.pos dat2),
                          LDatum.Atom (tau, pos)], pos)
         end

       | LDatum.Node ("bang", [dat], pos) => 
            LDatum.Node ("bang", [datToRule dctx dat], pos) 
       | LDatum.Node ("at", [dat], pos) =>
            LDatum.Node ("at", [datToRule dctx dat], pos)
       | LDatum.Node ("mobile", [dat], pos) =>
            LDatum.Node ("mobile", [datToRule dctx dat], pos) 
       | _ => raise Fail ("Bad SLS syntax: "^LDatum.toString dat)
   end

   fun handleCondec (s, dats, pos) = 
   let
      (* Install a condec *)
      fun install (NONE, _) = raise Fail "Anonymous definition?"
        | install (SOME ConDec, _) =
          let
             val cid = IntSyn.sgnAdd ConDec
             val _ = Names.installConstName cid
             val _ = Origins.installOrigin (cid, ("", NONE))
             val _ = Index.install IntSyn.Ordinary (IntSyn.Const cid) 
             val _ = IndexSkolem.install IntSyn.Ordinary (IntSyn.Const cid)
             val _ = Compile.install IntSyn.Ordinary cid
             val _ = Subordinate.install cid
             val _ = Subordinate.installDef cid
          in () end

      val dat = Fixity.resolve dats
      val syn = datToSyn dat
      val condec = ReconConDec.condecToConDec 
                      (ReconConDec.condec (s, syn), l, false)
   in
    ( install condec
    ; print (s^": ")
    ; print (LDatum.toString dat)
    ; print ".\n")
   end

   fun handleRule (s, dats, pos) = 
   let
      val dat = Fixity.resolve dats
      val _ = Names.varReset IntSyn.Null
      val _ = ReconTerm.resetErrors "fake"
      val syn = datToRule IntSyn.Null dat
      val _ = ReconTerm.checkErrors r
   in
    ( print ("#rule "^s^": ")
    ; print (LDatum.toString dat)
    ; print ".\n")
   end

   (* Effect: initializes Twelf's reconstruction facilities appropriately *)
   fun init () = 
   let
   in
    ( handleCondec ("prop", [PosDatum.List [("type", [], fake_pos)]], fake_pos)
    ; handleCondec ("ord", [PosDatum.List [("type", [], fake_pos)]], fake_pos)
    ; handleCondec ("lin", [PosDatum.List [("type", [], fake_pos)]], fake_pos)
    ; handleCondec ("pers", [PosDatum.List [("type", [], fake_pos)]], fake_pos)
    ; {syntax = 
          (fn (PosDatum.List [("condec", [PosDatum.Atom (s, _)], pos1), 
                               (":", dats, pos2)]) =>
                 handleCondec (s, dats, Pos.union pos1 pos2)
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
