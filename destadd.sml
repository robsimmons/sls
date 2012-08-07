structure DestAdd = 
struct
   val file: TextIO.outstream option ref = ref NONE

   fun print' s = Option.app (fn f => TextIO.output (f, s)) (!file)

   val dest_type: Symbol.symbol option ref = ref NONE
   fun getdesttype () = 
      Exp.Con (valOf (!dest_type), Spine.Nil)

   fun reset () = 
    ( Option.app TextIO.closeOut (!file)
    ; file := NONE
    ; dest_type := NONE)

  
   (* Revision *)

   fun reviseCondec (s, k, class) = 
   let
      fun loop k =
         case k of  
            Exp.PProp Perm.Ord => 
               Exp.Arrow (getdesttype (),
                          Exp.Arrow (getdesttype (),
                                     Exp.PProp Perm.Lin))
          | Exp.Pi (x, t, e) => Exp.Pi (x, t, loop e)
          | Exp.Pii (x, t, e) => Exp.Pii (x, t, loop e)
          | Exp.Arrow (t, e) => Exp.Arrow (t, loop e)
          | e => e
   in
      print' (Symbol.toValue s^": "^PrettyPrint.exp false (loop k)^".\n")
   end

   exception CannotAddDestinations of string * Symbol.symbol
 
   fun reviseRule (r, nprop) =
   let
      fun err s = raise CannotAddDestinations (s, r)

      (* All destinations free or bound in the term *)
      val allvars = ref (Syntax.Query.allvarsNeg 
                            (fn (x, set) => StringRedBlackSet.insert set x)  
                            StringRedBlackSet.empty
                            Signature.empty
                            nprop)
      val max = ref 1

      (* Make generated destinations distinct *)
      fun getvar n isLeft =
      let
         val lcdest = "d"^Int.toString n
         val ucdest = "D"^Int.toString n
      in
         if (StringRedBlackSet.member (!allvars) lcdest 
             orelse StringRedBlackSet.member (!allvars) ucdest
             orelse (Option.isSome (Signature.registered 
                                       (Symbol.fromValue lcdest))))
            then getvar (n+1) isLeft 
         else if isLeft
            then ( allvars := StringRedBlackSet.insert (!allvars) ucdest
                 ; max := n+1
                 ; ucdest)
         else ( allvars := StringRedBlackSet.insert (!allvars) lcdest
              ; max := n+1
              ; lcdest)
      end
      val getvar = fn isLeft => getvar (!max) isLeft


      fun loopSpine (dl, dr) sp = 
         case sp of 
            Spine.Nil => 
               Spine.App (Exp.Var (dl, ~1, Spine.Nil),
                          Spine.App (Exp.Var (dr, ~1, Spine.Nil), 
                                     Spine.Nil))
          | Spine.App (e, sp) => Spine.App (e, loopSpine (dl, dr) sp)
          | Spine.Appi (e, sp) => Spine.Appi (e, loopSpine (dl, dr) sp)

      (* Handle a subgoal *)
      datatype incoming = 
         NoDests of unit
       | LeftDest of string (* We know the leftmost destination only *)
       | RightDest of string (* We know the rightmost destination only *)

      fun loopPrem indest pprop = 
         case (pprop, indest) of
            (PosProp.PAtom (Perm.Ord, a, sp), NoDests ()) =>
            let 
               val destL = getvar true
               val destR = getvar true
            in
               ([destL, destR],
                PosProp.PAtom (Perm.Lin, a, loopSpine (destL, destR) sp))
            end
  
          | (PosProp.PAtom (Perm.Ord, a, sp), LeftDest destR) =>
            let 
               val destL = getvar true
            in
               ([destL],
                PosProp.PAtom (Perm.Lin, a, loopSpine (destL, destR) sp))
            end

          | (PosProp.PAtom (Perm.Ord, a, sp), RightDest destL) =>
            let 
               val destR = getvar true
            in
               ([destR],
                PosProp.PAtom (Perm.Lin, a, loopSpine (destL, destR) sp))
            end

          | (PosProp.PAtom _, _) => ([], pprop)

          | (PosProp.Down (Perm.Ord, _), _) => err "Left-nested proposition"

          | (PosProp.Down _, _) => ([], pprop)

          | (PosProp.One, _) => ([], pprop)

          | (PosProp.Fuse (pprop1, pprop2), LeftDest destL) =>
            let
               val (newdests2, pprop2') = loopPrem indest pprop2
               val indest' = LeftDest (List.hd (newdests2 @ [destL]))
               val (newdests1, pprop1') = loopPrem indest' pprop1
            in
               (newdests1 @ newdests2, PosProp.Fuse (pprop1', pprop2'))
            end
 
          | (PosProp.Fuse (pprop1, pprop2), _) => 
            let
               val (newdests1, pprop1') = loopPrem indest pprop1
               val indest' = 
                  if null newdests1
                     then indest
                  else (RightDest (List.last newdests1))
               val (newdests2, pprop2') = loopPrem indest' pprop2
            in
               (newdests1 @ newdests2, PosProp.Fuse (pprop1', pprop2'))
            end

          | (PosProp.Exists (x, t, pprop1), _) =>
            let
               val (newdests1, pprop1') = loopPrem indest pprop1
            in
               (newdests1, PosProp.Exists (x, t, pprop1'))
            end

          | (PosProp.Unif _, _) => ([], pprop)

      (* Figure out how many ordered propositions belong in a monadic head *)
      fun anaConc pprop = 
         case pprop of 
            PosProp.PAtom (Perm.Ord, _, _) => 1
          | PosProp.Down (Perm.Ord, _) => 1
          | PosProp.Fuse (pprop1, pprop2) => anaConc pprop1 + anaConc pprop2
          | _ => 0

      (* Make enough new destinations for a monadic head *)
      fun makeConcDests dR n = 
         if n <= 1 
            then [dR]
         else getvar false :: makeConcDests dR (n-1)

      (* Introduce the correct new destinations for a monadic head *)
      fun wrapConc [] pprop = raise Fail "wrapConc invariant"
        | wrapConc [_] pprop = pprop
        | wrapConc (dest :: dests) pprop = 
             PosProp.Exists (dest, getdesttype (), wrapConc dests pprop)



      (* Destination-add a set group of destinations to a conclusion *)
      fun loopConc dests pprop = 
         case (pprop, dests) of 
            (PosProp.PAtom (Perm.Ord, a, sp), dL :: dR :: dests) =>
               (dR :: dests,
                PosProp.PAtom (Perm.Lin, a, loopSpine (dL, dR) sp))
          | (PosProp.PAtom (Perm.Ord, _, _), _) => raise Fail "Invariant"
          | (PosProp.PAtom _, _) => (dests, pprop)
          | (PosProp.Down (Perm.Ord, nprop), dL :: dR :: dests) =>
               err "Nested rules not implemented"
          | (PosProp.Down (Perm.Ord, _), _) => raise Fail "Invariant"
          | (PosProp.Down (perm, nprop), _) =>
               err "Nested rules not implemented"
          | (PosProp.One, _) => (dests, pprop)
          | (PosProp.Fuse (pprop1, pprop2), _) => 
            let 
               val (dests1, pprop1') = loopConc dests pprop1
               val (dests2, pprop2') = loopConc dests1 pprop2
            in
               (dests2, PosProp.Fuse (pprop1', pprop2'))
            end
          | (PosProp.Exists (x, t, pprop1), _) => 
            let 
               val (dests', pprop1') = loopConc dests pprop1
            in
               (dests', PosProp.Exists (x, t, pprop1'))
            end
          | (PosProp.Unif _, _) => (dests, pprop)

      and loopRule dests nprop = 
         case (nprop, dests) of
            (NegProp.NAtom _, []) => ([], nprop)
          | (NegProp.NAtom _, _) => err "Ordered backwards-chaining"
          | (NegProp.Lax pprop, []) => 
               if anaConc pprop > 0 
                  then err "Order in conclusion but not in any premise"
               else ([], NegProp.Lax pprop)
          | (NegProp.Lax pprop, _) => 
            let
               val dL = List.hd dests
               val dR = List.last dests
               val n = anaConc pprop
               val () = print ("ANSWER: "^Int.toString n^"\n")
               val dests = dL :: makeConcDests dR n
            in
               if n > 0 
                  then (dests, 
                        NegProp.Lax 
                           (wrapConc (List.tl dests) 
                               (#2 (loopConc dests pprop))))
               else (dests, 
                     NegProp.Lax
                        (PosProp.Fuse 
                            (PosProp.Unif (Exp.Var (dL, ~1, Spine.Nil),
                                           Exp.Var (dR, ~1, Spine.Nil)),
                             #2 (loopConc [] pprop))))
            end
          | (NegProp.Lefti (pprop, nprop), _) => 
            let
               val indest = 
                  if null dests 
                     then NoDests () 
                  else (LeftDest (List.hd dests))
               val (newdests, pprop') = loopPrem indest pprop
               val (alldests, nprop') = loopRule (newdests @ dests) nprop
            in
               (alldests, NegProp.Lefti (pprop', nprop'))
            end 
          | (NegProp.Righti (pprop, nprop), _) => 
            let
               val indest = 
                  if null dests 
                     then NoDests () 
                  else (RightDest (List.last dests))
               val (newdests, pprop') = loopPrem indest pprop
               val (alldests, nprop') = loopRule (dests @ newdests) nprop
            in
               (alldests, NegProp.Righti (pprop', nprop'))
            end 
          | (NegProp.With _, _) => err "Cannot add destinations to with"
          | (NegProp.All (x, t, nprop), _) => 
            let 
               val (alldests, nprop') = loopRule dests nprop
            in 
               (alldests, NegProp.All (x, t, nprop'))
            end
          | (NegProp.Alli (x, t, nprop), _) => 
            let 
               val (alldests, nprop') = loopRule dests nprop
            in 
               (alldests, NegProp.Alli (x, t, nprop'))
            end
            
      (* Introduce the correct new destinations for a monadic head *)
      fun wrapRule ([], nprop) = nprop
        | wrapRule (dest :: dests, nprop) = 
             NegProp.Alli (dest, getdesttype (), wrapRule (dests, nprop))

      val nprop' = wrapRule (loopRule [] nprop)
   in
      print' (Symbol.toValue r^": "^PrettyPrint.neg false nprop'^".\n")
   end
  

   (* #destadd *)

   fun failOperation pos = 
       raise Fail ("Ill formed #destadd (expected form \
                   \'#destadd \"filename\" dest.'),\
                   \ where dest is a type."
                   ^Pos.toString pos)

   fun handleOperation ([(PosDatum.Atom (filename, _)), 
                         (PosDatum.Atom (dest, _))], 
                        pos) =
       let val dest_cid = Symbol.fromValue dest 
       in 
         (if size filename = 0 orelse String.sub (filename, 0) <> #"\""
          then failOperation pos
          else case !file of
                  NONE => 
                   ( file := SOME (TextIO.openOut 
                                     (String.extract (filename, 1, NONE)))
                   ; dest_type := SOME dest_cid
                   ; case Signature.registered dest_cid of
                        NONE => 
                         ( Signature.register dest_cid pos
                         ; print' (dest^": type.\n"))
                      | SOME pos' => 
                           (* TODO: Check that it's the correct kind? *)
                           print' (";; "^dest^" already \
                                   \declared at "^Pos.toString pos'^"\n"))
           | SOME _ => 
                raise Fail ("Already defunctionalizing! "^Pos.toString pos))
       end

     | handleOperation (_, pos) = failOperation pos

   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("destadd", 
                               [PosDatum.Atom ("stop", _)], pos)]) => 
                 (reset (); print "#destadd stop.\n")
            | (PosDatum.List [("destadd", dats, pos)]) => 
                ( handleOperation (dats, pos)
                ; print "#destadd start.\n")
            | _ => ()),
       condec = fn x => if Option.isSome (!file) then reviseCondec x else (),
       rule = fn x => if Option.isSome (!file) then reviseRule x else (),
       reset = reset}

end
