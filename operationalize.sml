structure Operationalize =
struct
   val db = Syntax.empty (* Caching *)

   val forwardChain: (Symbol.symbol * Symbol.symbol) 
                     SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty

   val file: TextIO.outstream option ref = ref NONE

   fun print s = Option.app (fn f => TextIO.output (f, s)) (!file)

   fun mappings 
          (PosDatum.List 
              [("(", [PosDatum.Atom (old, _),
                      PosDatum.Atom ("~>", _),
                      PosDatum.Atom (eval, _), 
                      PosDatum.Atom (retn, _)], pos1), 
               (")", [], pos2)]) =
          forwardChain := SymbolRedBlackDict.insert (!forwardChain)
                             (Symbol.fromValue old)
                             (Symbol.fromValue eval, Symbol.fromValue retn)
     | mappings dats = 
          raise Fail "Bad mappings (expected '(ev ~> eval retn)')"

   fun failOperation pos = 
       raise Fail ("Ill formed #operationalize (expected form \
                   \'#operationalize \"filename\" (ev ~> eval retn) ...': "
                   ^Pos.toString pos)
   fun handleOperation ((PosDatum.Atom (filename, _) :: dats), pos) =
         (if size filename = 0 orelse String.sub (filename, 0) <> #"\""
          then failOperation pos
          else case !file of
                  NONE => 
                    (app mappings dats
                   ; file := SOME (TextIO.openOut 
                                     (String.extract (filename, 1, NONE))))
           | SOME _ => 
                raise Fail ("Already operationalizing! "^Pos.toString pos))
     | handleOperation (_, pos) = failOperation pos



   (* REWRITING DEDUCTIVE RULES *)

   fun splitSpine [] Spine.Nil = (Spine.Nil, Spine.Nil)
     | splitSpine (md :: mds) (Spine.App (exp, sp)) = 
       let val (sp1, sp2) = splitSpine mds sp
       in case md of
             Mode.Input => (Spine.App (exp, sp1), sp2)
           | Mode.Output => (sp1, Spine.App (exp, sp2))
       end
     | splitSpine (md :: mds) (Spine.Appi (exp, sp)) = 
       let val (sp1, sp2) = splitSpine mds sp
       in case md of
             Mode.Input => (Spine.Appi (exp, sp1), sp2)
           | Mode.Output => (sp1, Spine.Appi (exp, sp2))
       end
     | splitSpine _ _ = raise Fail "Invariant"

   fun rewriteD' pprop = 
      case pprop of 
         PosProp.PAtom (Perm.Pers, a, sp) => PosProp.PAtom (Perm.Pers, a, sp)
       | PosProp.Down (Perm.Pers, NegProp.NAtom (a, sp)) =>
           (case SymbolRedBlackDict.find (!forwardChain) a of 
               NONE => pprop
             | SOME (eval, retn) => 
               let 
                  val mds = Modes.lookup a
                  val (speval, spretn) = splitSpine mds sp
                  val evalP = PosProp.PAtom (Perm.Ord, eval, speval)
                  val retnP = PosProp.PAtom (Perm.Ord, retn, spretn)
               in PosProp.Down 
                     (Perm.Pers, NegProp.Lefti (evalP, NegProp.Lax retnP))
               end)
       | PosProp.Down (Perm.Pers, nprop) => 
            PosProp.Down (Perm.Pers, rewriteG nprop)
       | _ => raise Fail ("Proposition not in operationalizable form \
                          \(D subgoal): "^PrettyPrint.pos false pprop^"'")

   and rewriteD nprop =
      case nprop of 
         NegProp.NAtom (a, sp) => 
            if SymbolRedBlackDict.member (!forwardChain) a 
            then raise Fail ("Can't translate concurrent '"^Symbol.toValue a
                             ^"' in this position")
            else NegProp.NAtom (a, sp)
       | NegProp.Lefti (pprop1, nprop2) =>
            NegProp.Lefti (rewriteD' pprop1, rewriteD nprop2) 
       | NegProp.Righti (pprop1, nprop2) =>
            NegProp.Righti (rewriteD' pprop1, rewriteD nprop2) 
       | NegProp.All (x, t, nprop) => NegProp.All (x, t, rewriteD nprop)
       | NegProp.Alli (x, t, nprop) => NegProp.Alli (x, t, rewriteD nprop)
       | _ => raise Fail ("Proposition not in operationalizable form (D): '"
                          ^PrettyPrint.neg false nprop^"'")

   and rewriteG' pprop = 
      case pprop of 
         PosProp.PAtom (Perm.Pers, a, sp) => PosProp.PAtom (Perm.Pers, a, sp)
       | PosProp.Down (Perm.Pers, nprop) => 
            PosProp.Down (Perm.Pers, rewriteD nprop)
       | _ => raise Fail ("Proposition not in operationalizable form \
                          \(G subgoal): "^PrettyPrint.pos false pprop^"'")

   and rewriteG nprop = 
      case nprop of 
         NegProp.NAtom (a, sp) => 
            if SymbolRedBlackDict.member (!forwardChain) a 
            then raise Fail ("Can't translate concurrent '"^Symbol.toValue a
                             ^"' in this position")
            else NegProp.NAtom (a, sp)
       | NegProp.Lefti (pprop1, nprop2) =>
            NegProp.Lefti (rewriteG' pprop1, rewriteG nprop2) 
       | NegProp.Righti (pprop1, nprop2) =>
            NegProp.Righti (rewriteG' pprop1, rewriteG nprop2) 
       | NegProp.All (x, t, nprop) => NegProp.All (x, t, rewriteG nprop)
       | NegProp.Alli (x, t, nprop) => NegProp.Alli (x, t, rewriteG nprop)
       | _ => raise Fail ("Proposition not in operationalizable form (G): '"
                          ^PrettyPrint.neg false nprop^"'")



   (* REWRITING CONCURRENT RULES *)

   fun isC nprop = 
      case Syntax.Query.negHeadsList db nprop of
         [NegProp.NAtom (a, sp)] => SymbolRedBlackDict.member (!forwardChain) a
       | _ => false

(*
   fun update_bound n (x, db) = StringRedBlackDict.insert db n (fn m => m) 

   fun prepC db nprop =
      case nprop of
         NegProp.NAtom (a, sp) => 
         let
            val (spin, _) = splitSpine sp
            val db = Syntax.Query.fvNeg (update_bound 0) db
         in
             
         end
       | NegProp.Lefti 
    
*)





   (* REWRITING KINDS *)

   (* Note: this totally kills the de Bruijn indices, which is why we don't
    * use de Bruijn indices for printing *)
   fun splitKnd [] Exp.NProp = (Exp.PProp Perm.Ord, Exp.PProp Perm.Ord)
     | splitKnd (md :: mds) (Exp.Pi (x, t, k)) =
       let val (k1, k2) = splitKnd mds k
       in case md of
             Mode.Input => (Exp.Pi (x, t, k1), k2)
           | Mode.Output => (k1, Exp.Pi (x, t, k2))          
       end 
     | splitKnd (md :: mds) (Exp.Pii (x, t, k)) =
       let val (k1, k2) = splitKnd mds k
       in case md of
             Mode.Input => (Exp.Pii (x, t, k1), k2)
           | Mode.Output => (k1, Exp.Pii (x, t, k2))          
       end 
     | splitKnd (md :: mds) (Exp.Arrow (t, k)) =
       let val (k1, k2) = splitKnd mds k
       in case md of
             Mode.Input => (Exp.Arrow (t, k1), k2)
           | Mode.Output => (k1, Exp.Arrow (t, k2))          
       end 
     | splitKnd _ _ = raise Fail "Invariant"

   fun reviseCondec (s, k, class) = 
      case SymbolRedBlackDict.find (!forwardChain) s of
         NONE => print (Symbol.toValue s^": "^PrettyPrint.exp false k^".\n")
       | SOME (eval, retn) => 
           (case Modes.find s of
               NONE => raise Fail ("Cannot operationalize '"^Symbol.toValue s
                                   ^"' without a mode declaration")
             | SOME mds =>
               let val (keval, kretn) = splitKnd mds k
               in print (Symbol.toValue eval^": "
                         ^PrettyPrint.exp false keval^".\n")
                ; print (Symbol.toValue retn^": "
                         ^PrettyPrint.exp false kretn^".\n")
               end)

   fun reviseRule (r, nprop) =
      if isC nprop 
      then ()
      else print (Symbol.toValue r^": "^PrettyPrint.neg false (rewriteD nprop)
                  ^".\n")

   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("operationalize", 
                               [PosDatum.Atom ("stop", _)], pos)]) => 
                 (forwardChain := SymbolRedBlackDict.empty
                ; case !file of 
                     SOME file => (TextIO.closeOut file)
                   | NONE => raise Fail ("Not operationalizing!"
                                         ^Pos.toString pos)
                ; file := NONE)
            | (PosDatum.List [("operationalize", dats, pos)]) => 
                 handleOperation (dats, pos)
            | _ => ()),
       condec = reviseCondec,
       rule = reviseRule,
       reset = fn () => 
                 (forwardChain := SymbolRedBlackDict.empty
                ; Option.app TextIO.closeOut (!file)
                ; file := NONE)}

end
