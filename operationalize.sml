structure Operationalize =
struct
   val db = Syntax.empty (* Caching *)

   val forwardChain: (Symbol.symbol * Symbol.symbol) 
                     SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty

   val file: TextIO.outstream option ref = ref NONE

   fun print' s = Option.app (fn f => TextIO.output (f, s)) (!file)



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

   val doTailCall = ref true

   fun isC nprop = 
      case Syntax.Query.negHeadsList db nprop of
         [NegProp.NAtom (a, sp)] => SymbolRedBlackDict.member (!forwardChain) a
       | _ => false

   fun update_bound n (x, db) = StringRedBlackDict.insert db n (fn m => m) 

   fun ins (x, set) = (StringRedBlackSet.insert set x)

   (* Turns a proposition that is morally of the form
    *
    * An >-> ... >-> A1 >-> (a t0 tn+1)
    *
    * into a tuple 
    * 
    * (n, [(An,fvN),...,(A1,fv1)], fv, fv0, t0, tn+1)
    * 
    * where fvi is the free variables bound in Ai (or, when i=0, the 
    * variables bound in t0) in their original dependency order. *)
   fun prepC ctx_in nprop =
      case nprop of
         NegProp.NAtom (a, sp) => 
         let
            val (spin, spout) = splitSpine (Modes.lookup a) sp
            (* val () = print ("ZERO: "^PrettyPrint.neg false nprop^"\n") *)
            val fv0 =
               Syntax.Query.freevarsSpine ins StringRedBlackSet.empty db spin
            val (ctx0, ctx) = Context.partition ctx_in fv0
         in
            (1, [], ctx, (ctx0, a, spin, spout))
         end
       | NegProp.Lefti (ppropi, nprop) =>
         let
            (* val () = print ("STEP: "^PrettyPrint.pos false ppropi^"\n") *)
            val fvi = 
               Syntax.Query.freevarsPos ins StringRedBlackSet.empty db ppropi
            val (i, props, ctx, hd) = prepC ctx_in nprop
            val (ctxi, ctx) = Context.partition ctx fvi
         in
            (i+1, ((ppropi, ctxi) :: props), ctx, hd)
         end
       | NegProp.Righti (ppropi, nprop) =>
         let
            (* val () = print ("STEP: "^PrettyPrint.pos false ppropi^"\n") *)
            val fvi =  
               Syntax.Query.freevarsPos ins StringRedBlackSet.empty db ppropi
            val (i, props, ctx, hd) = prepC ctx_in nprop
            val (ctxi, ctx) = Context.partition ctx fvi
         in
            (i+1, ((ppropi, ctxi) :: props), ctx, hd)
         end
       | NegProp.All (x, t, nprop) =>
         let
            val (i, props, ctx, hd) = prepC ((x, t) :: ctx_in) nprop
         in
            (i, props, ctx, hd)
         end
       | NegProp.Alli (x, t, nprop) =>
         let
            val (i, props, ctx, hd) = prepC ((x, t) :: ctx_in) nprop
         in
            (i, props, ctx, hd)
         end
       | _ => raise Fail ("Proposition not in operationalizable form \
                          \(C): "^PrettyPrint.neg false nprop^"'")    
   fun rewriteC nprop =
   let
      val (_, props, _, (ctx0, a, spin, spout)) = prepC [] nprop
      val (eval_a, retn_a) = SymbolRedBlackDict.lookup (!forwardChain) a

      (* Tail-call helper function: returns true if retn_a and retn_b are 
       * exactly the same spine, each bind only variables mentioned in 
       * the bound-here context, and each variable is only mentioned once. *)
      fun checkgen ctx retn_a retn_b = 
      let 
         fun remove x [] = NONE
           | remove (x: string) ((y, t) :: ys) =
                if x = y then SOME ys 
                else Option.map (fn ys => (y, t) :: ys) (remove x ys)
      in (* Note: what does it mean that we only say "yes" if the implicit
          * and explicit bindings match? Is that overly restrictive? *)
         case (retn_a, retn_b) of
            (Spine.Nil, Spine.Nil) => true
          | (Spine.App (Exp.Var (xa, _, Spine.Nil), retn_a),
             Spine.App (Exp.Var (xb, _, Spine.Nil), retn_b)) =>
                if EQUAL = String.compare (xa, xb)
                then (case remove xa ctx of NONE => false
                       | SOME ctx => checkgen ctx retn_a retn_b)
                else false
          | (Spine.Appi (Exp.Var (xa, _, Spine.Nil), retn_a),
             Spine.Appi (Exp.Var (xb, _, Spine.Nil), retn_b)) =>
                if EQUAL = String.compare (xa, xb)
                then (case remove xa ctx of NONE => false
                       | SOME ctx => checkgen ctx retn_a retn_b)
                else false
          | _ => false
      end

      (* Attempt tail-call optimization, return NONE if it doesn't apply *)
      val tailCall =
         if not (!doTailCall) then (fn x => NONE)
         else fn [(PosProp.Down (Perm.Pers, NegProp.NAtom (b, spi)), ctxi)] =>
                   (case SymbolRedBlackDict.find (!forwardChain) b of
                       NONE => NONE
                     | SOME (eval_b, retn_b) => 
                       let val (spin_i, spout_i) = 
                              splitSpine (Modes.lookup b) spi
                       in if checkgen ctxi spout_i spout
                          then SOME (NegProp.Lax 
                                        (PosProp.PAtom 
                                            (Perm.Ord, eval_b, spin_i)))
                          else NONE
                       end)
               | _ => NONE

      (* Main loop that implements the [[Ai...An]](retn_a, spout) function *)
      fun loop props = 
      let val wrap = Context.wrap
      in case tailCall props of 
            SOME nprop => nprop
          | NONE => 
              (case props of 
                  [] => NegProp.Lax (PosProp.PAtom (Perm.Ord, retn_a, spout))
                | ((p as PosProp.PAtom (Perm.Pers, b, sp), ctxi) :: props) =>
                     wrap ctxi (NegProp.Lefti (p, loop props))
                | ((p as PosProp.Down (Perm.Pers, NegProp.NAtom (b, spi)), ctxi)
                  :: props) =>
                     (case SymbolRedBlackDict.find (!forwardChain) b of
                        NONE => wrap ctxi (NegProp.Lefti (p, loop props))
                      | SOME (eval_b, retn_b) =>
                        let val (spin_i, spout_i) = 
                               splitSpine (Modes.lookup b) spi
                           val npropCont = 
                              wrap ctxi (NegProp.Lefti 
                                            (PosProp.PAtom 
                                                (Perm.Ord, retn_b, spout_i),
                                            loop props))
                        in NegProp.Lax
                              (PosProp.Fuse
                                  (PosProp.PAtom (Perm.Ord, eval_b, spin_i),
                                   PosProp.Down (Perm.Ord, npropCont)))
                        end)
                | ((PosProp.Down (Perm.Pers, nprop), ctxi) :: props) =>
                     wrap ctxi (NegProp.Lefti 
                                   (PosProp.Down (Perm.Pers, rewriteG nprop),
                                   loop props))
                | ((pprop, ctxi) :: pprops) =>
                     raise Fail ("Proposition not in operationalizable form \
                                 \(C subgoal): "^PrettyPrint.pos false pprop
                                 ^"'"))
      end
   in
      Context.wrapi ctx0 
         (NegProp.Lefti (PosProp.PAtom (Perm.Ord, eval_a, spin),
                         loop (rev props)))
   end

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

   (* Revise constant declarations *)

   fun reviseCondec (s, k, class) = 
      case SymbolRedBlackDict.find (!forwardChain) s of
         NONE => print' (Symbol.toValue s^": "^PrettyPrint.exp false k^".\n")
       | SOME (eval, retn) => 
           (case Modes.find s of
               NONE => raise Fail ("Cannot operationalize '"^Symbol.toValue s
                                   ^"' without a mode declaration")
             | SOME mds =>
               let val (keval, kretn) = splitKnd mds k
               in print' (Symbol.toValue eval^": "
                         ^PrettyPrint.exp false keval^".\n")
                ; print' (Symbol.toValue retn^": "
                         ^PrettyPrint.exp false kretn^".\n")
               end)


   
   (* Revise rules *)

   fun reviseRule (r, nprop) =
      if isC nprop 
      then print' (Symbol.toValue r^": "^PrettyPrint.neg false (rewriteC nprop)
                  ^".\n")
      else print' (Symbol.toValue r^": "^PrettyPrint.neg false (rewriteD nprop)
                  ^".\n")



   (* #operationalize *)

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



   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("operationalize", 
                               [PosDatum.Atom ("stop", _)], pos)]) => 
                 (forwardChain := SymbolRedBlackDict.empty
                ; case !file of 
                     SOME file => (TextIO.closeOut file)
                   | NONE => raise Fail ("Not operationalizing!"
                                         ^Pos.toString pos)
                ; file := NONE
                ; print "#operationalize stop.\n")
            | (PosDatum.List [("operationalize", dats, pos)]) => 
                 (handleOperation (dats, pos)
                ; print "#operationalize start.\n")
            | _ => ()),
       condec = fn x => if Option.isSome (!file) then reviseCondec x else (),
       rule = fn x => if Option.isSome (!file) then reviseRule x else (),
       reset = fn () => 
                 (forwardChain := SymbolRedBlackDict.empty
                ; Option.app TextIO.closeOut (!file)
                ; file := NONE)}

end
