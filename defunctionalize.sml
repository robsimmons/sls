structure Defunctionalize =
struct
   val db = Syntax.empty (* Caching *)

   val file: TextIO.outstream option ref = ref NONE

   fun print' s = Option.app (fn f => TextIO.output (f, s)) (!file)

   val cont_ord: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_lin: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_aff: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val cont_pers: (Symbol.symbol * Symbol.symbol) option ref = ref NONE
   val used_names: SymbolRedBlackSet.set ref = ref SymbolRedBlackSet.empty
   fun reset () = 
     (Option.app TextIO.closeOut (!file)
    ; file := NONE
    ; cont_ord := NONE
    ; cont_lin := NONE
    ; cont_aff := NONE
    ; cont_pers := NONE
    ; used_names := SymbolRedBlackSet.empty)

   fun register name = 
      used_names := SymbolRedBlackSet.insert (!used_names) name

   fun freshname base = 
   let fun loop n =  
       let val candidate = Symbol.fromValue (base^Int.toString n)
       in if SymbolRedBlackSet.member (!used_names) candidate
          then loop (n+1) else (register candidate; candidate)
       end
   in loop 1 end

   fun ins (x, set) = (StringRedBlackSet.insert set x)

   fun defunctionalize rule_root frame_root = 
   let 
      exception CannotDefunctionalize of int

      fun pprocess ctx n pprop =  
         case pprop of 
            PosProp.PAtom (perm, a, spi) => (n, pprop)
          | PosProp.Down (perm, nprop) =>
           (let 
               val (a, t) = 
                  case perm of
                     Perm.Ord => valOf (!cont_ord)
                   | Perm.Lin => valOf (!cont_lin)
                   | Perm.Aff => valOf (!cont_aff)
                   | Perm.Pers => valOf (!cont_pers)

               val fv = Syntax.Query.freevarsNeg ins StringRedBlackSet.empty
                           db nprop
               val (relevant_ctx, _) = Context.partition ctx fv

               (* Form and declare new frame *)
               val frame = freshname frame_root
               val frame_type = 
                  Context.wrape relevant_ctx (Exp.Con (t, Spine.Nil))
               val () = print' (Symbol.toValue frame^": "
                                ^PrettyPrint.exp false frame_type ^".\n")
 
               val (n', defunct_nprop) = nprocess relevant_ctx (n+1) nprop
               val cont_spine = 
                  List.foldl Spine.App Spine.Nil
                     (map (fn (x, _) => Exp.Var (x, ~1, Spine.Nil)) 
                         relevant_ctx)
               val cont_arg = Exp.Con (frame, cont_spine)
               val cont = 
                  PosProp.PAtom (perm, a, Spine.App (cont_arg, Spine.Nil))
               val new_rule = 
                  Context.wrapi relevant_ctx 
                     (NegProp.Lefti (cont, defunct_nprop))
               val rule_name = rule_root^Int.toString n
               val () = register (Symbol.fromValue rule_name)
               val new_rule' = Uncurry.uncurry_unsafe new_rule
               val () = print' (rule_name^": " 
                                ^PrettyPrint.neg false new_rule'^".\n") 
            in 
               (n', cont)
            end (* No way to defunctionalze? Don't. *)
             handle Option => (n, pprop)
                  | CannotDefunctionalize n' => (n', pprop))
                  
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
               (n', PosProp.Exists (x, t, pprop'))
            end
          | PosProp.Unif (t, s) => (n, pprop)

      and nprocess ctx n nprop = 
         case nprop of 
            NegProp.NAtom _ => raise CannotDefunctionalize n
          | NegProp.Lax pprop => 
            let val (n', pprop') = pprocess ctx n pprop
            in (n', NegProp.Lax pprop') end
          | NegProp.Lefti (pprop, nprop) => 
            let val (n', nprop') = nprocess ctx n nprop
            in (n', NegProp.Lefti (pprop, nprop')) end
          | NegProp.Righti (pprop, nprop) => 
            let val (n', nprop') = nprocess ctx n nprop
            in (n', NegProp.Righti (pprop, nprop')) end
          | NegProp.With (nprop1, nprop2) => 
            raise CannotDefunctionalize n (* Uncurry doesn't handle this case *)
          | NegProp.All (x, t, nprop) => 
            let val (n', nprop') = nprocess ((x, t) :: ctx) n nprop
            in (n', NegProp.All (x, t, nprop')) end
          | NegProp.Alli (x, t, nprop) => 
            let val (n', nprop') = nprocess ((x, t) :: ctx) n nprop
            in (n', NegProp.Alli (x, t, nprop')) end
   in 
      fn nprop =>
         (SOME (#2 (nprocess [] 1 nprop))
          handle CannotDefunctionalize _ => NONE)
   end

   fun reviseCondec (s, k, class) = 
     (register s
    ; print' (Symbol.toValue s^": "^PrettyPrint.exp false k^".\n"))
       
   fun reviseRule (r, nprop) = 
   let 
      val rule_root = Symbol.toValue r
      val frame_root = 
         List.last (String.tokens (not o Char.isAlphaNum) rule_root)
   in
     (register r
    ; case defunctionalize rule_root frame_root nprop of
         NONE => print' (rule_root^": "^PrettyPrint.neg false nprop^".\n")
       | SOME nprop => 
            print' (rule_root^": "^PrettyPrint.neg false nprop^".\n"))
   end


   (* #defunctionalize *)

   fun failOperation pos = 
       raise Fail ("Ill formed #defunctionalize (expected form \
                   \'#defunctionalize \"filename\" (cont frame : perm) ...'),\
                   \ where\
                     \ cont is an undeclared predicate, frame is a declared\
                     \ type, and perm one of {ord, lin, aff, pers}"
                   ^Pos.toString pos)

   fun mappings pos
          (PosDatum.List 
              [("(", [PosDatum.Atom (cont, _),
                      PosDatum.Atom (frame, _),
                      PosDatum.Atom (":", _), 
                      PosDatum.List [(perm, [], posprem)]], pos1), 
               (")", [], pos2)]) =
       let 
          val frame_cid = Symbol.fromValue frame
          val cont_cid = Symbol.fromValue cont
          fun store cell =  
            (print' (cont^": "^frame^" -> prop "^perm^".\n")
           ; cell := SOME (cont_cid, frame_cid))
       in 
         (case Signature.find frame_cid of
                NONE => (print' (frame^": type.\n"); register frame_cid)
              | SOME Exp.Typ => ()
              | SOME exp => raise Fail ("Frame "^frame^" already declared as\
                                        \ a constant of type "
                                        ^PrettyPrint.exp false exp)
        ; case perm of
             "ord" => store cont_ord
           | "lin" => store cont_lin
           | "aff" => store cont_aff
           | "pers" => store cont_pers
           | _ => raise failOperation posprem
        ; register cont_cid)
       end
     | mappings pos dats = failOperation pos

   fun handleOperation ((PosDatum.Atom (filename, _) :: dats), pos) =
         (if size filename = 0 orelse String.sub (filename, 0) <> #"\""
          then failOperation pos
          else case !file of
                  NONE => 
                    (file := SOME (TextIO.openOut 
                                     (String.extract (filename, 1, NONE)))
                   ; app (mappings pos) dats)
           | SOME _ => 
                raise Fail ("Already defunctionalizing! "^Pos.toString pos))
     | handleOperation (_, pos) = failOperation pos

   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("defunctionalize", 
                               [PosDatum.Atom ("stop", _)], pos)]) => 
                 (reset (); print "#defunctionalize stop.\n")
            | (PosDatum.List [("defunctionalize", dats, pos)]) => 
                 (handleOperation (dats, pos)
                ; print "#defunctionalize start.\n")
            | _ => ()),
       condec = fn x => if Option.isSome (!file) then reviseCondec x else (),
       rule = fn x => if Option.isSome (!file) then reviseRule x else (),
       reset = reset}
end
