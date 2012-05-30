(* Fixity datums: factor out into lamda-reader *)
structure LDatum =
struct
   datatype ('label, 'atom) datum = 
      Atom of 'atom * Pos.t
    | Node of 'label * ('label, 'atom) datum list * Pos.t
    | List of ('label, 'atom) datum list * Pos.t

   type ('label, 'atom) t = ('label, 'atom) datum

   fun pos dat = 
      case dat of 
         Atom (_, pos) => pos
       | Node (_, _, pos) => pos
       | List (_, pos) => pos
 
   fun toString dat = 
      case dat of 
         Atom (s, _) => s
       | Node (s, [], _) => "("^s^")" 
       | Node (s, dats, _) => 
            "("^s^" "^String.concatWith " " (map toString dats)^")" 
       | List (dats, _) => 
            "["^String.concatWith " " (map toString dats)^"]"
end

(* Fixity resolution *)
structure Fixity:> sig
   val resolve: string PosDatum.t list -> (string, string) LDatum.t
   (* exception concrete syntax or something like that *)
end = 
struct
   structure Fix = 
   IntFixityFn (type tok = string PosDatum.t
                type result = (string, string) LDatum.t)

   val fake_coord = Coord.init "fake"
   val fake_pos = Pos.pos fake_coord fake_coord

   fun resolve dats = 
   let      
      (* XXX should be snoc lists, somehow *)
      fun adj (LDatum.List (xs, pos)) y = 
             LDatum.List (xs @ [ y ], Pos.union pos (LDatum.pos y))
        | adj x y = 
             LDatum.List (x :: y :: [], Pos.union (LDatum.pos x) (LDatum.pos y))

      fun mk g prec f =
         Sum.INR (g (prec, f))

      fun node name a b = 
         LDatum.Node (name, [a, b], Pos.union (LDatum.pos a) (LDatum.pos b))

      fun mkForward name = mk Fix.Infixr 3 (fn a => fn b => node name a b)

      fun mkBackward name = mk Fix.Infixl 2 (fn b => fn a => node name a b)

      fun mkModal name pos =
         Sum.INR (Fix.Prefix
                     (5, fn a => LDatum.Node (name, [a], 
                                              Pos.union pos (LDatum.pos a))))

      fun token dat = 
         case dat of 
            PosDatum.Atom a => Sum.INL (LDatum.Atom a)

          (* Brackets *)
          | PosDatum.List [("(", dats, pos1), (")", [], pos2)] =>
               Sum.INL (resolve dats)
          | PosDatum.List [("{", dats, pos1), ("}", [], pos2)] =>
               Sum.INL (LDatum.Node ("monad", [resolve dats],
                                     Pos.union pos1 pos2))

          (* Binders *)
          | PosDatum.List (parts as (("All", _, _) :: _)) => 
               Sum.INL (LDatum.Node ("forall", map (resolve o #2) parts,
                                     PosDatum.pos dat))
          | PosDatum.List (parts as (("Pi", _, _) :: _)) => 
               Sum.INL (LDatum.Node ("pi", map (resolve o #2) parts,
                                     PosDatum.pos dat))
          | PosDatum.List (parts as (("Exists", _, _) :: _)) => 
               Sum.INL (LDatum.Node ("exists", map (resolve o #2) parts,
                                     PosDatum.pos dat))
          | PosDatum.List (parts as (("\\", _, _) :: _)) => 
               Sum.INL (LDatum.Node ("lambda", map (resolve o #2) parts,
                                     PosDatum.pos dat))

          (* Fixity 1 *)
          | PosDatum.List [("&", [], _)] => 
               mk Fix.Infixr 1 (fn a => fn b => node "with" a b)

          (* Fixity 2 *)
          | PosDatum.List [("<-<", [], _)] => mkBackward "lefti" 
          | PosDatum.List [("<<-", [], _)] => mkBackward "righti" 
          | PosDatum.List [("o-", [], _)] => mkBackward "lolli" 
          | PosDatum.List [("@-", [], _)] => mkBackward "affi" 
          | PosDatum.List [("<-", [], _)] => mkBackward "arrow" 

          (* Fixity 3 *)
          | PosDatum.List [(">->", [], _)] => mkForward "lefti" 
          | PosDatum.List [("->>", [], _)] => mkForward "righti" 
          | PosDatum.List [("-o", [], _)] => mkForward "lolli" 
          | PosDatum.List [("-@", [], _)] => mkForward "affi" 
          | PosDatum.List [("->", [], _)] => mkForward "arrow" 

          (* Fixity 4 *)
          | PosDatum.List [("*", [], _)] => 
               mk Fix.Infixr 1 (fn a => fn b => node "tensor" a b)

          (* Fixity 5 *)
          | PosDatum.List [("==", [], pos)] => 
               mk Fix.Infix 5 (fn a => fn b => node "unify" a b)

          | PosDatum.List [("!", [], pos)] => mkModal "bang" pos
          | PosDatum.List [("@", [], pos)] => mkModal "at" pos
          | PosDatum.List [("$", [], pos)] => mkModal "mobile" pos

          | PosDatum.List [("one", [], pos)] => 
               Sum.INL (LDatum.Node ("one", [], pos))
          | PosDatum.List [("type", [], pos)] => 
               Sum.INL (LDatum.Node ("type", [], pos))
          | PosDatum.List [("prop", [], pos)] => 
               Sum.INL (LDatum.Node ("prop", [], pos))
          | PosDatum.List [("prop", [PosDatum.List [("ord", _, _)]], pos)] => 
               Sum.INL (LDatum.Node ("ord", [], pos))
          | PosDatum.List [("prop", [PosDatum.List [("lin", _, _)]], pos)] => 
               Sum.INL (LDatum.Node ("lin", [], pos))
          | PosDatum.List [("prop", [PosDatum.List [("aff", _, _)]], pos)] => 
               Sum.INL (LDatum.Node ("aff", [], pos))
          | PosDatum.List [("prop", [PosDatum.List [("pers", _, _)]], pos)] => 
               Sum.INL (LDatum.Node ("pers", [], pos))

          | PosDatum.List [] => raise Fail "Empty syntax"
          | PosDatum.List ((s,_,_) :: _) => 
               raise Fail ("Internal: can't deal with '"^s^"'")

      val resolver = 
         Fix.AdjResolver 
            {adj = adj,
             adj_prec = 6,
             adj_assoc = Fix.LEFT,
             (* XXX get surrounding tokens to get position *)
             adj_tok = PosDatum.List [("application", [], fake_pos)],
             token = token}
   in
      Fix.resolveList resolver dats
   end         
end
