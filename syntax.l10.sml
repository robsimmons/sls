signature SYNTAX =
sig
   type db (* Type of L10 databases *)
   val empty: db
   
   type head    (* = Head.t *)
   type mode    (* = Mode.t *)
   type aProp   (* = AProp.t *)
   type negProp (* = NegProp.t *)
   type posProp (* = PosProp.t *)
   type spine   (* = Spine.t *)
   type exp     (* = Exp.t *)
   type perm    (* = Perm.t *)
   type cid        = Symbol.symbol (* extensible *)
   type string     = String.string (* builtin *)
   type nat        = IntInf.int (* builtin *)
   
   structure Assert:
   sig
      val notSemanticEffects:    db -> db
      val weaklySemanticEffects: db -> db
      val semanticEffects:       db -> db
      val ruleSubord:            (head * head) * db -> db
      val classify:              (cid * exp) * db -> db
      val rules:                 (cid * negProp) * db -> db
      val signat:                (cid * exp * exp) * db -> db
      val headNeg:               (negProp * head) * db -> db
      val headPos:               (posProp * head) * db -> db
      val endNeg:                (negProp * negProp) * db -> db
      val subgoal:               (negProp * posProp) * db -> db
      val endPos:                (posProp * posProp) * db -> db
      val subNeg:                (negProp * aProp) * db -> db
      val subPos:                (posProp * aProp) * db -> db
      val fvNeg:                 (negProp * string) * db -> db
      val fvPos:                 (posProp * string) * db -> db
      val varMode:               (string * mode) * db -> db
      val givenMode:             (exp * mode) * db -> db
      val fvSpine:               (spine * string) * db -> db
      val fv:                    (exp * string) * db -> db
      val headClass:             (exp * exp) * db -> db
   end
   
   structure Query:
   sig
      val notSemanticEffects:    db -> bool
      val weaklySemanticEffects: db -> bool
      val semanticEffects:       db -> bool
      val ruleSubord:            db -> (head * head) -> bool
      val classify:              db -> (cid * exp) -> bool
      val rules:                 db -> (cid * negProp) -> bool
      val signat:                db -> (cid * exp * exp) -> bool
      val headNeg:               db -> (negProp * head) -> bool
      val headPos:               db -> (posProp * head) -> bool
      val endNeg:                db -> (negProp * negProp) -> bool
      val subgoal:               db -> (negProp * posProp) -> bool
      val endPos:                db -> (posProp * posProp) -> bool
      val subNeg:                db -> (negProp * aProp) -> bool
      val subPos:                db -> (posProp * aProp) -> bool
      val fvNeg:                 db -> (negProp * string) -> bool
      val fvPos:                 db -> (posProp * string) -> bool
      val varMode:               db -> (string * mode) -> bool
      val givenMode:             db -> (exp * mode) -> bool
      val fvSpine:               db -> (spine * string) -> bool
      val fv:                    db -> (exp * string) -> bool
      val headClass:             db -> (exp * exp) -> bool
      
      val lookupClass:           (exp * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val lookupRule:            (negProp * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val lookup:                ((exp * exp) * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val negHeads:              (negProp * 'a -> 'a) -> 'a -> db -> negProp -> 'a
      val freevarsNeg:           (string * 'a -> 'a) -> 'a -> db -> negProp -> 'a
      val freevarsPos:           (string * 'a -> 'a) -> 'a -> db -> posProp -> 'a
      val freevarsSpine:         (string * 'a -> 'a) -> 'a -> db -> spine -> 'a
      val freevars:              (string * 'a -> 'a) -> 'a -> db -> exp -> 'a
      
      val lookupClassList: db -> cid -> exp list (* = lookupClass (op ::) [] *)
      val lookupRuleList: db -> cid -> negProp list (* = lookupRule (op ::) [] *)
      val lookupList: db -> cid -> (exp * exp) list (* = lookup (op ::) [] *)
      val negHeadsList: db -> negProp -> negProp list (* = negHeads (op ::) [] *)
      val freevarsNegList: db -> negProp -> string list (* = freevarsNeg (op ::) [] *)
      val freevarsPosList: db -> posProp -> string list (* = freevarsPos (op ::) [] *)
      val freevarsSpineList: db -> spine -> string list (* = freevarsSpine (op ::) [] *)
      val freevarsList: db -> exp -> string list (* = freevars (op ::) [] *)
   end
end


(* L10 Datatypes (datatypes.sml) *)
(* Datatypes meet the following specification: *)
(*
structure Head:>
sig
   datatype t
    = Monadic
    | Atomic of Symbol.symbol
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure Mode:>
sig
   datatype t
    = Input
    | Output
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure AProp:>
sig
   datatype t
    = Pos of PosProp.t
    | Neg of NegProp.t
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure NegProp:>
sig
   datatype t
    = NAtom of Symbol.symbol * Spine.t
    | Lax of PosProp.t
    | Lefti of PosProp.t * t
    | Righti of PosProp.t * t
    | With of t * t
    | All of String.string * Exp.t * t
    | Alli of String.string * Exp.t * t
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure PosProp:>
sig
   datatype t
    = PAtom of Perm.t * Symbol.symbol * Spine.t
    | Down of Perm.t * NegProp.t
    | One
    | Fuse of t * t
    | Exists of String.string * Exp.t * t
    | Unif of Exp.t * Exp.t
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure Spine:>
sig
   datatype t
    = Nil
    | App of Exp.t * t
    | Appi of Exp.t * t
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure Exp:>
sig
   datatype t
    = Knd
    | Typ
    | NProp
    | PProp of Perm.t
    | Pi of String.string * t * t
    | Pii of String.string * t * t
    | Arrow of t * t
    | Var of String.string * IntInf.int * Spine.t
    | Con of Symbol.symbol * Spine.t
    | Lam of String.string * t
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

structure Perm:>
sig
   datatype t
    = Ord
    | Pers
    | Aff
    | Lin
   
   structure Dict:> DICT where type key = t
   val eq: t * t -> bool
   val toString: t -> string
end

*)
(* Empty set of datatypes *)
(* Datatypes for world
                 rel
                 perm
                 exp
                 spine
                 posProp
                 negProp
                 aProp
                 mode
                 head *)

(* Part 1/3: Specialized discrimination tree structure *)

structure DiscDict:>
sig
   type 'a dict
   exception NotThere

   val empty: 'a dict
   val isEmpty: 'a dict -> bool
   val inj: 'a -> 'a dict (* Insert data *)
   val prj: 'a dict -> 'a (* Expect data, may raise NotThere *)
   val sub: int -> 'a dict -> 'a dict 
   val subNat: IntInf.int -> 'a dict -> 'a dict
   val subString: String.string -> 'a dict -> 'a dict
   val subCid: Symbol.symbol -> 'a dict -> 'a dict

   (* Combines the ORD_MAP intersectWith with a fold *)
   val intersect: ('a * 'b * 'c -> 'c) -> 'c -> ('a dict * 'b dict) -> 'c

   type 'a zipdict 
   val id: 'a dict -> 'a zipdict
   val unzip: int * int -> 'a zipdict -> 'a zipdict
   val unzipNat: IntInf.int -> 'a zipdict -> 'a zipdict
   val unzipString: String.string -> 'a zipdict -> 'a zipdict
   val unzipCid: Symbol.symbol -> 'a zipdict -> 'a zipdict

   val rezip: 'a zipdict -> 'a dict
   val replace: 'a zipdict * 'a dict -> 'a zipdict
end =
struct
   exception Invariant

   datatype 'a dict' = 
      D of 'a 
    | D_ of 'a dict' option vector
    | DNat of 'a dict' IntInfSplayDict.dict
    | DString of 'a dict' StringSplayDict.dict
    | DCid of 'a dict' SymbolSplayDict.dict

   fun intersect f a (NONE, _) = a
     | intersect f a (_, NONE) = a
     | intersect f a (SOME m1, SOME m2) = 
       case (m1, m2) of 
             (D data1, D data2) => f (data1, data2, a)
        | (D_ vec1, D_ vec2) => 
             if Vector.length vec1 <> Vector.length vec2
             then raise Invariant
             else Vector.foldri 
                (fn (i, d1, a) => 
                    intersect f a (d1, Vector.sub (vec2, i)))
                a vec1
        | (DNat dict1, DNat dict2) => 
             IntInfSplayDict.foldr
                (fn (s, d1, a) => 
                    intersect f a (SOME d1, IntInfSplayDict.find dict2 s))
                a dict1
        | (DString dict1, DString dict2) => 
             StringSplayDict.foldr
                (fn (s, d1, a) => 
                    intersect f a (SOME d1, StringSplayDict.find dict2 s))
                a dict1
        | (DCid dict1, DCid dict2) => 
             SymbolSplayDict.foldr
                (fn (s, d1, a) => 
                    intersect f a (SOME d1, SymbolSplayDict.find dict2 s))
                a dict1
        | _ => raise Invariant

   type 'a dict = 'a dict' option

   datatype 'a zipper = 
      Z_ of int * 'a dict vector
    | ZNat of IntInf.int * 'a dict' IntInfSplayDict.dict
    | ZString of String.string * 'a dict' StringSplayDict.dict
    | ZCid of Symbol.symbol * 'a dict' SymbolSplayDict.dict

   type 'a zipdict = 'a zipper list * 'a dict

   fun id dict = ([], dict)

   fun replace ((zipper, _), dict) = (zipper, dict)

   val empty = NONE

   fun isEmpty NONE = true
     | isEmpty _ = false

   fun inj x = SOME (D x)

   exception NotThere

   fun prj NONE = raise NotThere
     | prj (SOME (D x)) = x
     | prj _ = raise Invariant

   fun sub n dict =
      case dict of 
         NONE => raise NotThere
       | SOME (D_ vector) => Vector.sub (vector, n) 
       | _ => raise Invariant

   fun subNat s dict = 
      case dict of
         NONE => raise NotThere
       | SOME (DNat dict) => IntInfSplayDict.find dict s
       | _ => raise Invariant

   fun subString s dict = 
      case dict of
         NONE => raise NotThere
       | SOME (DString dict) => StringSplayDict.find dict s
       | _ => raise Invariant

   fun subCid s dict = 
      case dict of
         NONE => raise NotThere
       | SOME (DCid dict) => SymbolSplayDict.find dict s
       | _ => raise Invariant

   fun unzip (n, typ) (zipper, dict) = 
      case dict of 
          NONE => 
             (Z_ (n, Vector.tabulate (typ, fn _ => NONE)) :: zipper, NONE)
        | SOME (D_ vector) => 
             (Z_ (n, vector) :: zipper, Vector.sub (vector, n))
        | SOME _ => raise Invariant

   fun unzipNat s (zipper, dict) = 
      case dict of 
         NONE => (ZNat (s, IntInfSplayDict.empty) :: zipper, NONE)
       | SOME (DNat dict) =>
            (ZNat (s, dict) :: zipper, IntInfSplayDict.find dict s)
       | _ => raise Invariant

   fun unzipString s (zipper, dict) = 
      case dict of 
         NONE => (ZString (s, StringSplayDict.empty) :: zipper, NONE)
       | SOME (DString dict) =>
            (ZString (s, dict) :: zipper, StringSplayDict.find dict s)
       | _ => raise Invariant

   fun unzipCid s (zipper, dict) = 
      case dict of 
         NONE => (ZCid (s, SymbolSplayDict.empty) :: zipper, NONE)
       | SOME (DCid dict) =>
            (ZCid (s, dict) :: zipper, SymbolSplayDict.find dict s)
       | _ => raise Invariant

   (* XXX these insertion functions need to be revised if the rezip
    * function has the possibility of *deleting* entries *)

   fun insertNat dict s NONE = dict
     | insertNat dict s (SOME discdict) =
          IntInfSplayDict.insert dict s discdict

   fun insertString dict s NONE = dict
     | insertString dict s (SOME discdict) =
          StringSplayDict.insert dict s discdict

   fun insertCid dict s NONE = dict
     | insertCid dict s (SOME discdict) =
          SymbolSplayDict.insert dict s discdict

   fun rezip ([], discdict) = discdict
     | rezip (Z_ (n, vector) :: zipper, discdict) = 
          rezip (zipper, SOME (D_ (Vector.update (vector, n, discdict))))
     | rezip (ZNat (s, dict) :: zipper, discdict) = 
          rezip 
             (zipper
              , SOME (DNat (insertNat dict s discdict)))
     | rezip (ZString (s, dict) :: zipper, discdict) = 
          rezip 
             (zipper
              , SOME (DString (insertString dict s discdict)))
     | rezip (ZCid (s, dict) :: zipper, discdict) = 
          rezip 
             (zipper
              , SOME (DCid (insertCid dict s discdict)))
end

functor DiscDictFun
   (P: sig
          type t
          val unzip: t -> 'a DiscDict.zipdict -> 'a DiscDict.zipdict
          val sub: t -> 'a DiscDict.dict -> 'a DiscDict.dict
       end):> DICT where type key = P.t =
struct
   open DiscDict

   type key = P.t

   exception Absent

   type 'a dict = 'a dict

   val empty = empty

   fun singleton key data =
      rezip (replace (P.unzip key (id empty), inj data))

   fun insert dict key data = 
      rezip (replace (P.unzip key (id dict), inj data))

   fun find dict key = SOME (prj (P.sub key dict))
      handle NotThere => NONE

   fun lookup dict key = prj (P.sub key dict)
      handle NotThere => raise Absent

   fun insertMerge dict key default modify =
      insert dict key
         (modify (prj (P.sub key dict))
             handle NotThere => default)

   fun member dict key = (ignore (prj (P.sub key dict)); true)
      handle NotThere => false

   exception NotImpl
   val union = fn _ => raise NotImpl
   val operate = fn _ => raise NotImpl
   val isEmpty = fn _ => raise NotImpl
   val size = fn _ => raise NotImpl
   val toList = fn _ => raise NotImpl
   val domain = fn _ => raise NotImpl
   val map = fn _ => raise NotImpl
   val foldl = fn _ => raise NotImpl
   val foldr = fn _ => raise NotImpl
   val app = fn _ => raise NotImpl
   val remove = fn _ => raise NotImpl
end

(* Part 2/3: Implementation (permits mutual recursion) *)

structure L10_Terms = 
struct
   datatype t_world = 
     World
   | WExp of t_exp
   | WSpine of t_spine
   | WMode
   | WPos of t_posProp
   | WNeg of t_negProp
   | WSignat
   | WRuleSubord
   
   and t_rel = 
     HeadClass of t_exp * t_exp
   | Fv of t_exp * String.string
   | FvSpine of t_spine * String.string
   | GivenMode of t_exp * t_mode
   | VarMode of String.string * t_mode
   | FvPos of t_posProp * String.string
   | FvNeg of t_negProp * String.string
   | SubPos of t_posProp * t_aProp
   | SubNeg of t_negProp * t_aProp
   | EndPos of t_posProp * t_posProp
   | Subgoal of t_negProp * t_posProp
   | EndNeg of t_negProp * t_negProp
   | HeadPos of t_posProp * t_head
   | HeadNeg of t_negProp * t_head
   | Signat of Symbol.symbol * t_exp * t_exp
   | Rules of Symbol.symbol * t_negProp
   | Classify of Symbol.symbol * t_exp
   | RuleSubord of t_head * t_head
   | SemanticEffects
   | WeaklySemanticEffects
   | NotSemanticEffects
   
   and t_perm = 
     Ord
   | Pers
   | Aff
   | Lin
   
   and t_exp = 
     Knd
   | Typ
   | NProp
   | PProp of t_perm
   | Pi of String.string * t_exp * t_exp
   | Pii of String.string * t_exp * t_exp
   | Arrow of t_exp * t_exp
   | Var of String.string * IntInf.int * t_spine
   | Con of Symbol.symbol * t_spine
   | Lam of String.string * t_exp
   
   and t_spine = 
     Nil
   | App of t_exp * t_spine
   | Appi of t_exp * t_spine
   
   and t_posProp = 
     PAtom of t_perm * Symbol.symbol * t_spine
   | Down of t_perm * t_negProp
   | One
   | Fuse of t_posProp * t_posProp
   | Exists of String.string * t_exp * t_posProp
   | Unif of t_exp * t_exp
   
   and t_negProp = 
     NAtom of Symbol.symbol * t_spine
   | Lax of t_posProp
   | Lefti of t_posProp * t_negProp
   | Righti of t_posProp * t_negProp
   | With of t_negProp * t_negProp
   | All of String.string * t_exp * t_negProp
   | Alli of String.string * t_exp * t_negProp
   
   and t_aProp = 
     Pos of t_posProp
   | Neg of t_negProp
   
   and t_mode = 
     Input
   | Output
   
   and t_head = 
     Monadic
   | Atomic of Symbol.symbol
   
   fun eq_world (x, y) =
     (case (x, y) of
         (World, World) => 
            true
       | (WExp x_0, WExp y_0) => 
            eq_exp (x_0, y_0)
       | (WSpine x_0, WSpine y_0) => 
            eq_spine (x_0, y_0)
       | (WMode, WMode) => 
            true
       | (WPos x_0, WPos y_0) => 
            eq_posProp (x_0, y_0)
       | (WNeg x_0, WNeg y_0) => 
            eq_negProp (x_0, y_0)
       | (WSignat, WSignat) => 
            true
       | (WRuleSubord, WRuleSubord) => 
            true
       | _ => false)
   and eq_rel (x, y) =
     (case (x, y) of
         (HeadClass (x_0, x_1), HeadClass (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_exp (x_1, y_1)
       | (Fv (x_0, x_1), Fv (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (FvSpine (x_0, x_1), FvSpine (y_0, y_1)) => 
            eq_spine (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (GivenMode (x_0, x_1), GivenMode (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_mode (x_1, y_1)
       | (VarMode (x_0, x_1), VarMode (y_0, y_1)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_mode (x_1, y_1)
       | (FvPos (x_0, x_1), FvPos (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (FvNeg (x_0, x_1), FvNeg (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (SubPos (x_0, x_1), SubPos (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_aProp (x_1, y_1)
       | (SubNeg (x_0, x_1), SubNeg (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso eq_aProp (x_1, y_1)
       | (EndPos (x_0, x_1), EndPos (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_posProp (x_1, y_1)
       | (Subgoal (x_0, x_1), Subgoal (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso eq_posProp (x_1, y_1)
       | (EndNeg (x_0, x_1), EndNeg (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso eq_negProp (x_1, y_1)
       | (HeadPos (x_0, x_1), HeadPos (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_head (x_1, y_1)
       | (HeadNeg (x_0, x_1), HeadNeg (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso eq_head (x_1, y_1)
       | (Signat (x_0, x_1, x_2), Signat (y_0, y_1, y_2)) => 
            (Symbol.eq (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_exp (x_2, y_2)
       | (Rules (x_0, x_1), Rules (y_0, y_1)) => 
            (Symbol.eq (x_0, y_0))
            andalso eq_negProp (x_1, y_1)
       | (Classify (x_0, x_1), Classify (y_0, y_1)) => 
            (Symbol.eq (x_0, y_0))
            andalso eq_exp (x_1, y_1)
       | (RuleSubord (x_0, x_1), RuleSubord (y_0, y_1)) => 
            eq_head (x_0, y_0)
            andalso eq_head (x_1, y_1)
       | (SemanticEffects, SemanticEffects) => 
            true
       | (WeaklySemanticEffects, WeaklySemanticEffects) => 
            true
       | (NotSemanticEffects, NotSemanticEffects) => 
            true
       | _ => false)
   and eq_perm (x, y) =
     (case (x, y) of
         (Ord, Ord) => 
            true
       | (Pers, Pers) => 
            true
       | (Aff, Aff) => 
            true
       | (Lin, Lin) => 
            true
       | _ => false)
   and eq_exp (x, y) =
     (case (x, y) of
         (Knd, Knd) => 
            true
       | (Typ, Typ) => 
            true
       | (NProp, NProp) => 
            true
       | (PProp x_0, PProp y_0) => 
            eq_perm (x_0, y_0)
       | (Pi (x_0, x_1, x_2), Pi (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_exp (x_2, y_2)
       | (Pii (x_0, x_1, x_2), Pii (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_exp (x_2, y_2)
       | (Arrow (x_0, x_1), Arrow (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_exp (x_1, y_1)
       | (Var (x_0, x_1, x_2), Var (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso (EQUAL = IntInf.compare (x_1, y_1))
            andalso eq_spine (x_2, y_2)
       | (Con (x_0, x_1), Con (y_0, y_1)) => 
            (Symbol.eq (x_0, y_0))
            andalso eq_spine (x_1, y_1)
       | (Lam (x_0, x_1), Lam (y_0, y_1)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
       | _ => false)
   and eq_spine (x, y) =
     (case (x, y) of
         (Nil, Nil) => 
            true
       | (App (x_0, x_1), App (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_spine (x_1, y_1)
       | (Appi (x_0, x_1), Appi (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_spine (x_1, y_1)
       | _ => false)
   and eq_posProp (x, y) =
     (case (x, y) of
         (PAtom (x_0, x_1, x_2), PAtom (y_0, y_1, y_2)) => 
            eq_perm (x_0, y_0)
            andalso (Symbol.eq (x_1, y_1))
            andalso eq_spine (x_2, y_2)
       | (Down (x_0, x_1), Down (y_0, y_1)) => 
            eq_perm (x_0, y_0)
            andalso eq_negProp (x_1, y_1)
       | (One, One) => 
            true
       | (Fuse (x_0, x_1), Fuse (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_posProp (x_1, y_1)
       | (Exists (x_0, x_1, x_2), Exists (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_posProp (x_2, y_2)
       | (Unif (x_0, x_1), Unif (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso eq_exp (x_1, y_1)
       | _ => false)
   and eq_negProp (x, y) =
     (case (x, y) of
         (NAtom (x_0, x_1), NAtom (y_0, y_1)) => 
            (Symbol.eq (x_0, y_0))
            andalso eq_spine (x_1, y_1)
       | (Lax x_0, Lax y_0) => 
            eq_posProp (x_0, y_0)
       | (Lefti (x_0, x_1), Lefti (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_negProp (x_1, y_1)
       | (Righti (x_0, x_1), Righti (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso eq_negProp (x_1, y_1)
       | (With (x_0, x_1), With (y_0, y_1)) => 
            eq_negProp (x_0, y_0)
            andalso eq_negProp (x_1, y_1)
       | (All (x_0, x_1, x_2), All (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_negProp (x_2, y_2)
       | (Alli (x_0, x_1, x_2), Alli (y_0, y_1, y_2)) => 
            (EQUAL = String.compare (x_0, y_0))
            andalso eq_exp (x_1, y_1)
            andalso eq_negProp (x_2, y_2)
       | _ => false)
   and eq_aProp (x, y) =
     (case (x, y) of
         (Pos x_0, Pos y_0) => 
            eq_posProp (x_0, y_0)
       | (Neg x_0, Neg y_0) => 
            eq_negProp (x_0, y_0)
       | _ => false)
   and eq_mode (x, y) =
     (case (x, y) of
         (Input, Input) => 
            true
       | (Output, Output) => 
            true
       | _ => false)
   and eq_head (x, y) =
     (case (x, y) of
         (Monadic, Monadic) => 
            true
       | (Atomic x_0, Atomic y_0) => 
            (Symbol.eq (x_0, y_0))
       | _ => false)
   
   fun str_world x =
     (case x of
         World => 
            "World"
       | WExp x_0 => 
            "(WExp "^str_exp x_0 ^ ")"
       | WSpine x_0 => 
            "(WSpine "^str_spine x_0 ^ ")"
       | WMode => 
            "WMode"
       | WPos x_0 => 
            "(WPos "^str_posProp x_0 ^ ")"
       | WNeg x_0 => 
            "(WNeg "^str_negProp x_0 ^ ")"
       | WSignat => 
            "WSignat"
       | WRuleSubord => 
            "WRuleSubord")
   and str_rel x =
     (case x of
         HeadClass (x_0, x_1) => 
            "(HeadClass "^str_exp x_0
            ^" "^str_exp x_1^")"
       | Fv (x_0, x_1) => 
            "(Fv "^str_exp x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | FvSpine (x_0, x_1) => 
            "(FvSpine "^str_spine x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | GivenMode (x_0, x_1) => 
            "(GivenMode "^str_exp x_0
            ^" "^str_mode x_1^")"
       | VarMode (x_0, x_1) => 
            "(VarMode "^("\"" ^ x_0 ^ "\"")
            ^" "^str_mode x_1^")"
       | FvPos (x_0, x_1) => 
            "(FvPos "^str_posProp x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | FvNeg (x_0, x_1) => 
            "(FvNeg "^str_negProp x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | SubPos (x_0, x_1) => 
            "(SubPos "^str_posProp x_0
            ^" "^str_aProp x_1^")"
       | SubNeg (x_0, x_1) => 
            "(SubNeg "^str_negProp x_0
            ^" "^str_aProp x_1^")"
       | EndPos (x_0, x_1) => 
            "(EndPos "^str_posProp x_0
            ^" "^str_posProp x_1^")"
       | Subgoal (x_0, x_1) => 
            "(Subgoal "^str_negProp x_0
            ^" "^str_posProp x_1^")"
       | EndNeg (x_0, x_1) => 
            "(EndNeg "^str_negProp x_0
            ^" "^str_negProp x_1^")"
       | HeadPos (x_0, x_1) => 
            "(HeadPos "^str_posProp x_0
            ^" "^str_head x_1^")"
       | HeadNeg (x_0, x_1) => 
            "(HeadNeg "^str_negProp x_0
            ^" "^str_head x_1^")"
       | Signat (x_0, x_1, x_2) => 
            "(Signat "^(Symbol.toValue x_0)
            ^" "^str_exp x_1
            ^" "^str_exp x_2^")"
       | Rules (x_0, x_1) => 
            "(Rules "^(Symbol.toValue x_0)
            ^" "^str_negProp x_1^")"
       | Classify (x_0, x_1) => 
            "(Classify "^(Symbol.toValue x_0)
            ^" "^str_exp x_1^")"
       | RuleSubord (x_0, x_1) => 
            "(RuleSubord "^str_head x_0
            ^" "^str_head x_1^")"
       | SemanticEffects => 
            "SemanticEffects"
       | WeaklySemanticEffects => 
            "WeaklySemanticEffects"
       | NotSemanticEffects => 
            "NotSemanticEffects")
   and str_perm x =
     (case x of
         Ord => 
            "Ord"
       | Pers => 
            "Pers"
       | Aff => 
            "Aff"
       | Lin => 
            "Lin")
   and str_exp x =
     (case x of
         Knd => 
            "Knd"
       | Typ => 
            "Typ"
       | NProp => 
            "NProp"
       | PProp x_0 => 
            "(PProp "^str_perm x_0 ^ ")"
       | Pi (x_0, x_1, x_2) => 
            "(Pi "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1
            ^" "^str_exp x_2^")"
       | Pii (x_0, x_1, x_2) => 
            "(Pii "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1
            ^" "^str_exp x_2^")"
       | Arrow (x_0, x_1) => 
            "(Arrow "^str_exp x_0
            ^" "^str_exp x_1^")"
       | Var (x_0, x_1, x_2) => 
            "(Var "^("\"" ^ x_0 ^ "\"")
            ^" "^(IntInf.toString x_1)
            ^" "^str_spine x_2^")"
       | Con (x_0, x_1) => 
            "(Con "^(Symbol.toValue x_0)
            ^" "^str_spine x_1^")"
       | Lam (x_0, x_1) => 
            "(Lam "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1^")")
   and str_spine x =
     (case x of
         Nil => 
            "Nil"
       | App (x_0, x_1) => 
            "(App "^str_exp x_0
            ^" "^str_spine x_1^")"
       | Appi (x_0, x_1) => 
            "(Appi "^str_exp x_0
            ^" "^str_spine x_1^")")
   and str_posProp x =
     (case x of
         PAtom (x_0, x_1, x_2) => 
            "(PAtom "^str_perm x_0
            ^" "^(Symbol.toValue x_1)
            ^" "^str_spine x_2^")"
       | Down (x_0, x_1) => 
            "(Down "^str_perm x_0
            ^" "^str_negProp x_1^")"
       | One => 
            "One"
       | Fuse (x_0, x_1) => 
            "(Fuse "^str_posProp x_0
            ^" "^str_posProp x_1^")"
       | Exists (x_0, x_1, x_2) => 
            "(Exists "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1
            ^" "^str_posProp x_2^")"
       | Unif (x_0, x_1) => 
            "(Unif "^str_exp x_0
            ^" "^str_exp x_1^")")
   and str_negProp x =
     (case x of
         NAtom (x_0, x_1) => 
            "(NAtom "^(Symbol.toValue x_0)
            ^" "^str_spine x_1^")"
       | Lax x_0 => 
            "(Lax "^str_posProp x_0 ^ ")"
       | Lefti (x_0, x_1) => 
            "(Lefti "^str_posProp x_0
            ^" "^str_negProp x_1^")"
       | Righti (x_0, x_1) => 
            "(Righti "^str_posProp x_0
            ^" "^str_negProp x_1^")"
       | With (x_0, x_1) => 
            "(With "^str_negProp x_0
            ^" "^str_negProp x_1^")"
       | All (x_0, x_1, x_2) => 
            "(All "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1
            ^" "^str_negProp x_2^")"
       | Alli (x_0, x_1, x_2) => 
            "(Alli "^("\"" ^ x_0 ^ "\"")
            ^" "^str_exp x_1
            ^" "^str_negProp x_2^")")
   and str_aProp x =
     (case x of
         Pos x_0 => 
            "(Pos "^str_posProp x_0 ^ ")"
       | Neg x_0 => 
            "(Neg "^str_negProp x_0 ^ ")")
   and str_mode x =
     (case x of
         Input => 
            "Input"
       | Output => 
            "Output")
   and str_head x =
     (case x of
         Monadic => 
            "Monadic"
       | Atomic x_0 => 
            "(Atomic "^(Symbol.toValue x_0) ^ ")")
   
   fun sub_world x =
     (case x of
         World => 
            DiscDict.sub 0
       | WExp x_0 => 
            sub_exp x_0 o
            DiscDict.sub 1
       | WSpine x_0 => 
            sub_spine x_0 o
            DiscDict.sub 2
       | WMode => 
            DiscDict.sub 3
       | WPos x_0 => 
            sub_posProp x_0 o
            DiscDict.sub 4
       | WNeg x_0 => 
            sub_negProp x_0 o
            DiscDict.sub 5
       | WSignat => 
            DiscDict.sub 6
       | WRuleSubord => 
            DiscDict.sub 7)
   and sub_rel x =
     (case x of
         HeadClass (x_0, x_1) => 
            sub_exp x_1 o
            sub_exp x_0 o
            DiscDict.sub 0
       | Fv (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_exp x_0 o
            DiscDict.sub 1
       | FvSpine (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_spine x_0 o
            DiscDict.sub 2
       | GivenMode (x_0, x_1) => 
            sub_mode x_1 o
            sub_exp x_0 o
            DiscDict.sub 3
       | VarMode (x_0, x_1) => 
            sub_mode x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 4
       | FvPos (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_posProp x_0 o
            DiscDict.sub 5
       | FvNeg (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_negProp x_0 o
            DiscDict.sub 6
       | SubPos (x_0, x_1) => 
            sub_aProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 7
       | SubNeg (x_0, x_1) => 
            sub_aProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 8
       | EndPos (x_0, x_1) => 
            sub_posProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 9
       | Subgoal (x_0, x_1) => 
            sub_posProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 10
       | EndNeg (x_0, x_1) => 
            sub_negProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 11
       | HeadPos (x_0, x_1) => 
            sub_head x_1 o
            sub_posProp x_0 o
            DiscDict.sub 12
       | HeadNeg (x_0, x_1) => 
            sub_head x_1 o
            sub_negProp x_0 o
            DiscDict.sub 13
       | Signat (x_0, x_1, x_2) => 
            sub_exp x_2 o
            sub_exp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 14
       | Rules (x_0, x_1) => 
            sub_negProp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 15
       | Classify (x_0, x_1) => 
            sub_exp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 16
       | RuleSubord (x_0, x_1) => 
            sub_head x_1 o
            sub_head x_0 o
            DiscDict.sub 17
       | SemanticEffects => 
            DiscDict.sub 18
       | WeaklySemanticEffects => 
            DiscDict.sub 19
       | NotSemanticEffects => 
            DiscDict.sub 20)
   and sub_perm x =
     (case x of
         Ord => 
            DiscDict.sub 0
       | Pers => 
            DiscDict.sub 1
       | Aff => 
            DiscDict.sub 2
       | Lin => 
            DiscDict.sub 3)
   and sub_exp x =
     (case x of
         Knd => 
            DiscDict.sub 0
       | Typ => 
            DiscDict.sub 1
       | NProp => 
            DiscDict.sub 2
       | PProp x_0 => 
            sub_perm x_0 o
            DiscDict.sub 3
       | Pi (x_0, x_1, x_2) => 
            sub_exp x_2 o
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 4
       | Pii (x_0, x_1, x_2) => 
            sub_exp x_2 o
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 5
       | Arrow (x_0, x_1) => 
            sub_exp x_1 o
            sub_exp x_0 o
            DiscDict.sub 6
       | Var (x_0, x_1, x_2) => 
            sub_spine x_2 o
            DiscDict.subNat x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 7
       | Con (x_0, x_1) => 
            sub_spine x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 8
       | Lam (x_0, x_1) => 
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 9)
   and sub_spine x =
     (case x of
         Nil => 
            DiscDict.sub 0
       | App (x_0, x_1) => 
            sub_spine x_1 o
            sub_exp x_0 o
            DiscDict.sub 1
       | Appi (x_0, x_1) => 
            sub_spine x_1 o
            sub_exp x_0 o
            DiscDict.sub 2)
   and sub_posProp x =
     (case x of
         PAtom (x_0, x_1, x_2) => 
            sub_spine x_2 o
            DiscDict.subCid x_1 o
            sub_perm x_0 o
            DiscDict.sub 0
       | Down (x_0, x_1) => 
            sub_negProp x_1 o
            sub_perm x_0 o
            DiscDict.sub 1
       | One => 
            DiscDict.sub 2
       | Fuse (x_0, x_1) => 
            sub_posProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 3
       | Exists (x_0, x_1, x_2) => 
            sub_posProp x_2 o
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 4
       | Unif (x_0, x_1) => 
            sub_exp x_1 o
            sub_exp x_0 o
            DiscDict.sub 5)
   and sub_negProp x =
     (case x of
         NAtom (x_0, x_1) => 
            sub_spine x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 0
       | Lax x_0 => 
            sub_posProp x_0 o
            DiscDict.sub 1
       | Lefti (x_0, x_1) => 
            sub_negProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 2
       | Righti (x_0, x_1) => 
            sub_negProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 3
       | With (x_0, x_1) => 
            sub_negProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 4
       | All (x_0, x_1, x_2) => 
            sub_negProp x_2 o
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 5
       | Alli (x_0, x_1, x_2) => 
            sub_negProp x_2 o
            sub_exp x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 6)
   and sub_aProp x =
     (case x of
         Pos x_0 => 
            sub_posProp x_0 o
            DiscDict.sub 0
       | Neg x_0 => 
            sub_negProp x_0 o
            DiscDict.sub 1)
   and sub_mode x =
     (case x of
         Input => 
            DiscDict.sub 0
       | Output => 
            DiscDict.sub 1)
   and sub_head x =
     (case x of
         Monadic => 
            DiscDict.sub 0
       | Atomic x_0 => 
            DiscDict.subCid x_0 o
            DiscDict.sub 1)
   
   fun unzip_world x =
     (case x of
         World => 
            DiscDict.unzip (0, 8)
       | WExp x_0 => 
            unzip_exp x_0 o
            DiscDict.unzip (1, 8)
       | WSpine x_0 => 
            unzip_spine x_0 o
            DiscDict.unzip (2, 8)
       | WMode => 
            DiscDict.unzip (3, 8)
       | WPos x_0 => 
            unzip_posProp x_0 o
            DiscDict.unzip (4, 8)
       | WNeg x_0 => 
            unzip_negProp x_0 o
            DiscDict.unzip (5, 8)
       | WSignat => 
            DiscDict.unzip (6, 8)
       | WRuleSubord => 
            DiscDict.unzip (7, 8))
   and unzip_rel x =
     (case x of
         HeadClass (x_0, x_1) => 
            unzip_exp x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (0, 21)
       | Fv (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (1, 21)
       | FvSpine (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_spine x_0 o
            DiscDict.unzip (2, 21)
       | GivenMode (x_0, x_1) => 
            unzip_mode x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (3, 21)
       | VarMode (x_0, x_1) => 
            unzip_mode x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (4, 21)
       | FvPos (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (5, 21)
       | FvNeg (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (6, 21)
       | SubPos (x_0, x_1) => 
            unzip_aProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (7, 21)
       | SubNeg (x_0, x_1) => 
            unzip_aProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (8, 21)
       | EndPos (x_0, x_1) => 
            unzip_posProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (9, 21)
       | Subgoal (x_0, x_1) => 
            unzip_posProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (10, 21)
       | EndNeg (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (11, 21)
       | HeadPos (x_0, x_1) => 
            unzip_head x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (12, 21)
       | HeadNeg (x_0, x_1) => 
            unzip_head x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (13, 21)
       | Signat (x_0, x_1, x_2) => 
            unzip_exp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (14, 21)
       | Rules (x_0, x_1) => 
            unzip_negProp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (15, 21)
       | Classify (x_0, x_1) => 
            unzip_exp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (16, 21)
       | RuleSubord (x_0, x_1) => 
            unzip_head x_1 o
            unzip_head x_0 o
            DiscDict.unzip (17, 21)
       | SemanticEffects => 
            DiscDict.unzip (18, 21)
       | WeaklySemanticEffects => 
            DiscDict.unzip (19, 21)
       | NotSemanticEffects => 
            DiscDict.unzip (20, 21))
   and unzip_perm x =
     (case x of
         Ord => 
            DiscDict.unzip (0, 4)
       | Pers => 
            DiscDict.unzip (1, 4)
       | Aff => 
            DiscDict.unzip (2, 4)
       | Lin => 
            DiscDict.unzip (3, 4))
   and unzip_exp x =
     (case x of
         Knd => 
            DiscDict.unzip (0, 10)
       | Typ => 
            DiscDict.unzip (1, 10)
       | NProp => 
            DiscDict.unzip (2, 10)
       | PProp x_0 => 
            unzip_perm x_0 o
            DiscDict.unzip (3, 10)
       | Pi (x_0, x_1, x_2) => 
            unzip_exp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (4, 10)
       | Pii (x_0, x_1, x_2) => 
            unzip_exp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (5, 10)
       | Arrow (x_0, x_1) => 
            unzip_exp x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (6, 10)
       | Var (x_0, x_1, x_2) => 
            unzip_spine x_2 o
            DiscDict.unzipNat x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (7, 10)
       | Con (x_0, x_1) => 
            unzip_spine x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (8, 10)
       | Lam (x_0, x_1) => 
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (9, 10))
   and unzip_spine x =
     (case x of
         Nil => 
            DiscDict.unzip (0, 3)
       | App (x_0, x_1) => 
            unzip_spine x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (1, 3)
       | Appi (x_0, x_1) => 
            unzip_spine x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (2, 3))
   and unzip_posProp x =
     (case x of
         PAtom (x_0, x_1, x_2) => 
            unzip_spine x_2 o
            DiscDict.unzipCid x_1 o
            unzip_perm x_0 o
            DiscDict.unzip (0, 6)
       | Down (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_perm x_0 o
            DiscDict.unzip (1, 6)
       | One => 
            DiscDict.unzip (2, 6)
       | Fuse (x_0, x_1) => 
            unzip_posProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (3, 6)
       | Exists (x_0, x_1, x_2) => 
            unzip_posProp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (4, 6)
       | Unif (x_0, x_1) => 
            unzip_exp x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (5, 6))
   and unzip_negProp x =
     (case x of
         NAtom (x_0, x_1) => 
            unzip_spine x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (0, 7)
       | Lax x_0 => 
            unzip_posProp x_0 o
            DiscDict.unzip (1, 7)
       | Lefti (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (2, 7)
       | Righti (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (3, 7)
       | With (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (4, 7)
       | All (x_0, x_1, x_2) => 
            unzip_negProp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (5, 7)
       | Alli (x_0, x_1, x_2) => 
            unzip_negProp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (6, 7))
   and unzip_aProp x =
     (case x of
         Pos x_0 => 
            unzip_posProp x_0 o
            DiscDict.unzip (0, 2)
       | Neg x_0 => 
            unzip_negProp x_0 o
            DiscDict.unzip (1, 2))
   and unzip_mode x =
     (case x of
         Input => 
            DiscDict.unzip (0, 2)
       | Output => 
            DiscDict.unzip (1, 2))
   and unzip_head x =
     (case x of
         Monadic => 
            DiscDict.unzip (0, 2)
       | Atomic x_0 => 
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (1, 2))
end


(* Part 3/3: Exposed interfaces *)

structure World = 
struct
   datatype t = datatype L10_Terms.t_world
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_world
     val sub = L10_Terms.sub_world
     val unzip = L10_Terms.unzip_world
   end)
   val toString: t -> string = L10_Terms.str_world
   val eq: t * t -> bool = L10_Terms.eq_world
end

structure Rel = 
struct
   datatype t = datatype L10_Terms.t_rel
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_rel
     val sub = L10_Terms.sub_rel
     val unzip = L10_Terms.unzip_rel
   end)
   val toString: t -> string = L10_Terms.str_rel
   val eq: t * t -> bool = L10_Terms.eq_rel
end

structure Perm = 
struct
   datatype t = datatype L10_Terms.t_perm
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_perm
     val sub = L10_Terms.sub_perm
     val unzip = L10_Terms.unzip_perm
   end)
   val toString: t -> string = L10_Terms.str_perm
   val eq: t * t -> bool = L10_Terms.eq_perm
end

structure Exp = 
struct
   datatype t = datatype L10_Terms.t_exp
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_exp
     val sub = L10_Terms.sub_exp
     val unzip = L10_Terms.unzip_exp
   end)
   val toString: t -> string = L10_Terms.str_exp
   val eq: t * t -> bool = L10_Terms.eq_exp
end

structure Spine = 
struct
   datatype t = datatype L10_Terms.t_spine
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_spine
     val sub = L10_Terms.sub_spine
     val unzip = L10_Terms.unzip_spine
   end)
   val toString: t -> string = L10_Terms.str_spine
   val eq: t * t -> bool = L10_Terms.eq_spine
end

structure PosProp = 
struct
   datatype t = datatype L10_Terms.t_posProp
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_posProp
     val sub = L10_Terms.sub_posProp
     val unzip = L10_Terms.unzip_posProp
   end)
   val toString: t -> string = L10_Terms.str_posProp
   val eq: t * t -> bool = L10_Terms.eq_posProp
end

structure NegProp = 
struct
   datatype t = datatype L10_Terms.t_negProp
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_negProp
     val sub = L10_Terms.sub_negProp
     val unzip = L10_Terms.unzip_negProp
   end)
   val toString: t -> string = L10_Terms.str_negProp
   val eq: t * t -> bool = L10_Terms.eq_negProp
end

structure AProp = 
struct
   datatype t = datatype L10_Terms.t_aProp
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_aProp
     val sub = L10_Terms.sub_aProp
     val unzip = L10_Terms.unzip_aProp
   end)
   val toString: t -> string = L10_Terms.str_aProp
   val eq: t * t -> bool = L10_Terms.eq_aProp
end

structure Mode = 
struct
   datatype t = datatype L10_Terms.t_mode
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_mode
     val sub = L10_Terms.sub_mode
     val unzip = L10_Terms.unzip_mode
   end)
   val toString: t -> string = L10_Terms.str_mode
   val eq: t * t -> bool = L10_Terms.eq_mode
end

structure Head = 
struct
   datatype t = datatype L10_Terms.t_head
   structure Dict:> DICT where type key = t = DiscDictFun
   (struct
     type t = L10_Terms.t_head
     val sub = L10_Terms.sub_head
     val unzip = L10_Terms.unzip_head
   end)
   val toString: t -> string = L10_Terms.str_head
   val eq: t * t -> bool = L10_Terms.eq_head
end

structure L10_Terms = struct end (* Protect *)
structure DiscDict = struct end (* Protect *)
structure DiscDictFun = struct end (* Protect *)


(* L10 Logic programming *)

structure Syntax:> SYNTAX
   where type head = Head.t
   and type mode = Mode.t
   and type aProp = AProp.t
   and type negProp = NegProp.t
   and type posProp = PosProp.t
   and type spine = Spine.t
   and type exp = Exp.t
   and type perm = Perm.t
=
struct
   (* L10 databases with required indexing (indices.sml) *)
   
   structure L10_Tables =
   struct
      type tables = {
         (* 1: headClass + + *)
         1: unit list Exp.Dict.dict Exp.Dict.dict,
         (* 2: fv + + *)
         2: unit list StringSplayDict.dict Exp.Dict.dict,
         (* 3: fvSpine + + *)
         3: unit list StringSplayDict.dict Spine.Dict.dict,
         (* 4: fv + - *)
         4: String.string list Exp.Dict.dict,
         (* 5: fvSpine + - *)
         5: String.string list Spine.Dict.dict,
         (* 6: givenMode + + *)
         6: unit list Mode.Dict.dict Exp.Dict.dict,
         (* 7: varMode + + *)
         7: unit list Mode.Dict.dict StringSplayDict.dict,
         (* 8: fvPos + + *)
         8: unit list StringSplayDict.dict PosProp.Dict.dict,
         (* 9: fvNeg + + *)
         9: unit list StringSplayDict.dict NegProp.Dict.dict,
         (* 10: fvPos + - *)
         10: String.string list PosProp.Dict.dict,
         (* 11: fvNeg + - *)
         11: String.string list NegProp.Dict.dict,
         (* 12: subPos + + *)
         12: unit list AProp.Dict.dict PosProp.Dict.dict,
         (* 13: subNeg + + *)
         13: unit list AProp.Dict.dict NegProp.Dict.dict,
         (* 14: endPos + + *)
         14: unit list PosProp.Dict.dict PosProp.Dict.dict,
         (* 15: subgoal + + *)
         15: unit list PosProp.Dict.dict NegProp.Dict.dict,
         (* 16: endNeg + + *)
         16: unit list NegProp.Dict.dict NegProp.Dict.dict,
         (* 17: endNeg + - *)
         17: NegProp.t list NegProp.Dict.dict,
         (* 18: headPos + + *)
         18: unit list Head.Dict.dict PosProp.Dict.dict,
         (* 19: headNeg + + *)
         19: unit list Head.Dict.dict NegProp.Dict.dict,
         (* 20: signat + + + *)
         20: unit list Exp.Dict.dict Exp.Dict.dict SymbolSplayDict.dict,
         (* 21: rules + + *)
         21: unit list NegProp.Dict.dict SymbolSplayDict.dict,
         (* 22: signat + - - *)
         22: (Exp.t * Exp.t) list SymbolSplayDict.dict,
         (* 23: rules + - *)
         23: NegProp.t list SymbolSplayDict.dict,
         (* 24: classify + + *)
         24: unit list Exp.Dict.dict SymbolSplayDict.dict,
         (* 25: classify + - *)
         25: Exp.t list SymbolSplayDict.dict,
         (* 26: ruleSubord + + *)
         26: unit list Head.Dict.dict Head.Dict.dict,
         (* 27: semanticEffects *)
         27: unit list ,
         (* 28: weaklySemanticEffects *)
         28: unit list ,
         (* 29: notSemanticEffects *)
         29: unit list ,
         (* 30: rules - - *)
         30: (Symbol.symbol * NegProp.t) list ,
         (* 31: subNeg + (neg (lefti - -)) *)
         31: (PosProp.t * NegProp.t) list NegProp.Dict.dict,
         (* 32: headPos + - *)
         32: Head.t list PosProp.Dict.dict,
         (* 33: headNeg + - *)
         33: Head.t list NegProp.Dict.dict,
         (* 34: subNeg + (neg (righti - -)) *)
         34: (PosProp.t * NegProp.t) list NegProp.Dict.dict,
         (* 35: ruleSubord - - *)
         35: (Head.t * Head.t) list ,
         (* 36: ruleSubord + - *)
         36: Head.t list Head.Dict.dict,
         (* 37: signat - - - *)
         37: (Symbol.symbol * Exp.t * Exp.t) list ,
         (* 38: headClass + - *)
         38: Exp.t list Exp.Dict.dict,
         (* 39: subPos + - *)
         39: AProp.t list PosProp.Dict.dict,
         (* 40: subNeg + - *)
         40: AProp.t list NegProp.Dict.dict,
         (* 41: endPos + - *)
         41: PosProp.t list PosProp.Dict.dict,
         (* 42: subgoal + - *)
         42: PosProp.t list NegProp.Dict.dict,
         (* 43: endNeg + (lax -) *)
         43: PosProp.t list NegProp.Dict.dict,
         (* 44: endNeg + (nAtom - -) *)
         44: (Symbol.symbol * Spine.t) list NegProp.Dict.dict,
         (* 45: endPos + (down - -) *)
         45: (Perm.t * NegProp.t) list PosProp.Dict.dict,
         (* 46: givenMode - - *)
         46: (Exp.t * Mode.t) list ,
         (* 47: ruleSubord monadic - *)
         47: Head.t list ,
         (* 48: ruleSubord monadic monadic *)
         48: unit list ,
         worlds: unit World.Dict.dict}
      
      fun empty (): tables = {
         1=Exp.Dict.empty,
         2=Exp.Dict.empty,
         3=Spine.Dict.empty,
         4=Exp.Dict.empty,
         5=Spine.Dict.empty,
         6=Exp.Dict.empty,
         7=StringSplayDict.empty,
         8=PosProp.Dict.empty,
         9=NegProp.Dict.empty,
         10=PosProp.Dict.empty,
         11=NegProp.Dict.empty,
         12=PosProp.Dict.empty,
         13=NegProp.Dict.empty,
         14=PosProp.Dict.empty,
         15=NegProp.Dict.empty,
         16=NegProp.Dict.empty,
         17=NegProp.Dict.empty,
         18=PosProp.Dict.empty,
         19=NegProp.Dict.empty,
         20=SymbolSplayDict.empty,
         21=SymbolSplayDict.empty,
         22=SymbolSplayDict.empty,
         23=SymbolSplayDict.empty,
         24=SymbolSplayDict.empty,
         25=SymbolSplayDict.empty,
         26=Head.Dict.empty,
         27=[],
         28=[],
         29=[],
         30=[],
         31=NegProp.Dict.empty,
         32=PosProp.Dict.empty,
         33=NegProp.Dict.empty,
         34=NegProp.Dict.empty,
         35=[],
         36=Head.Dict.empty,
         37=[],
         38=Exp.Dict.empty,
         39=PosProp.Dict.empty,
         40=NegProp.Dict.empty,
         41=PosProp.Dict.empty,
         42=NegProp.Dict.empty,
         43=NegProp.Dict.empty,
         44=NegProp.Dict.empty,
         45=PosProp.Dict.empty,
         46=[],
         47=[],
         48=[],
         worlds=World.Dict.empty}
         
      fun get_1 (db: tables) = #1 db
      fun get_2 (db: tables) = #2 db
      fun get_3 (db: tables) = #3 db
      fun get_4 (db: tables) = #4 db
      fun get_5 (db: tables) = #5 db
      fun get_6 (db: tables) = #6 db
      fun get_7 (db: tables) = #7 db
      fun get_8 (db: tables) = #8 db
      fun get_9 (db: tables) = #9 db
      fun get_10 (db: tables) = #10 db
      fun get_11 (db: tables) = #11 db
      fun get_12 (db: tables) = #12 db
      fun get_13 (db: tables) = #13 db
      fun get_14 (db: tables) = #14 db
      fun get_15 (db: tables) = #15 db
      fun get_16 (db: tables) = #16 db
      fun get_17 (db: tables) = #17 db
      fun get_18 (db: tables) = #18 db
      fun get_19 (db: tables) = #19 db
      fun get_20 (db: tables) = #20 db
      fun get_21 (db: tables) = #21 db
      fun get_22 (db: tables) = #22 db
      fun get_23 (db: tables) = #23 db
      fun get_24 (db: tables) = #24 db
      fun get_25 (db: tables) = #25 db
      fun get_26 (db: tables) = #26 db
      fun get_27 (db: tables) = #27 db
      fun get_28 (db: tables) = #28 db
      fun get_29 (db: tables) = #29 db
      fun get_30 (db: tables) = #30 db
      fun get_31 (db: tables) = #31 db
      fun get_32 (db: tables) = #32 db
      fun get_33 (db: tables) = #33 db
      fun get_34 (db: tables) = #34 db
      fun get_35 (db: tables) = #35 db
      fun get_36 (db: tables) = #36 db
      fun get_37 (db: tables) = #37 db
      fun get_38 (db: tables) = #38 db
      fun get_39 (db: tables) = #39 db
      fun get_40 (db: tables) = #40 db
      fun get_41 (db: tables) = #41 db
      fun get_42 (db: tables) = #42 db
      fun get_43 (db: tables) = #43 db
      fun get_44 (db: tables) = #44 db
      fun get_45 (db: tables) = #45 db
      fun get_46 (db: tables) = #46 db
      fun get_47 (db: tables) = #47 db
      fun get_48 (db: tables) = #48 db
      fun get_worlds (db: tables) = #worlds db
      
      fun set_1 (db: tables) x = {
            1 = x,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_2 (db: tables) x = {
            1 = #1 db,
            2 = x,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_3 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = x,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_4 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = x,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_5 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = x,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_6 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = x,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_7 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = x,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_8 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = x,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_9 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = x,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_10 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = x,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_11 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = x,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_12 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = x,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_13 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = x,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_14 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = x,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_15 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = x,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_16 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = x,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_17 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = x,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_18 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = x,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_19 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = x,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_20 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = x,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_21 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = x,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_22 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = x,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_23 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = x,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_24 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = x,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_25 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = x,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_26 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = x,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_27 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = x,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_28 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = x,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_29 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = x,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_30 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = x,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_31 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = x,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_32 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = x,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_33 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = x,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_34 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = x,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_35 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = x,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_36 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = x,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_37 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = x,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_38 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = x,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_39 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = x,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_40 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = x,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_41 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = x,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_42 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = x,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_43 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = x,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_44 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = x,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_45 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = x,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_46 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = x,
            47 = #47 db,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_47 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = x,
            48 = #48 db,
            worlds = #worlds db}
      
      fun set_48 (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = x,
            worlds = #worlds db}
      
      fun set_worlds (db: tables) x = {
            1 = #1 db,
            2 = #2 db,
            3 = #3 db,
            4 = #4 db,
            5 = #5 db,
            6 = #6 db,
            7 = #7 db,
            8 = #8 db,
            9 = #9 db,
            10 = #10 db,
            11 = #11 db,
            12 = #12 db,
            13 = #13 db,
            14 = #14 db,
            15 = #15 db,
            16 = #16 db,
            17 = #17 db,
            18 = #18 db,
            19 = #19 db,
            20 = #20 db,
            21 = #21 db,
            22 = #22 db,
            23 = #23 db,
            24 = #24 db,
            25 = #25 db,
            26 = #26 db,
            27 = #27 db,
            28 = #28 db,
            29 = #29 db,
            30 = #30 db,
            31 = #31 db,
            32 = #32 db,
            33 = #33 db,
            34 = #34 db,
            35 = #35 db,
            36 = #36 db,
            37 = #37 db,
            38 = #38 db,
            39 = #39 db,
            40 = #40 db,
            41 = #41 db,
            42 = #42 db,
            43 = #43 db,
            44 = #44 db,
            45 = #45 db,
            46 = #46 db,
            47 = #47 db,
            48 = #48 db,
            worlds = x}
      
      fun fold folder seed NONE = seed
        | fold folder seed (SOME x) = List.foldr folder seed x
      
      fun mapPartial lookup x NONE = NONE
        | mapPartial lookup x (SOME dict) = lookup dict x
      
      fun fold_1 f x (db as {1= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Exp.Dict.find x_1
             (Exp.Dict.find dict x_0))
      
      fun fold_2 f x (db as {2= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (Exp.Dict.find dict x_0))
      
      fun fold_3 f x (db as {3= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (Spine.Dict.find dict x_0))
      
      fun fold_4 f x (db as {4= dict, ...}: tables) x_0 =
         fold f x
            (Exp.Dict.find dict x_0)
      
      fun fold_5 f x (db as {5= dict, ...}: tables) x_0 =
         fold f x
            (Spine.Dict.find dict x_0)
      
      fun fold_6 f x (db as {6= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Mode.Dict.find x_1
             (Exp.Dict.find dict x_0))
      
      fun fold_7 f x (db as {7= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Mode.Dict.find x_1
             (StringSplayDict.find dict x_0))
      
      fun fold_8 f x (db as {8= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_9 f x (db as {9= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_10 f x (db as {10= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_11 f x (db as {11= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_12 f x (db as {12= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial AProp.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_13 f x (db as {13= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial AProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_14 f x (db as {14= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial PosProp.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_15 f x (db as {15= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial PosProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_16 f x (db as {16= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial NegProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_17 f x (db as {17= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_18 f x (db as {18= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_19 f x (db as {19= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_20 f x (db as {20= dict, ...}: tables) (x_0, x_1, x_2) =
         fold f x
            (mapPartial Exp.Dict.find x_2
             (mapPartial Exp.Dict.find x_1
              (SymbolSplayDict.find dict x_0)))
      
      fun fold_21 f x (db as {21= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial NegProp.Dict.find x_1
             (SymbolSplayDict.find dict x_0))
      
      fun fold_22 f x (db as {22= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_23 f x (db as {23= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_24 f x (db as {24= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Exp.Dict.find x_1
             (SymbolSplayDict.find dict x_0))
      
      fun fold_25 f x (db as {25= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_26 f x (db as {26= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (Head.Dict.find dict x_0))
      
      fun fold_27 f x (db as {27= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_28 f x (db as {28= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_29 f x (db as {29= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_30 f x (db as {30= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_31 f x (db as {31= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_32 f x (db as {32= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_33 f x (db as {33= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_34 f x (db as {34= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_35 f x (db as {35= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_36 f x (db as {36= dict, ...}: tables) x_0 =
         fold f x
            (Head.Dict.find dict x_0)
      
      fun fold_37 f x (db as {37= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_38 f x (db as {38= dict, ...}: tables) x_0 =
         fold f x
            (Exp.Dict.find dict x_0)
      
      fun fold_39 f x (db as {39= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_40 f x (db as {40= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_41 f x (db as {41= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_42 f x (db as {42= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_43 f x (db as {43= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_44 f x (db as {44= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_45 f x (db as {45= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_46 f x (db as {46= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_47 f x (db as {47= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_48 f x (db as {48= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun ins_1 (x_0, x_1) data (db: tables) =
      let
         val this =get_1 db
         val single_1 = [data]
         val single_0 = Exp.Dict.singleton x_1 single_1
      in
         set_1 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Exp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_2 (x_0, x_1) data (db: tables) =
      let
         val this =get_2 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_2 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_3 (x_0, x_1) data (db: tables) =
      let
         val this =get_3 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_3 db
            (Spine.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_4 x_0 data (db: tables) =
      let
         val this =get_4 db
         val single_0 = [data]
      in
         set_4 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_5 x_0 data (db: tables) =
      let
         val this =get_5 db
         val single_0 = [data]
      in
         set_5 db
            (Spine.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_6 (x_0, x_1) data (db: tables) =
      let
         val this =get_6 db
         val single_1 = [data]
         val single_0 = Mode.Dict.singleton x_1 single_1
      in
         set_6 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Mode.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_7 (x_0, x_1) data (db: tables) =
      let
         val this =get_7 db
         val single_1 = [data]
         val single_0 = Mode.Dict.singleton x_1 single_1
      in
         set_7 db
            (StringSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Mode.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_8 (x_0, x_1) data (db: tables) =
      let
         val this =get_8 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_8 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_9 (x_0, x_1) data (db: tables) =
      let
         val this =get_9 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_9 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_10 x_0 data (db: tables) =
      let
         val this =get_10 db
         val single_0 = [data]
      in
         set_10 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_11 x_0 data (db: tables) =
      let
         val this =get_11 db
         val single_0 = [data]
      in
         set_11 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_12 (x_0, x_1) data (db: tables) =
      let
         val this =get_12 db
         val single_1 = [data]
         val single_0 = AProp.Dict.singleton x_1 single_1
      in
         set_12 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (AProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_13 (x_0, x_1) data (db: tables) =
      let
         val this =get_13 db
         val single_1 = [data]
         val single_0 = AProp.Dict.singleton x_1 single_1
      in
         set_13 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (AProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_14 (x_0, x_1) data (db: tables) =
      let
         val this =get_14 db
         val single_1 = [data]
         val single_0 = PosProp.Dict.singleton x_1 single_1
      in
         set_14 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (PosProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_15 (x_0, x_1) data (db: tables) =
      let
         val this =get_15 db
         val single_1 = [data]
         val single_0 = PosProp.Dict.singleton x_1 single_1
      in
         set_15 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (PosProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_16 (x_0, x_1) data (db: tables) =
      let
         val this =get_16 db
         val single_1 = [data]
         val single_0 = NegProp.Dict.singleton x_1 single_1
      in
         set_16 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (NegProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_17 x_0 data (db: tables) =
      let
         val this =get_17 db
         val single_0 = [data]
      in
         set_17 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_18 (x_0, x_1) data (db: tables) =
      let
         val this =get_18 db
         val single_1 = [data]
         val single_0 = Head.Dict.singleton x_1 single_1
      in
         set_18 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_19 (x_0, x_1) data (db: tables) =
      let
         val this =get_19 db
         val single_1 = [data]
         val single_0 = Head.Dict.singleton x_1 single_1
      in
         set_19 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_20 (x_0, x_1, x_2) data (db: tables) =
      let
         val this =get_20 db
         val single_2 = [data]
         val single_1 = Exp.Dict.singleton x_2 single_2
         val single_0 = Exp.Dict.singleton x_1 single_1
      in
         set_20 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Exp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (Exp.Dict.insertMerge this x_2 single_2
                 (fn this =>
                  (data :: this)))))))
      end
      
      fun ins_21 (x_0, x_1) data (db: tables) =
      let
         val this =get_21 db
         val single_1 = [data]
         val single_0 = NegProp.Dict.singleton x_1 single_1
      in
         set_21 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (NegProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_22 x_0 data (db: tables) =
      let
         val this =get_22 db
         val single_0 = [data]
      in
         set_22 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_23 x_0 data (db: tables) =
      let
         val this =get_23 db
         val single_0 = [data]
      in
         set_23 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_24 (x_0, x_1) data (db: tables) =
      let
         val this =get_24 db
         val single_1 = [data]
         val single_0 = Exp.Dict.singleton x_1 single_1
      in
         set_24 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Exp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_25 x_0 data (db: tables) =
      let
         val this =get_25 db
         val single_0 = [data]
      in
         set_25 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_26 (x_0, x_1) data (db: tables) =
      let
         val this =get_26 db
         val single_1 = [data]
         val single_0 = Head.Dict.singleton x_1 single_1
      in
         set_26 db
            (Head.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_27 data (db: tables) =
      let
         val this =get_27 db
      in
         set_27 db
            (data :: this)
      end
      
      fun ins_28 data (db: tables) =
      let
         val this =get_28 db
      in
         set_28 db
            (data :: this)
      end
      
      fun ins_29 data (db: tables) =
      let
         val this =get_29 db
      in
         set_29 db
            (data :: this)
      end
      
      fun ins_30 data (db: tables) =
      let
         val this =get_30 db
      in
         set_30 db
            (data :: this)
      end
      
      fun ins_31 x_0 data (db: tables) =
      let
         val this =get_31 db
         val single_0 = [data]
      in
         set_31 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_32 x_0 data (db: tables) =
      let
         val this =get_32 db
         val single_0 = [data]
      in
         set_32 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_33 x_0 data (db: tables) =
      let
         val this =get_33 db
         val single_0 = [data]
      in
         set_33 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_34 x_0 data (db: tables) =
      let
         val this =get_34 db
         val single_0 = [data]
      in
         set_34 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_35 data (db: tables) =
      let
         val this =get_35 db
      in
         set_35 db
            (data :: this)
      end
      
      fun ins_36 x_0 data (db: tables) =
      let
         val this =get_36 db
         val single_0 = [data]
      in
         set_36 db
            (Head.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_37 data (db: tables) =
      let
         val this =get_37 db
      in
         set_37 db
            (data :: this)
      end
      
      fun ins_38 x_0 data (db: tables) =
      let
         val this =get_38 db
         val single_0 = [data]
      in
         set_38 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_39 x_0 data (db: tables) =
      let
         val this =get_39 db
         val single_0 = [data]
      in
         set_39 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_40 x_0 data (db: tables) =
      let
         val this =get_40 db
         val single_0 = [data]
      in
         set_40 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_41 x_0 data (db: tables) =
      let
         val this =get_41 db
         val single_0 = [data]
      in
         set_41 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_42 x_0 data (db: tables) =
      let
         val this =get_42 db
         val single_0 = [data]
      in
         set_42 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_43 x_0 data (db: tables) =
      let
         val this =get_43 db
         val single_0 = [data]
      in
         set_43 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_44 x_0 data (db: tables) =
      let
         val this =get_44 db
         val single_0 = [data]
      in
         set_44 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_45 x_0 data (db: tables) =
      let
         val this =get_45 db
         val single_0 = [data]
      in
         set_45 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_46 data (db: tables) =
      let
         val this =get_46 db
      in
         set_46 db
            (data :: this)
      end
      
      fun ins_47 data (db: tables) =
      let
         val this =get_47 db
      in
         set_47 db
            (data :: this)
      end
      
      fun ins_48 data (db: tables) =
      let
         val this =get_48 db
      in
         set_48 db
            (data :: this)
      end
      
      fun insert_headClass (x_0, x_1) db =
         (* headClass x_0 x_1 *)
         (ins_1 (x_0, x_1) ()
          (ins_38 x_0 x_1 db))
      fun assert_headClass (x_0, x_1) (flag, db) =
         if fold_1 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_headClass (x_0, x_1) db)
      
      fun insert_fv (x_0, x_1) db =
         (* fv x_0 x_1 *)
         (ins_2 (x_0, x_1) ()
          (ins_4 x_0 x_1 db))
      fun assert_fv (x_0, x_1) (flag, db) =
         if fold_2 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fv (x_0, x_1) db)
      
      fun insert_fvSpine (x_0, x_1) db =
         (* fvSpine x_0 x_1 *)
         (ins_3 (x_0, x_1) ()
          (ins_5 x_0 x_1 db))
      fun assert_fvSpine (x_0, x_1) (flag, db) =
         if fold_3 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fvSpine (x_0, x_1) db)
      
      fun insert_givenMode (x_0, x_1) db =
         (* givenMode x_0 x_1 *)
         (ins_6 (x_0, x_1) ()
          (ins_46 (x_0, x_1) db))
      fun assert_givenMode (x_0, x_1) (flag, db) =
         if fold_6 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_givenMode (x_0, x_1) db)
      
      fun insert_varMode (x_0, x_1) db =
         (* varMode x_0 x_1 *)
         (ins_7 (x_0, x_1) () db)
      fun assert_varMode (x_0, x_1) (flag, db) =
         if fold_7 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_varMode (x_0, x_1) db)
      
      fun insert_fvPos (x_0, x_1) db =
         (* fvPos x_0 x_1 *)
         (ins_8 (x_0, x_1) ()
          (ins_10 x_0 x_1 db))
      fun assert_fvPos (x_0, x_1) (flag, db) =
         if fold_8 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fvPos (x_0, x_1) db)
      
      fun insert_fvNeg (x_0, x_1) db =
         (* fvNeg x_0 x_1 *)
         (ins_9 (x_0, x_1) ()
          (ins_11 x_0 x_1 db))
      fun assert_fvNeg (x_0, x_1) (flag, db) =
         if fold_9 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fvNeg (x_0, x_1) db)
      
      fun insert_subPos (x_0, x_1) db =
         (* subPos x_0 x_1 *)
         (ins_12 (x_0, x_1) ()
          (ins_39 x_0 x_1 db))
      fun assert_subPos (x_0, x_1) (flag, db) =
         if fold_12 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subPos (x_0, x_1) db)
      
      fun insert_subNeg (x_0, x_1) db =
        (case x_1 of 
            AProp.Neg x_1_0 =>
              (case x_1_0 of 
                  NegProp.Lefti (x_1_0_0, x_1_0_1) =>
                     (* subNeg x_0 (neg (lefti x_1_0_0 x_1_0_1)) *)
                     (ins_13 (x_0, x_1) ()
                      (ins_31 x_0 (x_1_0_0, x_1_0_1)
                       (ins_40 x_0 x_1 db)))
                | NegProp.Righti (x_1_0_0, x_1_0_1) =>
                     (* subNeg x_0 (neg (righti x_1_0_0 x_1_0_1)) *)
                     (ins_13 (x_0, x_1) ()
                      (ins_34 x_0 (x_1_0_0, x_1_0_1)
                       (ins_40 x_0 x_1 db)))
                | _ =>
                     (* subNeg x_0 (neg x_1_0) *)
                     (ins_13 (x_0, x_1) ()
                      (ins_40 x_0 x_1 db)))
          | _ =>
               (* subNeg x_0 x_1 *)
               (ins_13 (x_0, x_1) ()
                (ins_40 x_0 x_1 db)))
      fun assert_subNeg (x_0, x_1) (flag, db) =
         if fold_13 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subNeg (x_0, x_1) db)
      
      fun insert_endPos (x_0, x_1) db =
        (case x_1 of 
            PosProp.Down (x_1_0, x_1_1) =>
               (* endPos x_0 (down x_1_0 x_1_1) *)
               (ins_14 (x_0, x_1) ()
                (ins_41 x_0 x_1
                 (ins_45 x_0 (x_1_0, x_1_1) db)))
          | _ =>
               (* endPos x_0 x_1 *)
               (ins_14 (x_0, x_1) ()
                (ins_41 x_0 x_1 db)))
      fun assert_endPos (x_0, x_1) (flag, db) =
         if fold_14 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_endPos (x_0, x_1) db)
      
      fun insert_subgoal (x_0, x_1) db =
         (* subgoal x_0 x_1 *)
         (ins_15 (x_0, x_1) ()
          (ins_42 x_0 x_1 db))
      fun assert_subgoal (x_0, x_1) (flag, db) =
         if fold_15 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subgoal (x_0, x_1) db)
      
      fun insert_endNeg (x_0, x_1) db =
        (case x_1 of 
            NegProp.NAtom (x_1_0, x_1_1) =>
               (* endNeg x_0 (nAtom x_1_0 x_1_1) *)
               (ins_16 (x_0, x_1) ()
                (ins_17 x_0 x_1
                 (ins_44 x_0 (x_1_0, x_1_1) db)))
          | NegProp.Lax x_1_0 =>
               (* endNeg x_0 (lax x_1_0) *)
               (ins_16 (x_0, x_1) ()
                (ins_17 x_0 x_1
                 (ins_43 x_0 x_1_0 db)))
          | _ =>
               (* endNeg x_0 x_1 *)
               (ins_16 (x_0, x_1) ()
                (ins_17 x_0 x_1 db)))
      fun assert_endNeg (x_0, x_1) (flag, db) =
         if fold_16 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_endNeg (x_0, x_1) db)
      
      fun insert_headPos (x_0, x_1) db =
         (* headPos x_0 x_1 *)
         (ins_18 (x_0, x_1) ()
          (ins_32 x_0 x_1 db))
      fun assert_headPos (x_0, x_1) (flag, db) =
         if fold_18 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_headPos (x_0, x_1) db)
      
      fun insert_headNeg (x_0, x_1) db =
         (* headNeg x_0 x_1 *)
         (ins_19 (x_0, x_1) ()
          (ins_33 x_0 x_1 db))
      fun assert_headNeg (x_0, x_1) (flag, db) =
         if fold_19 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_headNeg (x_0, x_1) db)
      
      fun insert_signat (x_0, x_1, x_2) db =
         (* signat x_0 x_1 x_2 *)
         (ins_20 (x_0, x_1, x_2) ()
          (ins_22 x_0 (x_1, x_2)
           (ins_37 (x_0, x_1, x_2) db)))
      fun assert_signat (x_0, x_1, x_2) (flag, db) =
         if fold_20 (fn _ => true) false db (x_0, x_1, x_2)
         then (flag, db)
         else (true, insert_signat (x_0, x_1, x_2) db)
      
      fun insert_rules (x_0, x_1) db =
         (* rules x_0 x_1 *)
         (ins_21 (x_0, x_1) ()
          (ins_23 x_0 x_1
           (ins_30 (x_0, x_1) db)))
      fun assert_rules (x_0, x_1) (flag, db) =
         if fold_21 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_rules (x_0, x_1) db)
      
      fun insert_classify (x_0, x_1) db =
         (* classify x_0 x_1 *)
         (ins_24 (x_0, x_1) ()
          (ins_25 x_0 x_1 db))
      fun assert_classify (x_0, x_1) (flag, db) =
         if fold_24 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_classify (x_0, x_1) db)
      
      fun insert_ruleSubord (x_0, x_1) db =
        (case x_0 of 
            Head.Monadic =>
              (case x_1 of 
                  Head.Monadic =>
                     (* ruleSubord monadic monadic *)
                     (ins_26 (x_0, x_1) ()
                      (ins_35 (x_0, x_1)
                       (ins_36 x_0 x_1
                        (ins_47 x_1
                         (ins_48 () db)))))
                | _ =>
                     (* ruleSubord monadic x_1 *)
                     (ins_26 (x_0, x_1) ()
                      (ins_35 (x_0, x_1)
                       (ins_36 x_0 x_1
                        (ins_47 x_1 db)))))
          | _ =>
              (case x_1 of 
                  Head.Monadic =>
                     (* ruleSubord x_0 monadic *)
                     (ins_26 (x_0, x_1) ()
                      (ins_35 (x_0, x_1)
                       (ins_36 x_0 x_1 db)))
                | _ =>
                     (* ruleSubord x_0 x_1 *)
                     (ins_26 (x_0, x_1) ()
                      (ins_35 (x_0, x_1)
                       (ins_36 x_0 x_1 db)))))
      fun assert_ruleSubord (x_0, x_1) (flag, db) =
         if fold_26 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_ruleSubord (x_0, x_1) db)
      
      fun insert_semanticEffects () db =
         (* semanticEffects *)
         (ins_27 () db)
      fun assert_semanticEffects () (flag, db) =
         if fold_27 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_semanticEffects () db)
      
      fun insert_weaklySemanticEffects () db =
         (* weaklySemanticEffects *)
         (ins_28 () db)
      fun assert_weaklySemanticEffects () (flag, db) =
         if fold_28 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_weaklySemanticEffects () db)
      
      fun insert_notSemanticEffects () db =
         (* notSemanticEffects *)
         (ins_29 () db)
      fun assert_notSemanticEffects () (flag, db) =
         if fold_29 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_notSemanticEffects () db)
      
   end
   
   
   (* L10 immediate consequences (rules.sml) *)
   
   structure L10_Consequence =
   struct
   
      (* Rule at syntax.l10:244.1-244.50 *)
      
      (* assert -- notSemanticEffects *)
      fun exec_89_1 () satu db =
         (L10_Tables.assert_notSemanticEffects () db)
      (* ruleSubord monadic monadic - syntax.l10:244.1-244.27 *)
      fun exec_89 () satu db =
         L10_Tables.fold_48
            (fn ((), db) => 
               exec_89_1 () satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:241.1-241.81 *)
      
      (* assert -- weaklySemanticEffects *)
      fun exec_88_2 () satu db =
         (L10_Tables.assert_weaklySemanticEffects () db)
      (* not (ruleSubord monadic monadic) - syntax.l10:241.23-241.55 *)
      fun exec_88_1 () satu db =
         if L10_Tables.fold_48
               (fn _ => true) false (#2 db) ()
         then db else exec_88_2 () satu db
      (* ruleSubord monadic _ - syntax.l10:241.1-241.21 *)
      fun exec_88 () satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_88_1 () satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:238.1-238.47 *)
      
      (* assert -- semanticEffects *)
      fun exec_87_1 () satu db =
         (L10_Tables.assert_semanticEffects () db)
      (* not (ruleSubord monadic _) - syntax.l10:238.1-238.27 *)
      fun exec_87 () satu db =
         if L10_Tables.fold_47
               (fn _ => true) false (#2 db) ()
         then db else exec_87_1 () satu db
      
      (* Rule at syntax.l10:81.1-81.34 *)
      
      (* assert -- fv (lam X E) Y *)
      fun exec_17_2 (E, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Lam (X, E)), Y) db)
      (* X != Y - syntax.l10:81.27-81.33 *)
      fun exec_17_1 (E, Y, X) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_17_2 (E, Y, X) satu db else db
      (* fv E Y - syntax.l10:81.19-81.25 *)
      fun exec_17 (E, X) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_17_1 (E, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:80.1-80.33 *)
      
      (* assert -- fv (con _ Sp) Y *)
      fun exec_16_1 (USCORE_1, Sp, Y) satu db =
         (L10_Tables.assert_fv ((Exp.Con (USCORE_1, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:80.20-80.32 *)
      fun exec_16 (USCORE_1, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_16_1 (USCORE_1, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:79.1-79.35 *)
      
      (* assert -- fv (var X _ Sp) Y *)
      fun exec_15_1 (USCORE_1, Sp, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Var (X, USCORE_1, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:79.22-79.34 *)
      fun exec_15 (USCORE_1, Sp, X) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_15_1 (USCORE_1, Sp, x_1 (* Y *), X) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:78.1-78.19 *)
      
      (* assert -- fv (var X _ Sp) X *)
      fun exec_14 (USCORE_1, Sp, X) satu db =
         (L10_Tables.assert_fv ((Exp.Var (X, USCORE_1, Sp)), X) db)
      
      (* Rule at syntax.l10:77.1-77.31 *)
      
      (* assert -- fv (arrow E1 E2) Y *)
      fun exec_13_1 (Y, E1, E2) satu db =
         (L10_Tables.assert_fv ((Exp.Arrow (E1, E2)), Y) db)
      (* fv E2 Y - syntax.l10:77.23-77.30 *)
      fun exec_13 (E1, E2) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_13_1 (x_1 (* Y *), E1, E2) satu db)
            db (#2 db) E2
      
      (* Rule at syntax.l10:76.1-76.31 *)
      
      (* assert -- fv (arrow E1 E2) Y *)
      fun exec_12_1 (Y, E1, E2) satu db =
         (L10_Tables.assert_fv ((Exp.Arrow (E1, E2)), Y) db)
      (* fv E1 Y - syntax.l10:76.23-76.30 *)
      fun exec_12 (E1, E2) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_12_1 (x_1 (* Y *), E1, E2) satu db)
            db (#2 db) E1
      
      (* Rule at syntax.l10:75.1-75.36 *)
      
      (* assert -- fv (pii X T E) Y *)
      fun exec_11_2 (E, T, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Pii (X, T, E)), Y) db)
      (* X != Y - syntax.l10:75.29-75.35 *)
      fun exec_11_1 (E, T, Y, X) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_11_2 (E, T, Y, X) satu db else db
      (* fv E Y - syntax.l10:75.21-75.27 *)
      fun exec_11 (E, T, X) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_11_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:74.1-74.28 *)
      
      (* assert -- fv (pii X T E) Y *)
      fun exec_10_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Pii (X, T, E)), Y) db)
      (* fv T Y - syntax.l10:74.21-74.27 *)
      fun exec_10 (E, T, X) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_10_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:73.1-73.35 *)
      
      (* assert -- fv (pi X T E) Y *)
      fun exec_9_2 (E, T, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Pi (X, T, E)), Y) db)
      (* X != Y - syntax.l10:73.28-73.34 *)
      fun exec_9_1 (E, T, Y, X) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_9_2 (E, T, Y, X) satu db else db
      (* fv E Y - syntax.l10:73.20-73.26 *)
      fun exec_9 (E, T, X) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_9_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:72.1-72.27 *)
      
      (* assert -- fv (pi X T E) Y *)
      fun exec_8_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_fv ((Exp.Pi (X, T, E)), Y) db)
      (* fv T Y - syntax.l10:72.20-72.26 *)
      fun exec_8 (E, T, X) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_8_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:67.1-67.44 *)
      
      (* assert -- headClass (arrow _ E) Eh *)
      fun exec_7_1 (E, Eh, USCORE_1) satu db =
         (L10_Tables.assert_headClass ((Exp.Arrow (USCORE_1, E)), Eh) db)
      (* headClass E Eh - syntax.l10:67.29-67.43 *)
      fun exec_7 (E, USCORE_1) satu db =
         L10_Tables.fold_38
            (fn (x_1, db) => 
               exec_7_1 (E, x_1 (* Eh *), USCORE_1) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:66.1-66.44 *)
      
      (* assert -- headClass (pi _ _ E) Eh *)
      fun exec_6_1 (E, Eh, USCORE_1, USCORE_2) satu db =
         (L10_Tables.assert_headClass ((Exp.Pi (USCORE_1, USCORE_2, E)), Eh) db)
      (* headClass E Eh - syntax.l10:66.29-66.43 *)
      fun exec_6 (E, USCORE_1, USCORE_2) satu db =
         L10_Tables.fold_38
            (fn (x_1, db) => 
               exec_6_1 (E, x_1 (* Eh *), USCORE_1, USCORE_2) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:65.1-65.44 *)
      
      (* assert -- headClass (pii _ _ E) Eh *)
      fun exec_5_1 (E, Eh, USCORE_1, USCORE_2) satu db =
         (L10_Tables.assert_headClass ((Exp.Pii (USCORE_1, USCORE_2, E)), Eh) db)
      (* headClass E Eh - syntax.l10:65.29-65.43 *)
      fun exec_5 (E, USCORE_1, USCORE_2) satu db =
         L10_Tables.fold_38
            (fn (x_1, db) => 
               exec_5_1 (E, x_1 (* Eh *), USCORE_1, USCORE_2) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:64.1-64.37 *)
      
      (* assert -- headClass (pProp Perm) (pProp Perm) *)
      fun exec_4 Perm satu db =
         (L10_Tables.assert_headClass ((Exp.PProp Perm), (Exp.PProp Perm)) db)
      
      (* Rule at syntax.l10:63.1-63.23 *)
      
      (* assert -- headClass nProp nProp *)
      fun exec_3 () satu db =
         (L10_Tables.assert_headClass (Exp.NProp, Exp.NProp) db)
      
      (* Rule at syntax.l10:62.1-62.19 *)
      
      (* assert -- headClass typ typ *)
      fun exec_2 () satu db =
         (L10_Tables.assert_headClass (Exp.Typ, Exp.Typ) db)
      
      (* Rule at syntax.l10:61.1-61.19 *)
      
      (* assert -- headClass knd knd *)
      fun exec_1 () satu db =
         (L10_Tables.assert_headClass (Exp.Knd, Exp.Knd) db)
      
      (* Rule at syntax.l10:87.1-87.39 *)
      
      (* assert -- fvSpine (appi E Sp) Y *)
      fun exec_21_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_fvSpine ((Spine.Appi (E, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:87.26-87.38 *)
      fun exec_21 (E, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_21_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:86.1-86.33 *)
      
      (* assert -- fvSpine (appi E Sp) Y *)
      fun exec_20_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_fvSpine ((Spine.Appi (E, Sp)), Y) db)
      (* fv E Y - syntax.l10:86.26-86.32 *)
      fun exec_20 (E, Sp) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_20_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:85.1-85.38 *)
      
      (* assert -- fvSpine (app E Sp) Y *)
      fun exec_19_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_fvSpine ((Spine.App (E, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:85.25-85.37 *)
      fun exec_19 (E, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_19_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:84.1-84.32 *)
      
      (* assert -- fvSpine (app E Sp) Y *)
      fun exec_18_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_fvSpine ((Spine.App (E, Sp)), Y) db)
      (* fv E Y - syntax.l10:84.25-84.31 *)
      fun exec_18 (E, Sp) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_18_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:100.1-100.38 *)
      
      (* assert -- varMode X M *)
      fun exec_22_3 (X, M) satu db =
         (L10_Tables.assert_varMode (X, M) db)
      (* fv E X - syntax.l10:100.16-100.22 *)
      fun exec_22_2 (E, M) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_22_3 (x_1 (* X *), M) satu db)
            db (#2 db) E
      (* Dynamic world search: wExp E *)
      fun exec_22_1 (E, M) satu (flag, db) =
         exec_22_2 (E, M) satu (flag, satu (World.WExp E) db)
      (* givenMode E M - syntax.l10:100.1-100.14 *)
      fun exec_22 () satu db =
         L10_Tables.fold_46
            (fn ((x_0, x_1), db) => 
               exec_22_1 (x_0 (* E *), x_1 (* M *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:193.1-193.51 *)
      
      (* assert -- headPos A H *)
      fun exec_82_3 (A, H) satu db =
         (L10_Tables.assert_headPos (A, H) db)
      (* headNeg A' H - syntax.l10:193.38-193.50 *)
      fun exec_82_2 (A, A') satu db =
         L10_Tables.fold_33
            (fn (x_1, db) => 
               exec_82_3 (A, x_1 (* H *)) satu db)
            db (#2 db) A'
      (* Dynamic world search: wNeg A' *)
      fun exec_82_1 (A, A') satu (flag, db) =
         exec_82_2 (A, A') satu (flag, satu (World.WNeg A') db)
      (* endPos A (down _ A') - syntax.l10:193.16-193.36 *)
      fun exec_82 A satu db =
         L10_Tables.fold_45
            (fn ((x_1_0, x_1_1), db) => 
               exec_82_1 (A, x_1_1 (* A' *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:161.1-161.30 *)
      
      (* assert -- endPos (unif T S) (unif T S) *)
      fun exec_63 (T, S) satu db =
         (L10_Tables.assert_endPos ((PosProp.Unif (T, S)), (PosProp.Unif (T, S))) db)
      
      (* Rule at syntax.l10:160.1-160.39 *)
      
      (* assert -- endPos (exists _ _ A) H *)
      fun exec_62_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Exists (USCORE_1, USCORE_2, A)), H) db)
      (* endPos A H - syntax.l10:160.28-160.38 *)
      fun exec_62 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_62_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:159.1-159.35 *)
      
      (* assert -- endPos (fuse _ A) H *)
      fun exec_61_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Fuse (USCORE_1, A)), H) db)
      (* endPos A H - syntax.l10:159.24-159.34 *)
      fun exec_61 (USCORE_1, A) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_61_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:158.1-158.35 *)
      
      (* assert -- endPos (fuse A _) H *)
      fun exec_60_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Fuse (A, USCORE_1)), H) db)
      (* endPos A H - syntax.l10:158.24-158.34 *)
      fun exec_60 (USCORE_1, A) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_60_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:157.1-157.30 *)
      
      (* assert -- endPos (down P A) (down P A) *)
      fun exec_59 (A, P) satu db =
         (L10_Tables.assert_endPos ((PosProp.Down (P, A)), (PosProp.Down (P, A))) db)
      
      (* Rule at syntax.l10:156.1-156.38 *)
      
      (* assert -- endPos (pAtom P A Sp) (pAtom P A Sp) *)
      fun exec_58 (Sp, A, P) satu db =
         (L10_Tables.assert_endPos ((PosProp.PAtom (P, A, Sp)), (PosProp.PAtom (P, A, Sp))) db)
      
      (* Rule at syntax.l10:142.1-142.39 *)
      
      (* assert -- subPos (exists _ _ A) C *)
      fun exec_47_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Exists (USCORE_1, USCORE_2, A)), C) db)
      (* subPos A C - syntax.l10:142.28-142.38 *)
      fun exec_47 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_47_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:141.1-141.35 *)
      
      (* assert -- subPos (fuse _ A) C *)
      fun exec_46_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Fuse (USCORE_1, A)), C) db)
      (* subPos A C - syntax.l10:141.24-141.34 *)
      fun exec_46 (USCORE_1, A) satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_46_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:140.1-140.35 *)
      
      (* assert -- subPos (fuse A _) C *)
      fun exec_45_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Fuse (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:140.24-140.34 *)
      fun exec_45 (USCORE_1, A) satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_45_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:139.1-139.35 *)
      
      (* assert -- subPos (down _ A) C *)
      fun exec_44_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Down (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:139.24-139.34 *)
      fun exec_44 (USCORE_1, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_44_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:138.1-138.18 *)
      
      (* assert -- subPos A (pos A) *)
      fun exec_43 A satu db =
         (L10_Tables.assert_subPos (A, (AProp.Pos A)) db)
      
      (* Rule at syntax.l10:118.1-118.30 *)
      
      (* assert -- fvPos (unif T S) Y *)
      fun exec_30_1 (T, Y, S) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Unif (T, S)), Y) db)
      (* fv S Y - syntax.l10:118.23-118.29 *)
      fun exec_30 (T, S) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_30_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) S
      
      (* Rule at syntax.l10:117.1-117.30 *)
      
      (* assert -- fvPos (unif T S) Y *)
      fun exec_29_1 (T, Y, S) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Unif (T, S)), Y) db)
      (* fv T Y - syntax.l10:117.23-117.29 *)
      fun exec_29 (T, S) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_29_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:116.1-116.45 *)
      
      (* assert -- fvPos (exists X T A) Y *)
      fun exec_28_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* X != Y - syntax.l10:116.38-116.44 *)
      fun exec_28_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_28_2 (T, Y, X, A) satu db else db
      (* fvPos A Y - syntax.l10:116.27-116.36 *)
      fun exec_28 (T, X, A) satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_28_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:115.1-115.34 *)
      
      (* assert -- fvPos (exists X T A) Y *)
      fun exec_27_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:115.27-115.33 *)
      fun exec_27 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_27_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:114.1-114.33 *)
      
      (* assert -- fvPos (fuse _ A) Y *)
      fun exec_26_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Fuse (USCORE_1, A)), Y) db)
      (* fvPos A Y - syntax.l10:114.23-114.32 *)
      fun exec_26 (USCORE_1, A) satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_26_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:113.1-113.33 *)
      
      (* assert -- fvPos (fuse A _) Y *)
      fun exec_25_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Fuse (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:113.23-113.32 *)
      fun exec_25 (USCORE_1, A) satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_25_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:112.1-112.33 *)
      
      (* assert -- fvPos (down _ A) Y *)
      fun exec_24_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Down (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:112.23-112.32 *)
      fun exec_24 (USCORE_1, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_24_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:111.1-111.40 *)
      
      (* assert -- fvPos (pAtom _ _ Sp) Y *)
      fun exec_23_1 (USCORE_1, USCORE_2, Sp, Y) satu db =
         (L10_Tables.assert_fvPos ((PosProp.PAtom (USCORE_1, USCORE_2, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:111.27-111.39 *)
      fun exec_23 (USCORE_1, USCORE_2, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_23_1 (USCORE_1, USCORE_2, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:192.1-192.46 *)
      
      (* assert -- headNeg A (atomic P) *)
      fun exec_81_1 (A, P) satu db =
         (L10_Tables.assert_headNeg (A, (Head.Atomic P)) db)
      (* endNeg A (nAtom P _) - syntax.l10:192.25-192.45 *)
      fun exec_81 A satu db =
         L10_Tables.fold_44
            (fn ((x_1_0, x_1_1), db) => 
               exec_81_1 (A, x_1_0 (* P *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:191.1-191.39 *)
      
      (* assert -- headNeg A monadic *)
      fun exec_80_1 A satu db =
         (L10_Tables.assert_headNeg (A, Head.Monadic) db)
      (* endNeg A (lax _) - syntax.l10:191.22-191.38 *)
      fun exec_80 A satu db =
         L10_Tables.fold_43
            (fn (x_1_0, db) => 
               exec_80_1 A satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:181.1-181.37 *)
      
      (* assert -- endNeg (alli _ _ A) H *)
      fun exec_79_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Alli (USCORE_1, USCORE_2, A)), H) db)
      (* endNeg A H - syntax.l10:181.1-181.11 *)
      fun exec_79 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_79_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:180.1-180.36 *)
      
      (* assert -- endNeg (all _ _ A) H *)
      fun exec_78_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.All (USCORE_1, USCORE_2, A)), H) db)
      (* endNeg A H - syntax.l10:180.1-180.11 *)
      fun exec_78 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_78_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:179.1-179.35 *)
      
      (* assert -- endNeg (with _ A) H *)
      fun exec_77_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.With (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:179.1-179.11 *)
      fun exec_77 (USCORE_1, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_77_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:178.1-178.35 *)
      
      (* assert -- endNeg (with A _) H *)
      fun exec_76_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.With (A, USCORE_1)), H) db)
      (* endNeg A H - syntax.l10:178.1-178.11 *)
      fun exec_76 (USCORE_1, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_76_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:177.1-177.37 *)
      
      (* assert -- endNeg (righti _ A) H *)
      fun exec_75_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Righti (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:177.1-177.11 *)
      fun exec_75 (USCORE_1, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_75_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:176.1-176.36 *)
      
      (* assert -- endNeg (lefti _ A) H *)
      fun exec_74_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Lefti (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:176.1-176.11 *)
      fun exec_74 (USCORE_1, A) satu db =
         L10_Tables.fold_17
            (fn (x_1, db) => 
               exec_74_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:175.1-175.24 *)
      
      (* assert -- endNeg (lax A) (lax A) *)
      fun exec_73 A satu db =
         (L10_Tables.assert_endNeg ((NegProp.Lax A), (NegProp.Lax A)) db)
      
      (* Rule at syntax.l10:174.1-174.34 *)
      
      (* assert -- endNeg (nAtom A Sp) (nAtom A Sp) *)
      fun exec_72 (Sp, A) satu db =
         (L10_Tables.assert_endNeg ((NegProp.NAtom (A, Sp)), (NegProp.NAtom (A, Sp))) db)
      
      (* Rule at syntax.l10:171.1-171.39 *)
      
      (* assert -- subgoal (alli _ _ A) H *)
      fun exec_71_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Alli (USCORE_1, USCORE_2, A)), H) db)
      (* subgoal A H - syntax.l10:171.27-171.38 *)
      fun exec_71 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_71_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:170.1-170.38 *)
      
      (* assert -- subgoal (all _ _ A) H *)
      fun exec_70_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_subgoal ((NegProp.All (USCORE_1, USCORE_2, A)), H) db)
      (* subgoal A H - syntax.l10:170.26-170.37 *)
      fun exec_70 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_70_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:169.1-169.37 *)
      
      (* assert -- subgoal (with A B) H *)
      fun exec_69_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.With (A, B)), H) db)
      (* subgoal B H - syntax.l10:169.25-169.36 *)
      fun exec_69 (A, B) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_69_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:168.1-168.37 *)
      
      (* assert -- subgoal (with A B) H *)
      fun exec_68_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.With (A, B)), H) db)
      (* subgoal A H - syntax.l10:168.25-168.36 *)
      fun exec_68 (A, B) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_68_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:167.1-167.39 *)
      
      (* assert -- subgoal (righti A B) H *)
      fun exec_67_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Righti (A, B)), H) db)
      (* subgoal B H - syntax.l10:167.27-167.38 *)
      fun exec_67 (A, B) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_67_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:166.1-166.38 *)
      
      (* assert -- subgoal (righti A B) H *)
      fun exec_66_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Righti (A, B)), H) db)
      (* endPos A H - syntax.l10:166.27-166.37 *)
      fun exec_66 (A, B) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_66_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:165.1-165.38 *)
      
      (* assert -- subgoal (lefti A B) H *)
      fun exec_65_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Lefti (A, B)), H) db)
      (* subgoal B H - syntax.l10:165.26-165.37 *)
      fun exec_65 (A, B) satu db =
         L10_Tables.fold_42
            (fn (x_1, db) => 
               exec_65_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:164.1-164.37 *)
      
      (* assert -- subgoal (lefti A B) H *)
      fun exec_64_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Lefti (A, B)), H) db)
      (* endPos A H - syntax.l10:164.26-164.36 *)
      fun exec_64 (A, B) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_64_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:153.1-153.37 *)
      
      (* assert -- subNeg (alli _ _ A) C *)
      fun exec_57_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Alli (USCORE_1, USCORE_2, A)), C) db)
      (* subNeg A C - syntax.l10:153.26-153.36 *)
      fun exec_57 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_57_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:152.1-152.36 *)
      
      (* assert -- subNeg (all _ _ A) C *)
      fun exec_56_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.All (USCORE_1, USCORE_2, A)), C) db)
      (* subNeg A C - syntax.l10:152.25-152.35 *)
      fun exec_56 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_56_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:151.1-151.35 *)
      
      (* assert -- subNeg (with _ A) C *)
      fun exec_55_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.With (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:151.24-151.34 *)
      fun exec_55 (USCORE_1, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_55_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:150.1-150.35 *)
      
      (* assert -- subNeg (with A _) C *)
      fun exec_54_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.With (A, USCORE_1)), C) db)
      (* subNeg A C - syntax.l10:150.24-150.34 *)
      fun exec_54 (USCORE_1, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_54_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:149.1-149.37 *)
      
      (* assert -- subNeg (righti _ A) C *)
      fun exec_53_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Righti (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:149.26-149.36 *)
      fun exec_53 (USCORE_1, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_53_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:148.1-148.37 *)
      
      (* assert -- subNeg (righti A _) C *)
      fun exec_52_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Righti (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:148.26-148.36 *)
      fun exec_52 (USCORE_1, A) satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_52_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:147.1-147.36 *)
      
      (* assert -- subNeg (lefti _ A) C *)
      fun exec_51_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lefti (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:147.25-147.35 *)
      fun exec_51 (USCORE_1, A) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_51_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:146.1-146.36 *)
      
      (* assert -- subNeg (lefti A _) C *)
      fun exec_50_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lefti (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:146.25-146.35 *)
      fun exec_50 (USCORE_1, A) satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_50_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:145.1-145.32 *)
      
      (* assert -- subNeg (lax A) C *)
      fun exec_49_1 (A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lax A), C) db)
      (* subPos A C - syntax.l10:145.21-145.31 *)
      fun exec_49 A satu db =
         L10_Tables.fold_39
            (fn (x_1, db) => 
               exec_49_1 (A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:144.1-144.18 *)
      
      (* assert -- subNeg A (neg A) *)
      fun exec_48 A satu db =
         (L10_Tables.assert_subNeg (A, (AProp.Neg A)) db)
      
      (* Rule at syntax.l10:132.1-132.43 *)
      
      (* assert -- fvNeg (alli X T A) Y *)
      fun exec_42_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* X != Y - syntax.l10:132.36-132.42 *)
      fun exec_42_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_42_2 (T, Y, X, A) satu db else db
      (* fvNeg A Y - syntax.l10:132.25-132.34 *)
      fun exec_42 (T, X, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_42_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:131.1-131.32 *)
      
      (* assert -- fvNeg (alli X T A) Y *)
      fun exec_41_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:131.25-131.31 *)
      fun exec_41 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_41_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:130.1-130.42 *)
      
      (* assert -- fvNeg (all X T A) Y *)
      fun exec_40_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.All (X, T, A)), Y) db)
      (* X != Y - syntax.l10:130.35-130.41 *)
      fun exec_40_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_40_2 (T, Y, X, A) satu db else db
      (* fvNeg A Y - syntax.l10:130.24-130.33 *)
      fun exec_40 (T, X, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_40_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:129.1-129.31 *)
      
      (* assert -- fvNeg (all X T A) Y *)
      fun exec_39_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.All (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:129.24-129.30 *)
      fun exec_39 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_39_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:128.1-128.33 *)
      
      (* assert -- fvNeg (with _ A) Y *)
      fun exec_38_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.With (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:128.23-128.32 *)
      fun exec_38 (USCORE_1, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_38_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:127.1-127.33 *)
      
      (* assert -- fvNeg (with A _) Y *)
      fun exec_37_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.With (A, USCORE_1)), Y) db)
      (* fvNeg A Y - syntax.l10:127.23-127.32 *)
      fun exec_37 (USCORE_1, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_37_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:126.1-126.35 *)
      
      (* assert -- fvNeg (righti _ A) Y *)
      fun exec_36_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Righti (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:126.25-126.34 *)
      fun exec_36 (USCORE_1, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_36_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:125.1-125.35 *)
      
      (* assert -- fvNeg (righti A _) Y *)
      fun exec_35_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Righti (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:125.25-125.34 *)
      fun exec_35 (USCORE_1, A) satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_35_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:124.1-124.34 *)
      
      (* assert -- fvNeg (lefti _ A) Y *)
      fun exec_34_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lefti (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:124.24-124.33 *)
      fun exec_34 (USCORE_1, A) satu db =
         L10_Tables.fold_11
            (fn (x_1, db) => 
               exec_34_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:123.1-123.34 *)
      
      (* assert -- fvNeg (lefti A _) Y *)
      fun exec_33_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lefti (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:123.24-123.33 *)
      fun exec_33 (USCORE_1, A) satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_33_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:122.1-122.30 *)
      
      (* assert -- fvNeg (lax A) Y *)
      fun exec_32_1 (Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lax A), Y) db)
      (* fvPos A Y - syntax.l10:122.20-122.29 *)
      fun exec_32 A satu db =
         L10_Tables.fold_10
            (fn (x_1, db) => 
               exec_32_1 (x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:121.1-121.38 *)
      
      (* assert -- fvNeg (nAtom _ Sp) Y *)
      fun exec_31_1 (USCORE_1, Sp, Y) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.NAtom (USCORE_1, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:121.25-121.37 *)
      fun exec_31 (USCORE_1, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_31_1 (USCORE_1, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:205.1-205.47 *)
      
      (* assert -- classify C Eh *)
      fun exec_83_3 (Eh, C) satu db =
         (L10_Tables.assert_classify (C, Eh) db)
      (* headClass E Eh - syntax.l10:205.32-205.46 *)
      fun exec_83_2 (E, C) satu db =
         L10_Tables.fold_38
            (fn (x_1, db) => 
               exec_83_3 (x_1 (* Eh *), C) satu db)
            db (#2 db) E
      (* Dynamic world search: wExp E *)
      fun exec_83_1 (E, C) satu (flag, db) =
         exec_83_2 (E, C) satu (flag, satu (World.WExp E) db)
      (* signat C E _ - syntax.l10:205.18-205.30 *)
      fun exec_83 () satu db =
         L10_Tables.fold_37
            (fn ((x_0, x_1, x_2), db) => 
               exec_83_1 (x_1 (* E *), x_0 (* C *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:227.1-229.22 *)
      
      (* assert -- ruleSubord H1 H3 *)
      fun exec_86_2 (H1, H3) satu db =
         (L10_Tables.assert_ruleSubord (H1, H3) db)
      (* ruleSubord H2 H3 - syntax.l10:228.1-228.17 *)
      fun exec_86_1 (H1, H2) satu db =
         L10_Tables.fold_36
            (fn (x_1, db) => 
               exec_86_2 (H1, x_1 (* H3 *)) satu db)
            db (#2 db) H2
      (* ruleSubord H1 H2 - syntax.l10:227.1-227.17 *)
      fun exec_86 () satu db =
         L10_Tables.fold_35
            (fn ((x_0, x_1), db) => 
               exec_86_1 (x_0 (* H1 *), x_1 (* H2 *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:221.1-225.22 *)
      
      (* assert -- ruleSubord H1 H2 *)
      fun exec_85_7 (H1, H2) satu db =
         (L10_Tables.assert_ruleSubord (H1, H2) db)
      (* headNeg B2 H2 - syntax.l10:224.1-224.14 *)
      fun exec_85_6 (B2, H1) satu db =
         L10_Tables.fold_33
            (fn (x_1, db) => 
               exec_85_7 (H1, x_1 (* H2 *)) satu db)
            db (#2 db) B2
      (* Dynamic world search: wNeg B2 *)
      fun exec_85_5 (B2, H1) satu (flag, db) =
         exec_85_6 (B2, H1) satu (flag, satu (World.WNeg B2) db)
      (* headPos B1 H1 - syntax.l10:223.1-223.14 *)
      fun exec_85_4 (B1, B2) satu db =
         L10_Tables.fold_32
            (fn (x_1, db) => 
               exec_85_5 (B2, x_1 (* H1 *)) satu db)
            db (#2 db) B1
      (* Dynamic world search: wPos B1 *)
      fun exec_85_3 (B1, B2) satu (flag, db) =
         exec_85_4 (B1, B2) satu (flag, satu (World.WPos B1) db)
      (* subNeg A (neg (righti B1 B2)) - syntax.l10:222.1-222.30 *)
      fun exec_85_2 A satu db =
         L10_Tables.fold_34
            (fn ((x_1_0_0, x_1_0_1), db) => 
               exec_85_3 (x_1_0_0 (* B1 *), x_1_0_1 (* B2 *)) satu db)
            db (#2 db) A
      (* Dynamic world search: wNeg A *)
      fun exec_85_1 A satu (flag, db) =
         exec_85_2 A satu (flag, satu (World.WNeg A) db)
      (* rules C A - syntax.l10:221.1-221.10 *)
      fun exec_85 () satu db =
         L10_Tables.fold_30
            (fn ((x_0, x_1), db) => 
               exec_85_1 x_1 (* A *) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:215.1-219.22 *)
      
      (* assert -- ruleSubord H1 H2 *)
      fun exec_84_7 (H1, H2) satu db =
         (L10_Tables.assert_ruleSubord (H1, H2) db)
      (* headNeg B2 H2 - syntax.l10:218.1-218.14 *)
      fun exec_84_6 (B2, H1) satu db =
         L10_Tables.fold_33
            (fn (x_1, db) => 
               exec_84_7 (H1, x_1 (* H2 *)) satu db)
            db (#2 db) B2
      (* Dynamic world search: wNeg B2 *)
      fun exec_84_5 (B2, H1) satu (flag, db) =
         exec_84_6 (B2, H1) satu (flag, satu (World.WNeg B2) db)
      (* headPos B1 H1 - syntax.l10:217.1-217.14 *)
      fun exec_84_4 (B1, B2) satu db =
         L10_Tables.fold_32
            (fn (x_1, db) => 
               exec_84_5 (B2, x_1 (* H1 *)) satu db)
            db (#2 db) B1
      (* Dynamic world search: wPos B1 *)
      fun exec_84_3 (B1, B2) satu (flag, db) =
         exec_84_4 (B1, B2) satu (flag, satu (World.WPos B1) db)
      (* subNeg A (neg (lefti B1 B2)) - syntax.l10:216.1-216.29 *)
      fun exec_84_2 A satu db =
         L10_Tables.fold_31
            (fn ((x_1_0_0, x_1_0_1), db) => 
               exec_84_3 (x_1_0_0 (* B1 *), x_1_0_1 (* B2 *)) satu db)
            db (#2 db) A
      (* Dynamic world search: wNeg A *)
      fun exec_84_1 A satu (flag, db) =
         exec_84_2 A satu (flag, satu (World.WNeg A) db)
      (* rules C A - syntax.l10:215.1-215.10 *)
      fun exec_84 () satu db =
         L10_Tables.fold_30
            (fn ((x_0, x_1), db) => 
               exec_84_1 x_1 (* A *) satu db)
            db (#2 db) ()
      
   end
   
   
   (* L10 Generated Tabled Search (search.sml) *)
   
   structure L10_Search = 
   struct
      fun loop fs (db: L10_Tables.tables) = 
         case fs (false, db) of
            (false, db) => db
          | (true, db) => loop fs db
      
      fun saturate x_0 db =
        (case x_0 of 
            World.World =>
               saturate_world db
          | World.WExp x_0_0 =>
               saturate_wExp x_0_0 db
          | World.WSpine x_0_0 =>
               saturate_wSpine x_0_0 db
          | World.WMode =>
               saturate_wMode db
          | World.WPos x_0_0 =>
               saturate_wPos x_0_0 db
          | World.WNeg x_0_0 =>
               saturate_wNeg x_0_0 db
          | World.WSignat =>
               saturate_wSignat db
          | World.WRuleSubord =>
               saturate_wRuleSubord db)
      
      and saturate_world db =
      let
         val w = World.World
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
            (* world *)
            let
               (* Rule #87, default world *)
               (* syntax.l10:238.1-238.47 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_87 () saturate o exec
               
               (* Rule #88, default world *)
               (* syntax.l10:241.1-241.81 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_88 () saturate o exec
               
               (* Rule #89, default world *)
               (* syntax.l10:244.1-244.50 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_89 () saturate o exec
            in
               loop exec db
            end
         end
      end
      
      and saturate_wExp x_0 db =
      let
         val w = World.WExp x_0
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
           (case x_0 of 
               Exp.Knd =>
                  (* wExp knd *)
                  let
                     (* Rule #1, world (wExp knd) *)
                     (* syntax.l10:61.1-61.19 *)
                     val exec = L10_Consequence.exec_1 () saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Typ =>
                  (* wExp typ *)
                  let
                     (* Rule #2, world (wExp typ) *)
                     (* syntax.l10:62.1-62.19 *)
                     val exec = L10_Consequence.exec_2 () saturate o exec
                  in
                     loop exec db
                  end
             | Exp.NProp =>
                  (* wExp nProp *)
                  let
                     (* Rule #3, world (wExp nProp) *)
                     (* syntax.l10:63.1-63.23 *)
                     val exec = L10_Consequence.exec_3 () saturate o exec
                  in
                     loop exec db
                  end
             | Exp.PProp x_0_0 =>
                  (* wExp (pProp x_0_0) *)
                  let
                     (* Rule #4, world (wExp (pProp Perm)) *)
                     (* syntax.l10:64.1-64.37 *)
                     (* { Perm |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_4 x_0_0 saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Pi (x_0_0, x_0_1, x_0_2) =>
                  (* wExp (pi x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #6, world (wExp (pi _ _ E)) *)
                     (* syntax.l10:66.1-66.44 *)
                     (* { E |-> [ x_0_2 ],
                      *   USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_6 (x_0_2, x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #8, world (wExp (pi X T E)) *)
                     (* syntax.l10:72.1-72.27 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_8 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #9, world (wExp (pi X T E)) *)
                     (* syntax.l10:73.1-73.35 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_9 (x_0_2, x_0_1, x_0_0) saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Pii (x_0_0, x_0_1, x_0_2) =>
                  (* wExp (pii x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #5, world (wExp (pii _ _ E)) *)
                     (* syntax.l10:65.1-65.44 *)
                     (* { E |-> [ x_0_2 ],
                      *   USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_5 (x_0_2, x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #10, world (wExp (pii X T E)) *)
                     (* syntax.l10:74.1-74.28 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_10 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #11, world (wExp (pii X T E)) *)
                     (* syntax.l10:75.1-75.36 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_11 (x_0_2, x_0_1, x_0_0) saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Arrow (x_0_0, x_0_1) =>
                  (* wExp (arrow x_0_0 x_0_1) *)
                  let
                     (* Rule #7, world (wExp (arrow _ E)) *)
                     (* syntax.l10:67.1-67.44 *)
                     (* { E |-> [ x_0_1 ],
                      *   USCORE_1 |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_7 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #12, world (wExp (arrow E1 E2)) *)
                     (* syntax.l10:76.1-76.31 *)
                     (* { E1 |-> [ x_0_0 ],
                      *   E2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_12 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #13, world (wExp (arrow E1 E2)) *)
                     (* syntax.l10:77.1-77.31 *)
                     (* { E1 |-> [ x_0_0 ],
                      *   E2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_13 (x_0_0, x_0_1) saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Var (x_0_0, x_0_1, x_0_2) =>
                  (* wExp (var x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #14, world (wExp (var X _ Sp)) *)
                     (* syntax.l10:78.1-78.19 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ],
                      *   X |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_14 (x_0_1, x_0_2, x_0_0) saturate o exec
                     
                     (* Rule #15, world (wExp (var X _ Sp)) *)
                     (* syntax.l10:79.1-79.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wSpine x_0_2 db
                     val exec = L10_Consequence.exec_15 (x_0_1, x_0_2, x_0_0) saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Con (x_0_0, x_0_1) =>
                  (* wExp (con x_0_0 x_0_1) *)
                  let
                     (* Rule #16, world (wExp (con _ Sp)) *)
                     (* syntax.l10:80.1-80.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_16 (x_0_0, x_0_1) saturate o exec
                  in
                     loop exec db
                  end
             | Exp.Lam (x_0_0, x_0_1) =>
                  (* wExp (lam x_0_0 x_0_1) *)
                  let
                     (* Rule #17, world (wExp (lam X E)) *)
                     (* syntax.l10:81.1-81.34 *)
                     (* { E |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_17 (x_0_1, x_0_0) saturate o exec
                  in
                     loop exec db
                  end)
         end
      end
      
      and saturate_wSpine x_0 db =
      let
         val w = World.WSpine x_0
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
           (case x_0 of 
               Spine.App (x_0_0, x_0_1) =>
                  (* wSpine (app x_0_0 x_0_1) *)
                  let
                     (* Rule #18, world (wSpine (app E Sp)) *)
                     (* syntax.l10:84.1-84.32 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_18 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #19, world (wSpine (app E Sp)) *)
                     (* syntax.l10:85.1-85.38 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_19 (x_0_0, x_0_1) saturate o exec
                  in
                     loop exec db
                  end
             | Spine.Appi (x_0_0, x_0_1) =>
                  (* wSpine (appi x_0_0 x_0_1) *)
                  let
                     (* Rule #20, world (wSpine (appi E Sp)) *)
                     (* syntax.l10:86.1-86.33 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_20 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #21, world (wSpine (appi E Sp)) *)
                     (* syntax.l10:87.1-87.39 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_21 (x_0_0, x_0_1) saturate o exec
                  in
                     loop exec db
                  end
             | _ =>
                  (* wSpine x_0 *)
                  let
                  in
                     loop exec db
                  end)
         end
      end
      
      and saturate_wMode db =
      let
         val w = World.WMode
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
            (* wMode *)
            let
               (* Rule #22, world wMode *)
               (* syntax.l10:100.1-100.38 *)
               val exec = L10_Consequence.exec_22 () saturate o exec
            in
               loop exec db
            end
         end
      end
      
      and saturate_wPos x_0 db =
      let
         val w = World.WPos x_0
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
           (case x_0 of 
               PosProp.PAtom (x_0_0, x_0_1, x_0_2) =>
                  (* wPos (pAtom x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #23, world (wPos (pAtom _ _ Sp)) *)
                     (* syntax.l10:111.1-111.40 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ] } *)
                     val db = saturate_wSpine x_0_2 db
                     val exec = L10_Consequence.exec_23 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0=(pAtom x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #58, world (wPos (pAtom P A Sp)) *)
                     (* syntax.l10:156.1-156.38 *)
                     (* { Sp |-> [ x_0_2 ],
                      *   A |-> [ x_0_1 ],
                      *   P |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_58 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0=(pAtom x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Down (x_0_0, x_0_1) =>
                  (* wPos (down x_0_0 x_0_1) *)
                  let
                     (* Rule #24, world (wPos (down _ A)) *)
                     (* syntax.l10:112.1-112.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_24 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0=(down x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #44, world (wPos (down _ A)) *)
                     (* syntax.l10:139.1-139.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_44 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #59, world (wPos (down P A)) *)
                     (* syntax.l10:157.1-157.30 *)
                     (* { A |-> [ x_0_1 ],
                      *   P |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_59 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0=(down x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Fuse (x_0_0, x_0_1) =>
                  (* wPos (fuse x_0_0 x_0_1) *)
                  let
                     (* Rule #25, world (wPos (fuse A _)) *)
                     (* syntax.l10:113.1-113.33 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_25 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #26, world (wPos (fuse _ A)) *)
                     (* syntax.l10:114.1-114.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_26 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0=(fuse x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #45, world (wPos (fuse A _)) *)
                     (* syntax.l10:140.1-140.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_45 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #46, world (wPos (fuse _ A)) *)
                     (* syntax.l10:141.1-141.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_46 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #60, world (wPos (fuse A _)) *)
                     (* syntax.l10:158.1-158.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_60 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #61, world (wPos (fuse _ A)) *)
                     (* syntax.l10:159.1-159.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_61 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0=(fuse x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Exists (x_0_0, x_0_1, x_0_2) =>
                  (* wPos (exists x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #27, world (wPos (exists X T A)) *)
                     (* syntax.l10:115.1-115.34 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_27 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #28, world (wPos (exists X T A)) *)
                     (* syntax.l10:116.1-116.45 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_28 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0=(exists x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #47, world (wPos (exists _ _ A)) *)
                     (* syntax.l10:142.1-142.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_47 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #62, world (wPos (exists _ _ A)) *)
                     (* syntax.l10:160.1-160.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_62 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0=(exists x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Unif (x_0_0, x_0_1) =>
                  (* wPos (unif x_0_0 x_0_1) *)
                  let
                     (* Rule #29, world (wPos (unif T S)) *)
                     (* syntax.l10:117.1-117.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_29 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #30, world (wPos (unif T S)) *)
                     (* syntax.l10:118.1-118.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_30 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0=(unif x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #63, world (wPos (unif T S)) *)
                     (* syntax.l10:161.1-161.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val exec = L10_Consequence.exec_63 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0=(unif x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | _ =>
                  (* wPos x_0 *)
                  let
                     (* Rule #43, world (wPos A) *)
                     (* syntax.l10:138.1-138.18 *)
                     (* { A |-> [ x_0 ] } *)
                     val exec = L10_Consequence.exec_43 x_0 saturate o exec
                     
                     (* Rule #82, world (wPos A) *)
                     (* syntax.l10:193.1-193.51 *)
                     (* { A |-> [ x_0 ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                  in
                     loop exec db
                  end)
         end
      end
      
      and saturate_wNeg x_0 db =
      let
         val w = World.WNeg x_0
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
           (case x_0 of 
               NegProp.NAtom (x_0_0, x_0_1) =>
                  (* wNeg (nAtom x_0_0 x_0_1) *)
                  let
                     (* Rule #31, world (wNeg (nAtom _ Sp)) *)
                     (* syntax.l10:121.1-121.38 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_31 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #72, world (wNeg (nAtom A Sp)) *)
                     (* syntax.l10:174.1-174.34 *)
                     (* { Sp |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_72 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Lax x_0_0 =>
                  (* wNeg (lax x_0_0) *)
                  let
                     (* Rule #32, world (wNeg (lax A)) *)
                     (* syntax.l10:122.1-122.30 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_32 x_0_0 saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #49, world (wNeg (lax A)) *)
                     (* syntax.l10:145.1-145.32 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_49 x_0_0 saturate o exec
                     
                     (* Rule #73, world (wNeg (lax A)) *)
                     (* syntax.l10:175.1-175.24 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_73 x_0_0 saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Lefti (x_0_0, x_0_1) =>
                  (* wNeg (lefti x_0_0 x_0_1) *)
                  let
                     (* Rule #33, world (wNeg (lefti A _)) *)
                     (* syntax.l10:123.1-123.34 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_33 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #34, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:124.1-124.34 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_34 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #50, world (wNeg (lefti A _)) *)
                     (* syntax.l10:146.1-146.36 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_50 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #51, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:147.1-147.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_51 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #64, world (wNeg (lefti A B)) *)
                     (* syntax.l10:164.1-164.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_64 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #65, world (wNeg (lefti A B)) *)
                     (* syntax.l10:165.1-165.38 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_65 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #74, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:176.1-176.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_74 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Righti (x_0_0, x_0_1) =>
                  (* wNeg (righti x_0_0 x_0_1) *)
                  let
                     (* Rule #35, world (wNeg (righti A _)) *)
                     (* syntax.l10:125.1-125.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_35 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #36, world (wNeg (righti _ A)) *)
                     (* syntax.l10:126.1-126.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_36 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #52, world (wNeg (righti A _)) *)
                     (* syntax.l10:148.1-148.37 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_52 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #53, world (wNeg (righti _ A)) *)
                     (* syntax.l10:149.1-149.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_53 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #66, world (wNeg (righti A B)) *)
                     (* syntax.l10:166.1-166.38 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_66 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #67, world (wNeg (righti A B)) *)
                     (* syntax.l10:167.1-167.39 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_67 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #75, world (wNeg (righti _ A)) *)
                     (* syntax.l10:177.1-177.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_75 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.With (x_0_0, x_0_1) =>
                  (* wNeg (with x_0_0 x_0_1) *)
                  let
                     (* Rule #37, world (wNeg (with A _)) *)
                     (* syntax.l10:127.1-127.33 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_37 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #38, world (wNeg (with _ A)) *)
                     (* syntax.l10:128.1-128.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_38 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #54, world (wNeg (with A _)) *)
                     (* syntax.l10:150.1-150.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_54 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #55, world (wNeg (with _ A)) *)
                     (* syntax.l10:151.1-151.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_55 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #68, world (wNeg (with A B)) *)
                     (* syntax.l10:168.1-168.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_68 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #69, world (wNeg (with A B)) *)
                     (* syntax.l10:169.1-169.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_69 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #76, world (wNeg (with A _)) *)
                     (* syntax.l10:178.1-178.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_76 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #77, world (wNeg (with _ A)) *)
                     (* syntax.l10:179.1-179.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_77 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.All (x_0_0, x_0_1, x_0_2) =>
                  (* wNeg (all x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #39, world (wNeg (all X T A)) *)
                     (* syntax.l10:129.1-129.31 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_39 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #40, world (wNeg (all X T A)) *)
                     (* syntax.l10:130.1-130.42 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_40 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #56, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:152.1-152.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_56 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #70, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:170.1-170.38 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_70 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #78, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:180.1-180.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_78 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Alli (x_0_0, x_0_1, x_0_2) =>
                  (* wNeg (alli x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #41, world (wNeg (alli X T A)) *)
                     (* syntax.l10:131.1-131.32 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_41 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #42, world (wNeg (alli X T A)) *)
                     (* syntax.l10:132.1-132.43 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_42 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #48, world (wNeg A) *)
                     (* syntax.l10:144.1-144.18 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_48 x_0 saturate o exec
                     
                     (* Rule #57, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:153.1-153.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_57 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #71, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:171.1-171.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_71 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #79, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:181.1-181.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_79 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #80, world (wNeg A) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_80 x_0 saturate o exec
                     
                     (* Rule #81, world (wNeg A) *)
                     (* syntax.l10:192.1-192.46 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_81 x_0 saturate o exec
                  in
                     loop exec db
                  end)
         end
      end
      
      and saturate_wSignat db =
      let
         val w = World.WSignat
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
            (* wSignat *)
            let
               (* Rule #83, world wSignat *)
               (* syntax.l10:205.1-205.47 *)
               val exec = L10_Consequence.exec_83 () saturate o exec
            in
               loop exec db
            end
         end
      end
      
      and saturate_wRuleSubord db =
      let
         val w = World.WRuleSubord
         val worldset = L10_Tables.get_worlds db
         (* val () = print ("Entering "^World.toString w^"...") *)
         val exec = fn x => x
      in if World.Dict.member worldset w
      then ((* print "already visited.\n"; *) db) else
         let
            (* val () = print "entering.\n" *)
            val db = L10_Tables.set_worlds db (World.Dict.insert worldset w ())
         in
            (* wRuleSubord *)
            let
               (* Rule #84, world wRuleSubord *)
               (* syntax.l10:215.1-219.22 *)
               val db = saturate_wSignat db
               val exec = L10_Consequence.exec_84 () saturate o exec
               
               (* Rule #85, world wRuleSubord *)
               (* syntax.l10:221.1-225.22 *)
               val db = saturate_wSignat db
               val exec = L10_Consequence.exec_85 () saturate o exec
               
               (* Rule #86, world wRuleSubord *)
               (* syntax.l10:227.1-229.22 *)
               val exec = L10_Consequence.exec_86 () saturate o exec
            in
               loop exec db
            end
         end
      end
   end
   
   
   (* L10 public interface (interface.sml) *)
   
   type db = {pristine: L10_Tables.tables,
              public: L10_Tables.tables ref}
   type head = Head.t
   type mode = Mode.t
   type aProp = AProp.t
   type negProp = NegProp.t
   type posProp = PosProp.t
   type spine = Spine.t
   type exp = Exp.t
   type perm = Perm.t
   type cid = Symbol.symbol
   type rel = Rel.t
   type world = World.t
   type string = String.string
   type nat = IntInf.int
   
   val empty = 
      let val table = L10_Tables.empty ()
      in {pristine=table, public=ref table} end
   
   structure Assert =
   struct
      fun notSemanticEffects (db: db) =
         case L10_Tables.assert_notSemanticEffects () (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun weaklySemanticEffects (db: db) =
         case L10_Tables.assert_weaklySemanticEffects () (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun semanticEffects (db: db) =
         case L10_Tables.assert_semanticEffects () (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun ruleSubord (args, db: db) =
         case L10_Tables.assert_ruleSubord args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun classify (args, db: db) =
         case L10_Tables.assert_classify args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun rules (args, db: db) =
         case L10_Tables.assert_rules args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun signat (args, db: db) =
         case L10_Tables.assert_signat args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun headNeg (args, db: db) =
         case L10_Tables.assert_headNeg args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun headPos (args, db: db) =
         case L10_Tables.assert_headPos args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun endNeg (args, db: db) =
         case L10_Tables.assert_endNeg args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun subgoal (args, db: db) =
         case L10_Tables.assert_subgoal args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun endPos (args, db: db) =
         case L10_Tables.assert_endPos args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun subNeg (args, db: db) =
         case L10_Tables.assert_subNeg args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun subPos (args, db: db) =
         case L10_Tables.assert_subPos args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun fvNeg (args, db: db) =
         case L10_Tables.assert_fvNeg args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun fvPos (args, db: db) =
         case L10_Tables.assert_fvPos args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun varMode (args, db: db) =
         case L10_Tables.assert_varMode args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun givenMode (args, db: db) =
         case L10_Tables.assert_givenMode args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun fvSpine (args, db: db) =
         case L10_Tables.assert_fvSpine args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun fv (args, db: db) =
         case L10_Tables.assert_fv args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun headClass (args, db: db) =
         case L10_Tables.assert_headClass args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
   end
   
   structure Query =
   struct
      fun notSemanticEffects f x (db: db) =
      let
         val public = L10_Search.saturate_world (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_29 f x public ())
      end
      val notSemanticEffects = fn x => notSemanticEffects (fn _ => true) false x
      
      fun weaklySemanticEffects f x (db: db) =
      let
         val public = L10_Search.saturate_world (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_28 f x public ())
      end
      val weaklySemanticEffects = fn x => weaklySemanticEffects (fn _ => true) false x
      
      fun semanticEffects f x (db: db) =
      let
         val public = L10_Search.saturate_world (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_27 f x public ())
      end
      val semanticEffects = fn x => semanticEffects (fn _ => true) false x
      
      fun ruleSubord f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wRuleSubord (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_26 f x public (x_0, x_1))
      end
      val ruleSubord = fn x => ruleSubord (fn _ => true) false x
      
      fun lookupClass f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_25 f x public x_0)
      end
      val lookupClassList = lookupClass (op ::) []
      
      fun classify f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_24 f x public (x_0, x_1))
      end
      val classify = fn x => classify (fn _ => true) false x
      
      fun lookupRule f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_23 f x public x_0)
      end
      val lookupRuleList = lookupRule (op ::) []
      
      fun lookup f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_22 f x public x_0)
      end
      val lookupList = lookup (op ::) []
      
      fun rules f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_21 f x public (x_0, x_1))
      end
      val rules = fn x => rules (fn _ => true) false x
      
      fun signat f x (db: db) (x_0, x_1, x_2) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_20 f x public (x_0, x_1, x_2))
      end
      val signat = fn x => signat (fn _ => true) false x
      
      fun headNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_19 f x public (x_0, x_1))
      end
      val headNeg = fn x => headNeg (fn _ => true) false x
      
      fun headPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_18 f x public (x_0, x_1))
      end
      val headPos = fn x => headPos (fn _ => true) false x
      
      fun negHeads f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_17 f x public x_0)
      end
      val negHeadsList = negHeads (op ::) []
      
      fun endNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_16 f x public (x_0, x_1))
      end
      val endNeg = fn x => endNeg (fn _ => true) false x
      
      fun subgoal f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_15 f x public (x_0, x_1))
      end
      val subgoal = fn x => subgoal (fn _ => true) false x
      
      fun endPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_14 f x public (x_0, x_1))
      end
      val endPos = fn x => endPos (fn _ => true) false x
      
      fun subNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_13 f x public (x_0, x_1))
      end
      val subNeg = fn x => subNeg (fn _ => true) false x
      
      fun subPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_12 f x public (x_0, x_1))
      end
      val subPos = fn x => subPos (fn _ => true) false x
      
      fun freevarsNeg f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_11 f x public x_0)
      end
      val freevarsNegList = freevarsNeg (op ::) []
      
      fun freevarsPos f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_10 f x public x_0)
      end
      val freevarsPosList = freevarsPos (op ::) []
      
      fun fvNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_9 f x public (x_0, x_1))
      end
      val fvNeg = fn x => fvNeg (fn _ => true) false x
      
      fun fvPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_8 f x public (x_0, x_1))
      end
      val fvPos = fn x => fvPos (fn _ => true) false x
      
      fun varMode f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wMode (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_7 f x public (x_0, x_1))
      end
      val varMode = fn x => varMode (fn _ => true) false x
      
      fun givenMode f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wMode (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_6 f x public (x_0, x_1))
      end
      val givenMode = fn x => givenMode (fn _ => true) false x
      
      fun freevarsSpine f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSpine x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_5 f x public x_0)
      end
      val freevarsSpineList = freevarsSpine (op ::) []
      
      fun freevars f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wExp x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_4 f x public x_0)
      end
      val freevarsList = freevars (op ::) []
      
      fun fvSpine f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSpine x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_3 f x public (x_0, x_1))
      end
      val fvSpine = fn x => fvSpine (fn _ => true) false x
      
      fun fv f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wExp x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_2 f x public (x_0, x_1))
      end
      val fv = fn x => fv (fn _ => true) false x
      
      fun headClass f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wExp x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_1 f x public (x_0, x_1))
      end
      val headClass = fn x => headClass (fn _ => true) false x
   end
end
