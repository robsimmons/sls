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
      val allvNeg:               (negProp * string) * db -> db
      val allvPos:               (posProp * string) * db -> db
      val fvNeg:                 (negProp * string) * db -> db
      val fvPos:                 (posProp * string) * db -> db
      val varMode:               (string * mode) * db -> db
      val givenMode:             (exp * mode) * db -> db
      val allvSpine:             (spine * string) * db -> db
      val allv:                  (exp * string) * db -> db
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
      val allvNeg:               db -> (negProp * string) -> bool
      val allvPos:               db -> (posProp * string) -> bool
      val fvNeg:                 db -> (negProp * string) -> bool
      val fvPos:                 db -> (posProp * string) -> bool
      val varMode:               db -> (string * mode) -> bool
      val givenMode:             db -> (exp * mode) -> bool
      val allvSpine:             db -> (spine * string) -> bool
      val allv:                  db -> (exp * string) -> bool
      val fvSpine:               db -> (spine * string) -> bool
      val fv:                    db -> (exp * string) -> bool
      val headClass:             db -> (exp * exp) -> bool
      
      val lookupClass:           (exp * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val lookupRule:            (negProp * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val lookup:                ((exp * exp) * 'a -> 'a) -> 'a -> db -> cid -> 'a
      val negHeads:              (negProp * 'a -> 'a) -> 'a -> db -> negProp -> 'a
      val allvarsNeg:            (string * 'a -> 'a) -> 'a -> db -> negProp -> 'a
      val allvarsPos:            (string * 'a -> 'a) -> 'a -> db -> posProp -> 'a
      val freevarsNeg:           (string * 'a -> 'a) -> 'a -> db -> negProp -> 'a
      val freevarsPos:           (string * 'a -> 'a) -> 'a -> db -> posProp -> 'a
      val allvarsSpine:          (string * 'a -> 'a) -> 'a -> db -> spine -> 'a
      val allvars:               (string * 'a -> 'a) -> 'a -> db -> exp -> 'a
      val freevarsSpine:         (string * 'a -> 'a) -> 'a -> db -> spine -> 'a
      val freevars:              (string * 'a -> 'a) -> 'a -> db -> exp -> 'a
      
      val lookupClassList: db -> cid -> exp list (* = lookupClass (op ::) [] *)
      val lookupRuleList: db -> cid -> negProp list (* = lookupRule (op ::) [] *)
      val lookupList: db -> cid -> (exp * exp) list (* = lookup (op ::) [] *)
      val negHeadsList: db -> negProp -> negProp list (* = negHeads (op ::) [] *)
      val allvarsNegList: db -> negProp -> string list (* = allvarsNeg (op ::) [] *)
      val allvarsPosList: db -> posProp -> string list (* = allvarsPos (op ::) [] *)
      val freevarsNegList: db -> negProp -> string list (* = freevarsNeg (op ::) [] *)
      val freevarsPosList: db -> posProp -> string list (* = freevarsPos (op ::) [] *)
      val allvarsSpineList: db -> spine -> string list (* = allvarsSpine (op ::) [] *)
      val allvarsList: db -> exp -> string list (* = allvars (op ::) [] *)
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
   | Allv of t_exp * String.string
   | AllvSpine of t_spine * String.string
   | GivenMode of t_exp * t_mode
   | VarMode of String.string * t_mode
   | FvPos of t_posProp * String.string
   | FvNeg of t_negProp * String.string
   | AllvPos of t_posProp * String.string
   | AllvNeg of t_negProp * String.string
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
       | (Allv (x_0, x_1), Allv (y_0, y_1)) => 
            eq_exp (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (AllvSpine (x_0, x_1), AllvSpine (y_0, y_1)) => 
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
       | (AllvPos (x_0, x_1), AllvPos (y_0, y_1)) => 
            eq_posProp (x_0, y_0)
            andalso (EQUAL = String.compare (x_1, y_1))
       | (AllvNeg (x_0, x_1), AllvNeg (y_0, y_1)) => 
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
       | Allv (x_0, x_1) => 
            "(Allv "^str_exp x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | AllvSpine (x_0, x_1) => 
            "(AllvSpine "^str_spine x_0
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
       | AllvPos (x_0, x_1) => 
            "(AllvPos "^str_posProp x_0
            ^" "^("\"" ^ x_1 ^ "\"")^")"
       | AllvNeg (x_0, x_1) => 
            "(AllvNeg "^str_negProp x_0
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
       | Allv (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_exp x_0 o
            DiscDict.sub 3
       | AllvSpine (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_spine x_0 o
            DiscDict.sub 4
       | GivenMode (x_0, x_1) => 
            sub_mode x_1 o
            sub_exp x_0 o
            DiscDict.sub 5
       | VarMode (x_0, x_1) => 
            sub_mode x_1 o
            DiscDict.subString x_0 o
            DiscDict.sub 6
       | FvPos (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_posProp x_0 o
            DiscDict.sub 7
       | FvNeg (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_negProp x_0 o
            DiscDict.sub 8
       | AllvPos (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_posProp x_0 o
            DiscDict.sub 9
       | AllvNeg (x_0, x_1) => 
            DiscDict.subString x_1 o
            sub_negProp x_0 o
            DiscDict.sub 10
       | SubPos (x_0, x_1) => 
            sub_aProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 11
       | SubNeg (x_0, x_1) => 
            sub_aProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 12
       | EndPos (x_0, x_1) => 
            sub_posProp x_1 o
            sub_posProp x_0 o
            DiscDict.sub 13
       | Subgoal (x_0, x_1) => 
            sub_posProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 14
       | EndNeg (x_0, x_1) => 
            sub_negProp x_1 o
            sub_negProp x_0 o
            DiscDict.sub 15
       | HeadPos (x_0, x_1) => 
            sub_head x_1 o
            sub_posProp x_0 o
            DiscDict.sub 16
       | HeadNeg (x_0, x_1) => 
            sub_head x_1 o
            sub_negProp x_0 o
            DiscDict.sub 17
       | Signat (x_0, x_1, x_2) => 
            sub_exp x_2 o
            sub_exp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 18
       | Rules (x_0, x_1) => 
            sub_negProp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 19
       | Classify (x_0, x_1) => 
            sub_exp x_1 o
            DiscDict.subCid x_0 o
            DiscDict.sub 20
       | RuleSubord (x_0, x_1) => 
            sub_head x_1 o
            sub_head x_0 o
            DiscDict.sub 21
       | SemanticEffects => 
            DiscDict.sub 22
       | WeaklySemanticEffects => 
            DiscDict.sub 23
       | NotSemanticEffects => 
            DiscDict.sub 24)
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
            DiscDict.unzip (0, 25)
       | Fv (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (1, 25)
       | FvSpine (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_spine x_0 o
            DiscDict.unzip (2, 25)
       | Allv (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (3, 25)
       | AllvSpine (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_spine x_0 o
            DiscDict.unzip (4, 25)
       | GivenMode (x_0, x_1) => 
            unzip_mode x_1 o
            unzip_exp x_0 o
            DiscDict.unzip (5, 25)
       | VarMode (x_0, x_1) => 
            unzip_mode x_1 o
            DiscDict.unzipString x_0 o
            DiscDict.unzip (6, 25)
       | FvPos (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (7, 25)
       | FvNeg (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (8, 25)
       | AllvPos (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (9, 25)
       | AllvNeg (x_0, x_1) => 
            DiscDict.unzipString x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (10, 25)
       | SubPos (x_0, x_1) => 
            unzip_aProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (11, 25)
       | SubNeg (x_0, x_1) => 
            unzip_aProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (12, 25)
       | EndPos (x_0, x_1) => 
            unzip_posProp x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (13, 25)
       | Subgoal (x_0, x_1) => 
            unzip_posProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (14, 25)
       | EndNeg (x_0, x_1) => 
            unzip_negProp x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (15, 25)
       | HeadPos (x_0, x_1) => 
            unzip_head x_1 o
            unzip_posProp x_0 o
            DiscDict.unzip (16, 25)
       | HeadNeg (x_0, x_1) => 
            unzip_head x_1 o
            unzip_negProp x_0 o
            DiscDict.unzip (17, 25)
       | Signat (x_0, x_1, x_2) => 
            unzip_exp x_2 o
            unzip_exp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (18, 25)
       | Rules (x_0, x_1) => 
            unzip_negProp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (19, 25)
       | Classify (x_0, x_1) => 
            unzip_exp x_1 o
            DiscDict.unzipCid x_0 o
            DiscDict.unzip (20, 25)
       | RuleSubord (x_0, x_1) => 
            unzip_head x_1 o
            unzip_head x_0 o
            DiscDict.unzip (21, 25)
       | SemanticEffects => 
            DiscDict.unzip (22, 25)
       | WeaklySemanticEffects => 
            DiscDict.unzip (23, 25)
       | NotSemanticEffects => 
            DiscDict.unzip (24, 25))
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
         (* 6: allv + + *)
         6: unit list StringSplayDict.dict Exp.Dict.dict,
         (* 7: allvSpine + + *)
         7: unit list StringSplayDict.dict Spine.Dict.dict,
         (* 8: allv + - *)
         8: String.string list Exp.Dict.dict,
         (* 9: allvSpine + - *)
         9: String.string list Spine.Dict.dict,
         (* 10: givenMode + + *)
         10: unit list Mode.Dict.dict Exp.Dict.dict,
         (* 11: varMode + + *)
         11: unit list Mode.Dict.dict StringSplayDict.dict,
         (* 12: fvPos + + *)
         12: unit list StringSplayDict.dict PosProp.Dict.dict,
         (* 13: fvNeg + + *)
         13: unit list StringSplayDict.dict NegProp.Dict.dict,
         (* 14: fvPos + - *)
         14: String.string list PosProp.Dict.dict,
         (* 15: fvNeg + - *)
         15: String.string list NegProp.Dict.dict,
         (* 16: allvPos + + *)
         16: unit list StringSplayDict.dict PosProp.Dict.dict,
         (* 17: allvNeg + + *)
         17: unit list StringSplayDict.dict NegProp.Dict.dict,
         (* 18: allvPos + - *)
         18: String.string list PosProp.Dict.dict,
         (* 19: allvNeg + - *)
         19: String.string list NegProp.Dict.dict,
         (* 20: subPos + + *)
         20: unit list AProp.Dict.dict PosProp.Dict.dict,
         (* 21: subNeg + + *)
         21: unit list AProp.Dict.dict NegProp.Dict.dict,
         (* 22: endPos + + *)
         22: unit list PosProp.Dict.dict PosProp.Dict.dict,
         (* 23: subgoal + + *)
         23: unit list PosProp.Dict.dict NegProp.Dict.dict,
         (* 24: endNeg + + *)
         24: unit list NegProp.Dict.dict NegProp.Dict.dict,
         (* 25: endNeg + - *)
         25: NegProp.t list NegProp.Dict.dict,
         (* 26: headPos + + *)
         26: unit list Head.Dict.dict PosProp.Dict.dict,
         (* 27: headNeg + + *)
         27: unit list Head.Dict.dict NegProp.Dict.dict,
         (* 28: signat + + + *)
         28: unit list Exp.Dict.dict Exp.Dict.dict SymbolSplayDict.dict,
         (* 29: rules + + *)
         29: unit list NegProp.Dict.dict SymbolSplayDict.dict,
         (* 30: signat + - - *)
         30: (Exp.t * Exp.t) list SymbolSplayDict.dict,
         (* 31: rules + - *)
         31: NegProp.t list SymbolSplayDict.dict,
         (* 32: classify + + *)
         32: unit list Exp.Dict.dict SymbolSplayDict.dict,
         (* 33: classify + - *)
         33: Exp.t list SymbolSplayDict.dict,
         (* 34: ruleSubord + + *)
         34: unit list Head.Dict.dict Head.Dict.dict,
         (* 35: semanticEffects *)
         35: unit list ,
         (* 36: weaklySemanticEffects *)
         36: unit list ,
         (* 37: notSemanticEffects *)
         37: unit list ,
         (* 38: rules - - *)
         38: (Symbol.symbol * NegProp.t) list ,
         (* 39: subNeg + (neg (lefti - -)) *)
         39: (PosProp.t * NegProp.t) list NegProp.Dict.dict,
         (* 40: headPos + - *)
         40: Head.t list PosProp.Dict.dict,
         (* 41: headNeg + - *)
         41: Head.t list NegProp.Dict.dict,
         (* 42: subNeg + (neg (righti - -)) *)
         42: (PosProp.t * NegProp.t) list NegProp.Dict.dict,
         (* 43: ruleSubord - - *)
         43: (Head.t * Head.t) list ,
         (* 44: ruleSubord + - *)
         44: Head.t list Head.Dict.dict,
         (* 45: signat - - - *)
         45: (Symbol.symbol * Exp.t * Exp.t) list ,
         (* 46: headClass + - *)
         46: Exp.t list Exp.Dict.dict,
         (* 47: subPos + - *)
         47: AProp.t list PosProp.Dict.dict,
         (* 48: subNeg + - *)
         48: AProp.t list NegProp.Dict.dict,
         (* 49: endPos + - *)
         49: PosProp.t list PosProp.Dict.dict,
         (* 50: subgoal + - *)
         50: PosProp.t list NegProp.Dict.dict,
         (* 51: endNeg + (lax -) *)
         51: PosProp.t list NegProp.Dict.dict,
         (* 52: endNeg + (nAtom - -) *)
         52: (Symbol.symbol * Spine.t) list NegProp.Dict.dict,
         (* 53: endPos + (down - -) *)
         53: (Perm.t * NegProp.t) list PosProp.Dict.dict,
         (* 54: givenMode - - *)
         54: (Exp.t * Mode.t) list ,
         (* 55: ruleSubord monadic - *)
         55: Head.t list ,
         (* 56: ruleSubord monadic monadic *)
         56: unit list ,
         worlds: unit World.Dict.dict}
      
      fun empty (): tables = {
         1=Exp.Dict.empty,
         2=Exp.Dict.empty,
         3=Spine.Dict.empty,
         4=Exp.Dict.empty,
         5=Spine.Dict.empty,
         6=Exp.Dict.empty,
         7=Spine.Dict.empty,
         8=Exp.Dict.empty,
         9=Spine.Dict.empty,
         10=Exp.Dict.empty,
         11=StringSplayDict.empty,
         12=PosProp.Dict.empty,
         13=NegProp.Dict.empty,
         14=PosProp.Dict.empty,
         15=NegProp.Dict.empty,
         16=PosProp.Dict.empty,
         17=NegProp.Dict.empty,
         18=PosProp.Dict.empty,
         19=NegProp.Dict.empty,
         20=PosProp.Dict.empty,
         21=NegProp.Dict.empty,
         22=PosProp.Dict.empty,
         23=NegProp.Dict.empty,
         24=NegProp.Dict.empty,
         25=NegProp.Dict.empty,
         26=PosProp.Dict.empty,
         27=NegProp.Dict.empty,
         28=SymbolSplayDict.empty,
         29=SymbolSplayDict.empty,
         30=SymbolSplayDict.empty,
         31=SymbolSplayDict.empty,
         32=SymbolSplayDict.empty,
         33=SymbolSplayDict.empty,
         34=Head.Dict.empty,
         35=[],
         36=[],
         37=[],
         38=[],
         39=NegProp.Dict.empty,
         40=PosProp.Dict.empty,
         41=NegProp.Dict.empty,
         42=NegProp.Dict.empty,
         43=[],
         44=Head.Dict.empty,
         45=[],
         46=Exp.Dict.empty,
         47=PosProp.Dict.empty,
         48=NegProp.Dict.empty,
         49=PosProp.Dict.empty,
         50=NegProp.Dict.empty,
         51=NegProp.Dict.empty,
         52=NegProp.Dict.empty,
         53=PosProp.Dict.empty,
         54=[],
         55=[],
         56=[],
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
      fun get_49 (db: tables) = #49 db
      fun get_50 (db: tables) = #50 db
      fun get_51 (db: tables) = #51 db
      fun get_52 (db: tables) = #52 db
      fun get_53 (db: tables) = #53 db
      fun get_54 (db: tables) = #54 db
      fun get_55 (db: tables) = #55 db
      fun get_56 (db: tables) = #56 db
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_49 (db: tables) x = {
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
            49 = x,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_50 (db: tables) x = {
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
            49 = #49 db,
            50 = x,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_51 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = x,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_52 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = x,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_53 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = x,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_54 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = x,
            55 = #55 db,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_55 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = x,
            56 = #56 db,
            worlds = #worlds db}
      
      fun set_56 (db: tables) x = {
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = x,
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
            49 = #49 db,
            50 = #50 db,
            51 = #51 db,
            52 = #52 db,
            53 = #53 db,
            54 = #54 db,
            55 = #55 db,
            56 = #56 db,
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
            (mapPartial StringSplayDict.find x_1
             (Exp.Dict.find dict x_0))
      
      fun fold_7 f x (db as {7= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (Spine.Dict.find dict x_0))
      
      fun fold_8 f x (db as {8= dict, ...}: tables) x_0 =
         fold f x
            (Exp.Dict.find dict x_0)
      
      fun fold_9 f x (db as {9= dict, ...}: tables) x_0 =
         fold f x
            (Spine.Dict.find dict x_0)
      
      fun fold_10 f x (db as {10= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Mode.Dict.find x_1
             (Exp.Dict.find dict x_0))
      
      fun fold_11 f x (db as {11= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Mode.Dict.find x_1
             (StringSplayDict.find dict x_0))
      
      fun fold_12 f x (db as {12= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_13 f x (db as {13= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_14 f x (db as {14= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_15 f x (db as {15= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_16 f x (db as {16= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_17 f x (db as {17= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial StringSplayDict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_18 f x (db as {18= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_19 f x (db as {19= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_20 f x (db as {20= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial AProp.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_21 f x (db as {21= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial AProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_22 f x (db as {22= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial PosProp.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_23 f x (db as {23= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial PosProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_24 f x (db as {24= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial NegProp.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_25 f x (db as {25= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_26 f x (db as {26= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (PosProp.Dict.find dict x_0))
      
      fun fold_27 f x (db as {27= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (NegProp.Dict.find dict x_0))
      
      fun fold_28 f x (db as {28= dict, ...}: tables) (x_0, x_1, x_2) =
         fold f x
            (mapPartial Exp.Dict.find x_2
             (mapPartial Exp.Dict.find x_1
              (SymbolSplayDict.find dict x_0)))
      
      fun fold_29 f x (db as {29= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial NegProp.Dict.find x_1
             (SymbolSplayDict.find dict x_0))
      
      fun fold_30 f x (db as {30= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_31 f x (db as {31= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_32 f x (db as {32= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Exp.Dict.find x_1
             (SymbolSplayDict.find dict x_0))
      
      fun fold_33 f x (db as {33= dict, ...}: tables) x_0 =
         fold f x
            (SymbolSplayDict.find dict x_0)
      
      fun fold_34 f x (db as {34= dict, ...}: tables) (x_0, x_1) =
         fold f x
            (mapPartial Head.Dict.find x_1
             (Head.Dict.find dict x_0))
      
      fun fold_35 f x (db as {35= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_36 f x (db as {36= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_37 f x (db as {37= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_38 f x (db as {38= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_39 f x (db as {39= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_40 f x (db as {40= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_41 f x (db as {41= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_42 f x (db as {42= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_43 f x (db as {43= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_44 f x (db as {44= dict, ...}: tables) x_0 =
         fold f x
            (Head.Dict.find dict x_0)
      
      fun fold_45 f x (db as {45= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_46 f x (db as {46= dict, ...}: tables) x_0 =
         fold f x
            (Exp.Dict.find dict x_0)
      
      fun fold_47 f x (db as {47= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_48 f x (db as {48= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_49 f x (db as {49= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_50 f x (db as {50= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_51 f x (db as {51= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_52 f x (db as {52= dict, ...}: tables) x_0 =
         fold f x
            (NegProp.Dict.find dict x_0)
      
      fun fold_53 f x (db as {53= dict, ...}: tables) x_0 =
         fold f x
            (PosProp.Dict.find dict x_0)
      
      fun fold_54 f x (db as {54= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_55 f x (db as {55= dict, ...}: tables) () =
         List.foldr f x dict
      
      fun fold_56 f x (db as {56= dict, ...}: tables) () =
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
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_6 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_7 (x_0, x_1) data (db: tables) =
      let
         val this =get_7 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_7 db
            (Spine.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_8 x_0 data (db: tables) =
      let
         val this =get_8 db
         val single_0 = [data]
      in
         set_8 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_9 x_0 data (db: tables) =
      let
         val this =get_9 db
         val single_0 = [data]
      in
         set_9 db
            (Spine.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_10 (x_0, x_1) data (db: tables) =
      let
         val this =get_10 db
         val single_1 = [data]
         val single_0 = Mode.Dict.singleton x_1 single_1
      in
         set_10 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Mode.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_11 (x_0, x_1) data (db: tables) =
      let
         val this =get_11 db
         val single_1 = [data]
         val single_0 = Mode.Dict.singleton x_1 single_1
      in
         set_11 db
            (StringSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Mode.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_12 (x_0, x_1) data (db: tables) =
      let
         val this =get_12 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_12 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_13 (x_0, x_1) data (db: tables) =
      let
         val this =get_13 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_13 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_14 x_0 data (db: tables) =
      let
         val this =get_14 db
         val single_0 = [data]
      in
         set_14 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_15 x_0 data (db: tables) =
      let
         val this =get_15 db
         val single_0 = [data]
      in
         set_15 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_16 (x_0, x_1) data (db: tables) =
      let
         val this =get_16 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_16 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_17 (x_0, x_1) data (db: tables) =
      let
         val this =get_17 db
         val single_1 = [data]
         val single_0 = StringSplayDict.singleton x_1 single_1
      in
         set_17 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (StringSplayDict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_18 x_0 data (db: tables) =
      let
         val this =get_18 db
         val single_0 = [data]
      in
         set_18 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_19 x_0 data (db: tables) =
      let
         val this =get_19 db
         val single_0 = [data]
      in
         set_19 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_20 (x_0, x_1) data (db: tables) =
      let
         val this =get_20 db
         val single_1 = [data]
         val single_0 = AProp.Dict.singleton x_1 single_1
      in
         set_20 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (AProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_21 (x_0, x_1) data (db: tables) =
      let
         val this =get_21 db
         val single_1 = [data]
         val single_0 = AProp.Dict.singleton x_1 single_1
      in
         set_21 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (AProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_22 (x_0, x_1) data (db: tables) =
      let
         val this =get_22 db
         val single_1 = [data]
         val single_0 = PosProp.Dict.singleton x_1 single_1
      in
         set_22 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (PosProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_23 (x_0, x_1) data (db: tables) =
      let
         val this =get_23 db
         val single_1 = [data]
         val single_0 = PosProp.Dict.singleton x_1 single_1
      in
         set_23 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (PosProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_24 (x_0, x_1) data (db: tables) =
      let
         val this =get_24 db
         val single_1 = [data]
         val single_0 = NegProp.Dict.singleton x_1 single_1
      in
         set_24 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (NegProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_25 x_0 data (db: tables) =
      let
         val this =get_25 db
         val single_0 = [data]
      in
         set_25 db
            (NegProp.Dict.insertMerge this x_0 single_0
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
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_27 (x_0, x_1) data (db: tables) =
      let
         val this =get_27 db
         val single_1 = [data]
         val single_0 = Head.Dict.singleton x_1 single_1
      in
         set_27 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_28 (x_0, x_1, x_2) data (db: tables) =
      let
         val this =get_28 db
         val single_2 = [data]
         val single_1 = Exp.Dict.singleton x_2 single_2
         val single_0 = Exp.Dict.singleton x_1 single_1
      in
         set_28 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Exp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (Exp.Dict.insertMerge this x_2 single_2
                 (fn this =>
                  (data :: this)))))))
      end
      
      fun ins_29 (x_0, x_1) data (db: tables) =
      let
         val this =get_29 db
         val single_1 = [data]
         val single_0 = NegProp.Dict.singleton x_1 single_1
      in
         set_29 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (NegProp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_30 x_0 data (db: tables) =
      let
         val this =get_30 db
         val single_0 = [data]
      in
         set_30 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_31 x_0 data (db: tables) =
      let
         val this =get_31 db
         val single_0 = [data]
      in
         set_31 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_32 (x_0, x_1) data (db: tables) =
      let
         val this =get_32 db
         val single_1 = [data]
         val single_0 = Exp.Dict.singleton x_1 single_1
      in
         set_32 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (Exp.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_33 x_0 data (db: tables) =
      let
         val this =get_33 db
         val single_0 = [data]
      in
         set_33 db
            (SymbolSplayDict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_34 (x_0, x_1) data (db: tables) =
      let
         val this =get_34 db
         val single_1 = [data]
         val single_0 = Head.Dict.singleton x_1 single_1
      in
         set_34 db
            (Head.Dict.insertMerge this x_0 single_0
             (fn this =>
              (Head.Dict.insertMerge this x_1 single_1
               (fn this =>
                (data :: this)))))
      end
      
      fun ins_35 data (db: tables) =
      let
         val this =get_35 db
      in
         set_35 db
            (data :: this)
      end
      
      fun ins_36 data (db: tables) =
      let
         val this =get_36 db
      in
         set_36 db
            (data :: this)
      end
      
      fun ins_37 data (db: tables) =
      let
         val this =get_37 db
      in
         set_37 db
            (data :: this)
      end
      
      fun ins_38 data (db: tables) =
      let
         val this =get_38 db
      in
         set_38 db
            (data :: this)
      end
      
      fun ins_39 x_0 data (db: tables) =
      let
         val this =get_39 db
         val single_0 = [data]
      in
         set_39 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_40 x_0 data (db: tables) =
      let
         val this =get_40 db
         val single_0 = [data]
      in
         set_40 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_41 x_0 data (db: tables) =
      let
         val this =get_41 db
         val single_0 = [data]
      in
         set_41 db
            (NegProp.Dict.insertMerge this x_0 single_0
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
      
      fun ins_43 data (db: tables) =
      let
         val this =get_43 db
      in
         set_43 db
            (data :: this)
      end
      
      fun ins_44 x_0 data (db: tables) =
      let
         val this =get_44 db
         val single_0 = [data]
      in
         set_44 db
            (Head.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_45 data (db: tables) =
      let
         val this =get_45 db
      in
         set_45 db
            (data :: this)
      end
      
      fun ins_46 x_0 data (db: tables) =
      let
         val this =get_46 db
         val single_0 = [data]
      in
         set_46 db
            (Exp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_47 x_0 data (db: tables) =
      let
         val this =get_47 db
         val single_0 = [data]
      in
         set_47 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_48 x_0 data (db: tables) =
      let
         val this =get_48 db
         val single_0 = [data]
      in
         set_48 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_49 x_0 data (db: tables) =
      let
         val this =get_49 db
         val single_0 = [data]
      in
         set_49 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_50 x_0 data (db: tables) =
      let
         val this =get_50 db
         val single_0 = [data]
      in
         set_50 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_51 x_0 data (db: tables) =
      let
         val this =get_51 db
         val single_0 = [data]
      in
         set_51 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_52 x_0 data (db: tables) =
      let
         val this =get_52 db
         val single_0 = [data]
      in
         set_52 db
            (NegProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_53 x_0 data (db: tables) =
      let
         val this =get_53 db
         val single_0 = [data]
      in
         set_53 db
            (PosProp.Dict.insertMerge this x_0 single_0
             (fn this =>
              (data :: this)))
      end
      
      fun ins_54 data (db: tables) =
      let
         val this =get_54 db
      in
         set_54 db
            (data :: this)
      end
      
      fun ins_55 data (db: tables) =
      let
         val this =get_55 db
      in
         set_55 db
            (data :: this)
      end
      
      fun ins_56 data (db: tables) =
      let
         val this =get_56 db
      in
         set_56 db
            (data :: this)
      end
      
      fun insert_headClass (x_0, x_1) db =
         (* headClass x_0 x_1 *)
         (ins_1 (x_0, x_1) ()
          (ins_46 x_0 x_1 db))
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
      
      fun insert_allv (x_0, x_1) db =
         (* allv x_0 x_1 *)
         (ins_6 (x_0, x_1) ()
          (ins_8 x_0 x_1 db))
      fun assert_allv (x_0, x_1) (flag, db) =
         if fold_6 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_allv (x_0, x_1) db)
      
      fun insert_allvSpine (x_0, x_1) db =
         (* allvSpine x_0 x_1 *)
         (ins_7 (x_0, x_1) ()
          (ins_9 x_0 x_1 db))
      fun assert_allvSpine (x_0, x_1) (flag, db) =
         if fold_7 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_allvSpine (x_0, x_1) db)
      
      fun insert_givenMode (x_0, x_1) db =
         (* givenMode x_0 x_1 *)
         (ins_10 (x_0, x_1) ()
          (ins_54 (x_0, x_1) db))
      fun assert_givenMode (x_0, x_1) (flag, db) =
         if fold_10 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_givenMode (x_0, x_1) db)
      
      fun insert_varMode (x_0, x_1) db =
         (* varMode x_0 x_1 *)
         (ins_11 (x_0, x_1) () db)
      fun assert_varMode (x_0, x_1) (flag, db) =
         if fold_11 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_varMode (x_0, x_1) db)
      
      fun insert_fvPos (x_0, x_1) db =
         (* fvPos x_0 x_1 *)
         (ins_12 (x_0, x_1) ()
          (ins_14 x_0 x_1 db))
      fun assert_fvPos (x_0, x_1) (flag, db) =
         if fold_12 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fvPos (x_0, x_1) db)
      
      fun insert_fvNeg (x_0, x_1) db =
         (* fvNeg x_0 x_1 *)
         (ins_13 (x_0, x_1) ()
          (ins_15 x_0 x_1 db))
      fun assert_fvNeg (x_0, x_1) (flag, db) =
         if fold_13 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_fvNeg (x_0, x_1) db)
      
      fun insert_allvPos (x_0, x_1) db =
         (* allvPos x_0 x_1 *)
         (ins_16 (x_0, x_1) ()
          (ins_18 x_0 x_1 db))
      fun assert_allvPos (x_0, x_1) (flag, db) =
         if fold_16 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_allvPos (x_0, x_1) db)
      
      fun insert_allvNeg (x_0, x_1) db =
         (* allvNeg x_0 x_1 *)
         (ins_17 (x_0, x_1) ()
          (ins_19 x_0 x_1 db))
      fun assert_allvNeg (x_0, x_1) (flag, db) =
         if fold_17 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_allvNeg (x_0, x_1) db)
      
      fun insert_subPos (x_0, x_1) db =
         (* subPos x_0 x_1 *)
         (ins_20 (x_0, x_1) ()
          (ins_47 x_0 x_1 db))
      fun assert_subPos (x_0, x_1) (flag, db) =
         if fold_20 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subPos (x_0, x_1) db)
      
      fun insert_subNeg (x_0, x_1) db =
        (case x_1 of 
            AProp.Neg x_1_0 =>
              (case x_1_0 of 
                  NegProp.Lefti (x_1_0_0, x_1_0_1) =>
                     (* subNeg x_0 (neg (lefti x_1_0_0 x_1_0_1)) *)
                     (ins_21 (x_0, x_1) ()
                      (ins_39 x_0 (x_1_0_0, x_1_0_1)
                       (ins_48 x_0 x_1 db)))
                | NegProp.Righti (x_1_0_0, x_1_0_1) =>
                     (* subNeg x_0 (neg (righti x_1_0_0 x_1_0_1)) *)
                     (ins_21 (x_0, x_1) ()
                      (ins_42 x_0 (x_1_0_0, x_1_0_1)
                       (ins_48 x_0 x_1 db)))
                | _ =>
                     (* subNeg x_0 (neg x_1_0) *)
                     (ins_21 (x_0, x_1) ()
                      (ins_48 x_0 x_1 db)))
          | _ =>
               (* subNeg x_0 x_1 *)
               (ins_21 (x_0, x_1) ()
                (ins_48 x_0 x_1 db)))
      fun assert_subNeg (x_0, x_1) (flag, db) =
         if fold_21 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subNeg (x_0, x_1) db)
      
      fun insert_endPos (x_0, x_1) db =
        (case x_1 of 
            PosProp.Down (x_1_0, x_1_1) =>
               (* endPos x_0 (down x_1_0 x_1_1) *)
               (ins_22 (x_0, x_1) ()
                (ins_49 x_0 x_1
                 (ins_53 x_0 (x_1_0, x_1_1) db)))
          | _ =>
               (* endPos x_0 x_1 *)
               (ins_22 (x_0, x_1) ()
                (ins_49 x_0 x_1 db)))
      fun assert_endPos (x_0, x_1) (flag, db) =
         if fold_22 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_endPos (x_0, x_1) db)
      
      fun insert_subgoal (x_0, x_1) db =
         (* subgoal x_0 x_1 *)
         (ins_23 (x_0, x_1) ()
          (ins_50 x_0 x_1 db))
      fun assert_subgoal (x_0, x_1) (flag, db) =
         if fold_23 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_subgoal (x_0, x_1) db)
      
      fun insert_endNeg (x_0, x_1) db =
        (case x_1 of 
            NegProp.NAtom (x_1_0, x_1_1) =>
               (* endNeg x_0 (nAtom x_1_0 x_1_1) *)
               (ins_24 (x_0, x_1) ()
                (ins_25 x_0 x_1
                 (ins_52 x_0 (x_1_0, x_1_1) db)))
          | NegProp.Lax x_1_0 =>
               (* endNeg x_0 (lax x_1_0) *)
               (ins_24 (x_0, x_1) ()
                (ins_25 x_0 x_1
                 (ins_51 x_0 x_1_0 db)))
          | _ =>
               (* endNeg x_0 x_1 *)
               (ins_24 (x_0, x_1) ()
                (ins_25 x_0 x_1 db)))
      fun assert_endNeg (x_0, x_1) (flag, db) =
         if fold_24 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_endNeg (x_0, x_1) db)
      
      fun insert_headPos (x_0, x_1) db =
         (* headPos x_0 x_1 *)
         (ins_26 (x_0, x_1) ()
          (ins_40 x_0 x_1 db))
      fun assert_headPos (x_0, x_1) (flag, db) =
         if fold_26 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_headPos (x_0, x_1) db)
      
      fun insert_headNeg (x_0, x_1) db =
         (* headNeg x_0 x_1 *)
         (ins_27 (x_0, x_1) ()
          (ins_41 x_0 x_1 db))
      fun assert_headNeg (x_0, x_1) (flag, db) =
         if fold_27 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_headNeg (x_0, x_1) db)
      
      fun insert_signat (x_0, x_1, x_2) db =
         (* signat x_0 x_1 x_2 *)
         (ins_28 (x_0, x_1, x_2) ()
          (ins_30 x_0 (x_1, x_2)
           (ins_45 (x_0, x_1, x_2) db)))
      fun assert_signat (x_0, x_1, x_2) (flag, db) =
         if fold_28 (fn _ => true) false db (x_0, x_1, x_2)
         then (flag, db)
         else (true, insert_signat (x_0, x_1, x_2) db)
      
      fun insert_rules (x_0, x_1) db =
         (* rules x_0 x_1 *)
         (ins_29 (x_0, x_1) ()
          (ins_31 x_0 x_1
           (ins_38 (x_0, x_1) db)))
      fun assert_rules (x_0, x_1) (flag, db) =
         if fold_29 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_rules (x_0, x_1) db)
      
      fun insert_classify (x_0, x_1) db =
         (* classify x_0 x_1 *)
         (ins_32 (x_0, x_1) ()
          (ins_33 x_0 x_1 db))
      fun assert_classify (x_0, x_1) (flag, db) =
         if fold_32 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_classify (x_0, x_1) db)
      
      fun insert_ruleSubord (x_0, x_1) db =
        (case x_0 of 
            Head.Monadic =>
              (case x_1 of 
                  Head.Monadic =>
                     (* ruleSubord monadic monadic *)
                     (ins_34 (x_0, x_1) ()
                      (ins_43 (x_0, x_1)
                       (ins_44 x_0 x_1
                        (ins_55 x_1
                         (ins_56 () db)))))
                | _ =>
                     (* ruleSubord monadic x_1 *)
                     (ins_34 (x_0, x_1) ()
                      (ins_43 (x_0, x_1)
                       (ins_44 x_0 x_1
                        (ins_55 x_1 db)))))
          | _ =>
              (case x_1 of 
                  Head.Monadic =>
                     (* ruleSubord x_0 monadic *)
                     (ins_34 (x_0, x_1) ()
                      (ins_43 (x_0, x_1)
                       (ins_44 x_0 x_1 db)))
                | _ =>
                     (* ruleSubord x_0 x_1 *)
                     (ins_34 (x_0, x_1) ()
                      (ins_43 (x_0, x_1)
                       (ins_44 x_0 x_1 db)))))
      fun assert_ruleSubord (x_0, x_1) (flag, db) =
         if fold_34 (fn _ => true) false db (x_0, x_1)
         then (flag, db)
         else (true, insert_ruleSubord (x_0, x_1) db)
      
      fun insert_semanticEffects () db =
         (* semanticEffects *)
         (ins_35 () db)
      fun assert_semanticEffects () (flag, db) =
         if fold_35 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_semanticEffects () db)
      
      fun insert_weaklySemanticEffects () db =
         (* weaklySemanticEffects *)
         (ins_36 () db)
      fun assert_weaklySemanticEffects () (flag, db) =
         if fold_36 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_weaklySemanticEffects () db)
      
      fun insert_notSemanticEffects () db =
         (* notSemanticEffects *)
         (ins_37 () db)
      fun assert_notSemanticEffects () (flag, db) =
         if fold_37 (fn _ => true) false db ()
         then (flag, db)
         else (true, insert_notSemanticEffects () db)
      
   end
   
   
   (* L10 immediate consequences (rules.sml) *)
   
   structure L10_Consequence =
   struct
   
      (* Rule at syntax.l10:293.1-293.50 *)
      
      (* assert -- notSemanticEffects *)
      fun exec_123_1 () satu db =
         (L10_Tables.assert_notSemanticEffects () db)
      (* ruleSubord monadic monadic - syntax.l10:293.1-293.27 *)
      fun exec_123 () satu db =
         L10_Tables.fold_56
            (fn ((), db) => 
               exec_123_1 () satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:290.1-290.81 *)
      
      (* assert -- weaklySemanticEffects *)
      fun exec_122_2 () satu db =
         (L10_Tables.assert_weaklySemanticEffects () db)
      (* not (ruleSubord monadic monadic) - syntax.l10:290.23-290.55 *)
      fun exec_122_1 () satu db =
         if L10_Tables.fold_56
               (fn _ => true) false (#2 db) ()
         then db else exec_122_2 () satu db
      (* ruleSubord monadic _ - syntax.l10:290.1-290.21 *)
      fun exec_122 () satu db =
         L10_Tables.fold_55
            (fn (x_1, db) => 
               exec_122_1 () satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:287.1-287.47 *)
      
      (* assert -- semanticEffects *)
      fun exec_121_1 () satu db =
         (L10_Tables.assert_semanticEffects () db)
      (* not (ruleSubord monadic _) - syntax.l10:287.1-287.27 *)
      fun exec_121 () satu db =
         if L10_Tables.fold_55
               (fn _ => true) false (#2 db) ()
         then db else exec_121_1 () satu db
      
      (* Rule at syntax.l10:102.1-102.30 *)
      
      (* assert -- allv (lam X E) Y *)
      fun exec_31_1 (E, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Lam (X, E)), Y) db)
      (* allv E Y - syntax.l10:102.21-102.29 *)
      fun exec_31 (E, X) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_31_1 (E, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:101.1-101.37 *)
      
      (* assert -- allv (con _ Sp) Y *)
      fun exec_30_1 (USCORE_1, Sp, Y) satu db =
         (L10_Tables.assert_allv ((Exp.Con (USCORE_1, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:101.22-101.36 *)
      fun exec_30 (USCORE_1, Sp) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_30_1 (USCORE_1, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:100.1-100.39 *)
      
      (* assert -- allv (var X _ Sp) Y *)
      fun exec_29_1 (USCORE_1, Sp, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Var (X, USCORE_1, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:100.24-100.38 *)
      fun exec_29 (USCORE_1, Sp, X) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_29_1 (USCORE_1, Sp, x_1 (* Y *), X) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:99.1-99.21 *)
      
      (* assert -- allv (var X _ Sp) X *)
      fun exec_28 (USCORE_1, Sp, X) satu db =
         (L10_Tables.assert_allv ((Exp.Var (X, USCORE_1, Sp)), X) db)
      
      (* Rule at syntax.l10:98.1-98.35 *)
      
      (* assert -- allv (arrow E1 E2) Y *)
      fun exec_27_1 (Y, E1, E2) satu db =
         (L10_Tables.assert_allv ((Exp.Arrow (E1, E2)), Y) db)
      (* allv E2 Y - syntax.l10:98.25-98.34 *)
      fun exec_27 (E1, E2) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_27_1 (x_1 (* Y *), E1, E2) satu db)
            db (#2 db) E2
      
      (* Rule at syntax.l10:97.1-97.35 *)
      
      (* assert -- allv (arrow E1 E2) Y *)
      fun exec_26_1 (Y, E1, E2) satu db =
         (L10_Tables.assert_allv ((Exp.Arrow (E1, E2)), Y) db)
      (* allv E1 Y - syntax.l10:97.25-97.34 *)
      fun exec_26 (E1, E2) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_26_1 (x_1 (* Y *), E1, E2) satu db)
            db (#2 db) E1
      
      (* Rule at syntax.l10:96.1-96.32 *)
      
      (* assert -- allv (pii X T E) Y *)
      fun exec_25_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Pii (X, T, E)), Y) db)
      (* allv E Y - syntax.l10:96.23-96.31 *)
      fun exec_25 (E, T, X) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_25_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:95.1-95.32 *)
      
      (* assert -- allv (pii X T E) Y *)
      fun exec_24_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Pii (X, T, E)), Y) db)
      (* allv T Y - syntax.l10:95.23-95.31 *)
      fun exec_24 (E, T, X) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_24_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:94.1-94.31 *)
      
      (* assert -- allv (pi X T E) Y *)
      fun exec_23_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Pi (X, T, E)), Y) db)
      (* allv E Y - syntax.l10:94.22-94.30 *)
      fun exec_23 (E, T, X) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_23_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:93.1-93.31 *)
      
      (* assert -- allv (pi X T E) Y *)
      fun exec_22_1 (E, T, Y, X) satu db =
         (L10_Tables.assert_allv ((Exp.Pi (X, T, E)), Y) db)
      (* allv T Y - syntax.l10:93.22-93.30 *)
      fun exec_22 (E, T, X) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_22_1 (E, T, x_1 (* Y *), X) satu db)
            db (#2 db) T
      
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
         L10_Tables.fold_46
            (fn (x_1, db) => 
               exec_7_1 (E, x_1 (* Eh *), USCORE_1) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:66.1-66.44 *)
      
      (* assert -- headClass (pi _ _ E) Eh *)
      fun exec_6_1 (E, Eh, USCORE_1, USCORE_2) satu db =
         (L10_Tables.assert_headClass ((Exp.Pi (USCORE_1, USCORE_2, E)), Eh) db)
      (* headClass E Eh - syntax.l10:66.29-66.43 *)
      fun exec_6 (E, USCORE_1, USCORE_2) satu db =
         L10_Tables.fold_46
            (fn (x_1, db) => 
               exec_6_1 (E, x_1 (* Eh *), USCORE_1, USCORE_2) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:65.1-65.44 *)
      
      (* assert -- headClass (pii _ _ E) Eh *)
      fun exec_5_1 (E, Eh, USCORE_1, USCORE_2) satu db =
         (L10_Tables.assert_headClass ((Exp.Pii (USCORE_1, USCORE_2, E)), Eh) db)
      (* headClass E Eh - syntax.l10:65.29-65.43 *)
      fun exec_5 (E, USCORE_1, USCORE_2) satu db =
         L10_Tables.fold_46
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
      
      (* Rule at syntax.l10:108.1-108.43 *)
      
      (* assert -- allvSpine (appi E Sp) Y *)
      fun exec_35_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_allvSpine ((Spine.Appi (E, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:108.28-108.42 *)
      fun exec_35 (E, Sp) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_35_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:107.1-107.37 *)
      
      (* assert -- allvSpine (appi E Sp) Y *)
      fun exec_34_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_allvSpine ((Spine.Appi (E, Sp)), Y) db)
      (* allv E Y - syntax.l10:107.28-107.36 *)
      fun exec_34 (E, Sp) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_34_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) E
      
      (* Rule at syntax.l10:106.1-106.42 *)
      
      (* assert -- allvSpine (app E Sp) Y *)
      fun exec_33_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_allvSpine ((Spine.App (E, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:106.27-106.41 *)
      fun exec_33 (E, Sp) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_33_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:105.1-105.36 *)
      
      (* assert -- allvSpine (app E Sp) Y *)
      fun exec_32_1 (E, Sp, Y) satu db =
         (L10_Tables.assert_allvSpine ((Spine.App (E, Sp)), Y) db)
      (* allv E Y - syntax.l10:105.27-105.35 *)
      fun exec_32 (E, Sp) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_32_1 (E, Sp, x_1 (* Y *)) satu db)
            db (#2 db) E
      
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
      
      (* Rule at syntax.l10:122.1-122.38 *)
      
      (* assert -- varMode X M *)
      fun exec_36_3 (X, M) satu db =
         (L10_Tables.assert_varMode (X, M) db)
      (* fv E X - syntax.l10:122.16-122.22 *)
      fun exec_36_2 (E, M) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_36_3 (x_1 (* X *), M) satu db)
            db (#2 db) E
      (* Dynamic world search: wExp E *)
      fun exec_36_1 (E, M) satu (flag, db) =
         exec_36_2 (E, M) satu (flag, satu (World.WExp E) db)
      (* givenMode E M - syntax.l10:122.1-122.14 *)
      fun exec_36 () satu db =
         L10_Tables.fold_54
            (fn ((x_0, x_1), db) => 
               exec_36_1 (x_0 (* E *), x_1 (* M *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:242.1-242.51 *)
      
      (* assert -- headPos A H *)
      fun exec_116_3 (A, H) satu db =
         (L10_Tables.assert_headPos (A, H) db)
      (* headNeg A' H - syntax.l10:242.38-242.50 *)
      fun exec_116_2 (A, A') satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_116_3 (A, x_1 (* H *)) satu db)
            db (#2 db) A'
      (* Dynamic world search: wNeg A' *)
      fun exec_116_1 (A, A') satu (flag, db) =
         exec_116_2 (A, A') satu (flag, satu (World.WNeg A') db)
      (* endPos A (down _ A') - syntax.l10:242.16-242.36 *)
      fun exec_116 A satu db =
         L10_Tables.fold_53
            (fn ((x_1_0, x_1_1), db) => 
               exec_116_1 (A, x_1_1 (* A' *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:210.1-210.30 *)
      
      (* assert -- endPos (unif T S) (unif T S) *)
      fun exec_97 (T, S) satu db =
         (L10_Tables.assert_endPos ((PosProp.Unif (T, S)), (PosProp.Unif (T, S))) db)
      
      (* Rule at syntax.l10:209.1-209.39 *)
      
      (* assert -- endPos (exists _ _ A) H *)
      fun exec_96_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Exists (USCORE_1, USCORE_2, A)), H) db)
      (* endPos A H - syntax.l10:209.28-209.38 *)
      fun exec_96 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_49
            (fn (x_1, db) => 
               exec_96_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:208.1-208.35 *)
      
      (* assert -- endPos (fuse _ A) H *)
      fun exec_95_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Fuse (USCORE_1, A)), H) db)
      (* endPos A H - syntax.l10:208.24-208.34 *)
      fun exec_95 (USCORE_1, A) satu db =
         L10_Tables.fold_49
            (fn (x_1, db) => 
               exec_95_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:207.1-207.35 *)
      
      (* assert -- endPos (fuse A _) H *)
      fun exec_94_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endPos ((PosProp.Fuse (A, USCORE_1)), H) db)
      (* endPos A H - syntax.l10:207.24-207.34 *)
      fun exec_94 (USCORE_1, A) satu db =
         L10_Tables.fold_49
            (fn (x_1, db) => 
               exec_94_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:206.1-206.30 *)
      
      (* assert -- endPos (down P A) (down P A) *)
      fun exec_93 (A, P) satu db =
         (L10_Tables.assert_endPos ((PosProp.Down (P, A)), (PosProp.Down (P, A))) db)
      
      (* Rule at syntax.l10:205.1-205.38 *)
      
      (* assert -- endPos (pAtom P A Sp) (pAtom P A Sp) *)
      fun exec_92 (Sp, A, P) satu db =
         (L10_Tables.assert_endPos ((PosProp.PAtom (P, A, Sp)), (PosProp.PAtom (P, A, Sp))) db)
      
      (* Rule at syntax.l10:191.1-191.39 *)
      
      (* assert -- subPos (exists _ _ A) C *)
      fun exec_81_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Exists (USCORE_1, USCORE_2, A)), C) db)
      (* subPos A C - syntax.l10:191.28-191.38 *)
      fun exec_81 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_81_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:190.1-190.35 *)
      
      (* assert -- subPos (fuse _ A) C *)
      fun exec_80_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Fuse (USCORE_1, A)), C) db)
      (* subPos A C - syntax.l10:190.24-190.34 *)
      fun exec_80 (USCORE_1, A) satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_80_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:189.1-189.35 *)
      
      (* assert -- subPos (fuse A _) C *)
      fun exec_79_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Fuse (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:189.24-189.34 *)
      fun exec_79 (USCORE_1, A) satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_79_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:188.1-188.35 *)
      
      (* assert -- subPos (down _ A) C *)
      fun exec_78_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subPos ((PosProp.Down (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:188.24-188.34 *)
      fun exec_78 (USCORE_1, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_78_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:187.1-187.18 *)
      
      (* assert -- subPos A (pos A) *)
      fun exec_77 A satu db =
         (L10_Tables.assert_subPos (A, (AProp.Pos A)) db)
      
      (* Rule at syntax.l10:167.1-167.34 *)
      
      (* assert -- allvPos (unif T S) Y *)
      fun exec_64_1 (T, Y, S) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Unif (T, S)), Y) db)
      (* allv S Y - syntax.l10:167.25-167.33 *)
      fun exec_64 (T, S) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_64_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) S
      
      (* Rule at syntax.l10:166.1-166.34 *)
      
      (* assert -- allvPos (unif T S) Y *)
      fun exec_63_1 (T, Y, S) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Unif (T, S)), Y) db)
      (* allv T Y - syntax.l10:166.25-166.33 *)
      fun exec_63 (T, S) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_63_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:165.1-165.41 *)
      
      (* assert -- allvPos (exists X T A) Y *)
      fun exec_62_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* allvPos A Y - syntax.l10:165.29-165.40 *)
      fun exec_62 (T, X, A) satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_62_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:164.1-164.38 *)
      
      (* assert -- allvPos (exists X T A) Y *)
      fun exec_61_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* allv T Y - syntax.l10:164.29-164.37 *)
      fun exec_61 (T, X, A) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_61_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:163.1-163.37 *)
      
      (* assert -- allvPos (fuse _ A) Y *)
      fun exec_60_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Fuse (USCORE_1, A)), Y) db)
      (* allvPos A Y - syntax.l10:163.25-163.36 *)
      fun exec_60 (USCORE_1, A) satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_60_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:162.1-162.37 *)
      
      (* assert -- allvPos (fuse A _) Y *)
      fun exec_59_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Fuse (A, USCORE_1)), Y) db)
      (* allvPos A Y - syntax.l10:162.25-162.36 *)
      fun exec_59 (USCORE_1, A) satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_59_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:161.1-161.37 *)
      
      (* assert -- allvPos (down _ A) Y *)
      fun exec_58_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvPos ((PosProp.Down (USCORE_1, A)), Y) db)
      (* allvNeg A Y - syntax.l10:161.25-161.36 *)
      fun exec_58 (USCORE_1, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_58_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:160.1-160.44 *)
      
      (* assert -- allvPos (pAtom _ _ Sp) Y *)
      fun exec_57_1 (USCORE_1, USCORE_2, Sp, Y) satu db =
         (L10_Tables.assert_allvPos ((PosProp.PAtom (USCORE_1, USCORE_2, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:160.29-160.43 *)
      fun exec_57 (USCORE_1, USCORE_2, Sp) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_57_1 (USCORE_1, USCORE_2, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:140.1-140.30 *)
      
      (* assert -- fvPos (unif T S) Y *)
      fun exec_44_1 (T, Y, S) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Unif (T, S)), Y) db)
      (* fv S Y - syntax.l10:140.23-140.29 *)
      fun exec_44 (T, S) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_44_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) S
      
      (* Rule at syntax.l10:139.1-139.30 *)
      
      (* assert -- fvPos (unif T S) Y *)
      fun exec_43_1 (T, Y, S) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Unif (T, S)), Y) db)
      (* fv T Y - syntax.l10:139.23-139.29 *)
      fun exec_43 (T, S) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_43_1 (T, x_1 (* Y *), S) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:138.1-138.45 *)
      
      (* assert -- fvPos (exists X T A) Y *)
      fun exec_42_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* X != Y - syntax.l10:138.38-138.44 *)
      fun exec_42_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_42_2 (T, Y, X, A) satu db else db
      (* fvPos A Y - syntax.l10:138.27-138.36 *)
      fun exec_42 (T, X, A) satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_42_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:137.1-137.34 *)
      
      (* assert -- fvPos (exists X T A) Y *)
      fun exec_41_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Exists (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:137.27-137.33 *)
      fun exec_41 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_41_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:136.1-136.33 *)
      
      (* assert -- fvPos (fuse _ A) Y *)
      fun exec_40_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Fuse (USCORE_1, A)), Y) db)
      (* fvPos A Y - syntax.l10:136.23-136.32 *)
      fun exec_40 (USCORE_1, A) satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_40_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:135.1-135.33 *)
      
      (* assert -- fvPos (fuse A _) Y *)
      fun exec_39_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Fuse (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:135.23-135.32 *)
      fun exec_39 (USCORE_1, A) satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_39_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:134.1-134.33 *)
      
      (* assert -- fvPos (down _ A) Y *)
      fun exec_38_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvPos ((PosProp.Down (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:134.23-134.32 *)
      fun exec_38 (USCORE_1, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_38_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:133.1-133.40 *)
      
      (* assert -- fvPos (pAtom _ _ Sp) Y *)
      fun exec_37_1 (USCORE_1, USCORE_2, Sp, Y) satu db =
         (L10_Tables.assert_fvPos ((PosProp.PAtom (USCORE_1, USCORE_2, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:133.27-133.39 *)
      fun exec_37 (USCORE_1, USCORE_2, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_37_1 (USCORE_1, USCORE_2, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:241.1-241.46 *)
      
      (* assert -- headNeg A (atomic P) *)
      fun exec_115_1 (A, P) satu db =
         (L10_Tables.assert_headNeg (A, (Head.Atomic P)) db)
      (* endNeg A (nAtom P _) - syntax.l10:241.25-241.45 *)
      fun exec_115 A satu db =
         L10_Tables.fold_52
            (fn ((x_1_0, x_1_1), db) => 
               exec_115_1 (A, x_1_0 (* P *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:240.1-240.39 *)
      
      (* assert -- headNeg A monadic *)
      fun exec_114_1 A satu db =
         (L10_Tables.assert_headNeg (A, Head.Monadic) db)
      (* endNeg A (lax _) - syntax.l10:240.22-240.38 *)
      fun exec_114 A satu db =
         L10_Tables.fold_51
            (fn (x_1_0, db) => 
               exec_114_1 A satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:230.1-230.37 *)
      
      (* assert -- endNeg (alli _ _ A) H *)
      fun exec_113_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Alli (USCORE_1, USCORE_2, A)), H) db)
      (* endNeg A H - syntax.l10:230.1-230.11 *)
      fun exec_113 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_113_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:229.1-229.36 *)
      
      (* assert -- endNeg (all _ _ A) H *)
      fun exec_112_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.All (USCORE_1, USCORE_2, A)), H) db)
      (* endNeg A H - syntax.l10:229.1-229.11 *)
      fun exec_112 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_112_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:228.1-228.35 *)
      
      (* assert -- endNeg (with _ A) H *)
      fun exec_111_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.With (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:228.1-228.11 *)
      fun exec_111 (USCORE_1, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_111_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:227.1-227.35 *)
      
      (* assert -- endNeg (with A _) H *)
      fun exec_110_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.With (A, USCORE_1)), H) db)
      (* endNeg A H - syntax.l10:227.1-227.11 *)
      fun exec_110 (USCORE_1, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_110_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:226.1-226.37 *)
      
      (* assert -- endNeg (righti _ A) H *)
      fun exec_109_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Righti (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:226.1-226.11 *)
      fun exec_109 (USCORE_1, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_109_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:225.1-225.36 *)
      
      (* assert -- endNeg (lefti _ A) H *)
      fun exec_108_1 (USCORE_1, A, H) satu db =
         (L10_Tables.assert_endNeg ((NegProp.Lefti (USCORE_1, A)), H) db)
      (* endNeg A H - syntax.l10:225.1-225.11 *)
      fun exec_108 (USCORE_1, A) satu db =
         L10_Tables.fold_25
            (fn (x_1, db) => 
               exec_108_1 (USCORE_1, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:224.1-224.24 *)
      
      (* assert -- endNeg (lax A) (lax A) *)
      fun exec_107 A satu db =
         (L10_Tables.assert_endNeg ((NegProp.Lax A), (NegProp.Lax A)) db)
      
      (* Rule at syntax.l10:223.1-223.34 *)
      
      (* assert -- endNeg (nAtom A Sp) (nAtom A Sp) *)
      fun exec_106 (Sp, A) satu db =
         (L10_Tables.assert_endNeg ((NegProp.NAtom (A, Sp)), (NegProp.NAtom (A, Sp))) db)
      
      (* Rule at syntax.l10:220.1-220.39 *)
      
      (* assert -- subgoal (alli _ _ A) H *)
      fun exec_105_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Alli (USCORE_1, USCORE_2, A)), H) db)
      (* subgoal A H - syntax.l10:220.27-220.38 *)
      fun exec_105 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_105_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:219.1-219.38 *)
      
      (* assert -- subgoal (all _ _ A) H *)
      fun exec_104_1 (USCORE_1, USCORE_2, A, H) satu db =
         (L10_Tables.assert_subgoal ((NegProp.All (USCORE_1, USCORE_2, A)), H) db)
      (* subgoal A H - syntax.l10:219.26-219.37 *)
      fun exec_104 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_104_1 (USCORE_1, USCORE_2, A, x_1 (* H *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:218.1-218.37 *)
      
      (* assert -- subgoal (with A B) H *)
      fun exec_103_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.With (A, B)), H) db)
      (* subgoal B H - syntax.l10:218.25-218.36 *)
      fun exec_103 (A, B) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_103_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:217.1-217.37 *)
      
      (* assert -- subgoal (with A B) H *)
      fun exec_102_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.With (A, B)), H) db)
      (* subgoal A H - syntax.l10:217.25-217.36 *)
      fun exec_102 (A, B) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_102_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:216.1-216.39 *)
      
      (* assert -- subgoal (righti A B) H *)
      fun exec_101_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Righti (A, B)), H) db)
      (* subgoal B H - syntax.l10:216.27-216.38 *)
      fun exec_101 (A, B) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_101_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:215.1-215.38 *)
      
      (* assert -- subgoal (righti A B) H *)
      fun exec_100_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Righti (A, B)), H) db)
      (* endPos A H - syntax.l10:215.27-215.37 *)
      fun exec_100 (A, B) satu db =
         L10_Tables.fold_49
            (fn (x_1, db) => 
               exec_100_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:214.1-214.38 *)
      
      (* assert -- subgoal (lefti A B) H *)
      fun exec_99_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Lefti (A, B)), H) db)
      (* subgoal B H - syntax.l10:214.26-214.37 *)
      fun exec_99 (A, B) satu db =
         L10_Tables.fold_50
            (fn (x_1, db) => 
               exec_99_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) B
      
      (* Rule at syntax.l10:213.1-213.37 *)
      
      (* assert -- subgoal (lefti A B) H *)
      fun exec_98_1 (A, H, B) satu db =
         (L10_Tables.assert_subgoal ((NegProp.Lefti (A, B)), H) db)
      (* endPos A H - syntax.l10:213.26-213.36 *)
      fun exec_98 (A, B) satu db =
         L10_Tables.fold_49
            (fn (x_1, db) => 
               exec_98_1 (A, x_1 (* H *), B) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:202.1-202.37 *)
      
      (* assert -- subNeg (alli _ _ A) C *)
      fun exec_91_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Alli (USCORE_1, USCORE_2, A)), C) db)
      (* subNeg A C - syntax.l10:202.26-202.36 *)
      fun exec_91 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_91_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:201.1-201.36 *)
      
      (* assert -- subNeg (all _ _ A) C *)
      fun exec_90_1 (USCORE_1, USCORE_2, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.All (USCORE_1, USCORE_2, A)), C) db)
      (* subNeg A C - syntax.l10:201.25-201.35 *)
      fun exec_90 (USCORE_1, USCORE_2, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_90_1 (USCORE_1, USCORE_2, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:200.1-200.35 *)
      
      (* assert -- subNeg (with _ A) C *)
      fun exec_89_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.With (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:200.24-200.34 *)
      fun exec_89 (USCORE_1, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_89_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:199.1-199.35 *)
      
      (* assert -- subNeg (with A _) C *)
      fun exec_88_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.With (A, USCORE_1)), C) db)
      (* subNeg A C - syntax.l10:199.24-199.34 *)
      fun exec_88 (USCORE_1, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_88_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:198.1-198.37 *)
      
      (* assert -- subNeg (righti _ A) C *)
      fun exec_87_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Righti (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:198.26-198.36 *)
      fun exec_87 (USCORE_1, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_87_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:197.1-197.37 *)
      
      (* assert -- subNeg (righti A _) C *)
      fun exec_86_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Righti (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:197.26-197.36 *)
      fun exec_86 (USCORE_1, A) satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_86_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:196.1-196.36 *)
      
      (* assert -- subNeg (lefti _ A) C *)
      fun exec_85_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lefti (USCORE_1, A)), C) db)
      (* subNeg A C - syntax.l10:196.25-196.35 *)
      fun exec_85 (USCORE_1, A) satu db =
         L10_Tables.fold_48
            (fn (x_1, db) => 
               exec_85_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:195.1-195.36 *)
      
      (* assert -- subNeg (lefti A _) C *)
      fun exec_84_1 (USCORE_1, A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lefti (A, USCORE_1)), C) db)
      (* subPos A C - syntax.l10:195.25-195.35 *)
      fun exec_84 (USCORE_1, A) satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_84_1 (USCORE_1, A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:194.1-194.32 *)
      
      (* assert -- subNeg (lax A) C *)
      fun exec_83_1 (A, C) satu db =
         (L10_Tables.assert_subNeg ((NegProp.Lax A), C) db)
      (* subPos A C - syntax.l10:194.21-194.31 *)
      fun exec_83 A satu db =
         L10_Tables.fold_47
            (fn (x_1, db) => 
               exec_83_1 (A, x_1 (* C *)) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:193.1-193.18 *)
      
      (* assert -- subNeg A (neg A) *)
      fun exec_82 A satu db =
         (L10_Tables.assert_subNeg (A, (AProp.Neg A)) db)
      
      (* Rule at syntax.l10:181.1-181.39 *)
      
      (* assert -- allvNeg (alli X T A) Y *)
      fun exec_76_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* allvNeg A Y - syntax.l10:181.27-181.38 *)
      fun exec_76 (T, X, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_76_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:180.1-180.36 *)
      
      (* assert -- allvNeg (alli X T A) Y *)
      fun exec_75_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* allv T Y - syntax.l10:180.27-180.35 *)
      fun exec_75 (T, X, A) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_75_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:179.1-179.38 *)
      
      (* assert -- allvNeg (all X T A) Y *)
      fun exec_74_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.All (X, T, A)), Y) db)
      (* allvNeg A Y - syntax.l10:179.26-179.37 *)
      fun exec_74 (T, X, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_74_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:178.1-178.35 *)
      
      (* assert -- allvNeg (all X T A) Y *)
      fun exec_73_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.All (X, T, A)), Y) db)
      (* allv T Y - syntax.l10:178.26-178.34 *)
      fun exec_73 (T, X, A) satu db =
         L10_Tables.fold_8
            (fn (x_1, db) => 
               exec_73_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:177.1-177.37 *)
      
      (* assert -- allvNeg (with _ A) Y *)
      fun exec_72_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.With (USCORE_1, A)), Y) db)
      (* allvNeg A Y - syntax.l10:177.25-177.36 *)
      fun exec_72 (USCORE_1, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_72_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:176.1-176.37 *)
      
      (* assert -- allvNeg (with A _) Y *)
      fun exec_71_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.With (A, USCORE_1)), Y) db)
      (* allvNeg A Y - syntax.l10:176.25-176.36 *)
      fun exec_71 (USCORE_1, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_71_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:175.1-175.39 *)
      
      (* assert -- allvNeg (righti _ A) Y *)
      fun exec_70_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Righti (USCORE_1, A)), Y) db)
      (* allvNeg A Y - syntax.l10:175.27-175.38 *)
      fun exec_70 (USCORE_1, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_70_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:174.1-174.39 *)
      
      (* assert -- allvNeg (righti A _) Y *)
      fun exec_69_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Righti (A, USCORE_1)), Y) db)
      (* allvPos A Y - syntax.l10:174.27-174.38 *)
      fun exec_69 (USCORE_1, A) satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_69_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:173.1-173.38 *)
      
      (* assert -- allvNeg (lefti _ A) Y *)
      fun exec_68_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Lefti (USCORE_1, A)), Y) db)
      (* allvNeg A Y - syntax.l10:173.26-173.37 *)
      fun exec_68 (USCORE_1, A) satu db =
         L10_Tables.fold_19
            (fn (x_1, db) => 
               exec_68_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:172.1-172.38 *)
      
      (* assert -- allvNeg (lefti A _) Y *)
      fun exec_67_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Lefti (A, USCORE_1)), Y) db)
      (* allvPos A Y - syntax.l10:172.26-172.37 *)
      fun exec_67 (USCORE_1, A) satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_67_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:171.1-171.34 *)
      
      (* assert -- allvNeg (lax A) Y *)
      fun exec_66_1 (Y, A) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.Lax A), Y) db)
      (* allvPos A Y - syntax.l10:171.22-171.33 *)
      fun exec_66 A satu db =
         L10_Tables.fold_18
            (fn (x_1, db) => 
               exec_66_1 (x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:170.1-170.42 *)
      
      (* assert -- allvNeg (nAtom _ Sp) Y *)
      fun exec_65_1 (USCORE_1, Sp, Y) satu db =
         (L10_Tables.assert_allvNeg ((NegProp.NAtom (USCORE_1, Sp)), Y) db)
      (* allvSpine Sp Y - syntax.l10:170.27-170.41 *)
      fun exec_65 (USCORE_1, Sp) satu db =
         L10_Tables.fold_9
            (fn (x_1, db) => 
               exec_65_1 (USCORE_1, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:154.1-154.43 *)
      
      (* assert -- fvNeg (alli X T A) Y *)
      fun exec_56_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* X != Y - syntax.l10:154.36-154.42 *)
      fun exec_56_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_56_2 (T, Y, X, A) satu db else db
      (* fvNeg A Y - syntax.l10:154.25-154.34 *)
      fun exec_56 (T, X, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_56_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:153.1-153.32 *)
      
      (* assert -- fvNeg (alli X T A) Y *)
      fun exec_55_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Alli (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:153.25-153.31 *)
      fun exec_55 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_55_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:152.1-152.42 *)
      
      (* assert -- fvNeg (all X T A) Y *)
      fun exec_54_2 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.All (X, T, A)), Y) db)
      (* X != Y - syntax.l10:152.35-152.41 *)
      fun exec_54_1 (T, Y, X, A) satu db =
         if (not (EQUAL = String.compare (X, Y)))
         then exec_54_2 (T, Y, X, A) satu db else db
      (* fvNeg A Y - syntax.l10:152.24-152.33 *)
      fun exec_54 (T, X, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_54_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:151.1-151.31 *)
      
      (* assert -- fvNeg (all X T A) Y *)
      fun exec_53_1 (T, Y, X, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.All (X, T, A)), Y) db)
      (* fv T Y - syntax.l10:151.24-151.30 *)
      fun exec_53 (T, X, A) satu db =
         L10_Tables.fold_4
            (fn (x_1, db) => 
               exec_53_1 (T, x_1 (* Y *), X, A) satu db)
            db (#2 db) T
      
      (* Rule at syntax.l10:150.1-150.33 *)
      
      (* assert -- fvNeg (with _ A) Y *)
      fun exec_52_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.With (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:150.23-150.32 *)
      fun exec_52 (USCORE_1, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_52_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:149.1-149.33 *)
      
      (* assert -- fvNeg (with A _) Y *)
      fun exec_51_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.With (A, USCORE_1)), Y) db)
      (* fvNeg A Y - syntax.l10:149.23-149.32 *)
      fun exec_51 (USCORE_1, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_51_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:148.1-148.35 *)
      
      (* assert -- fvNeg (righti _ A) Y *)
      fun exec_50_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Righti (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:148.25-148.34 *)
      fun exec_50 (USCORE_1, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_50_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:147.1-147.35 *)
      
      (* assert -- fvNeg (righti A _) Y *)
      fun exec_49_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Righti (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:147.25-147.34 *)
      fun exec_49 (USCORE_1, A) satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_49_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:146.1-146.34 *)
      
      (* assert -- fvNeg (lefti _ A) Y *)
      fun exec_48_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lefti (USCORE_1, A)), Y) db)
      (* fvNeg A Y - syntax.l10:146.24-146.33 *)
      fun exec_48 (USCORE_1, A) satu db =
         L10_Tables.fold_15
            (fn (x_1, db) => 
               exec_48_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:145.1-145.34 *)
      
      (* assert -- fvNeg (lefti A _) Y *)
      fun exec_47_1 (USCORE_1, Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lefti (A, USCORE_1)), Y) db)
      (* fvPos A Y - syntax.l10:145.24-145.33 *)
      fun exec_47 (USCORE_1, A) satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_47_1 (USCORE_1, x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:144.1-144.30 *)
      
      (* assert -- fvNeg (lax A) Y *)
      fun exec_46_1 (Y, A) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.Lax A), Y) db)
      (* fvPos A Y - syntax.l10:144.20-144.29 *)
      fun exec_46 A satu db =
         L10_Tables.fold_14
            (fn (x_1, db) => 
               exec_46_1 (x_1 (* Y *), A) satu db)
            db (#2 db) A
      
      (* Rule at syntax.l10:143.1-143.38 *)
      
      (* assert -- fvNeg (nAtom _ Sp) Y *)
      fun exec_45_1 (USCORE_1, Sp, Y) satu db =
         (L10_Tables.assert_fvNeg ((NegProp.NAtom (USCORE_1, Sp)), Y) db)
      (* fvSpine Sp Y - syntax.l10:143.25-143.37 *)
      fun exec_45 (USCORE_1, Sp) satu db =
         L10_Tables.fold_5
            (fn (x_1, db) => 
               exec_45_1 (USCORE_1, Sp, x_1 (* Y *)) satu db)
            db (#2 db) Sp
      
      (* Rule at syntax.l10:254.1-254.47 *)
      
      (* assert -- classify C Eh *)
      fun exec_117_3 (Eh, C) satu db =
         (L10_Tables.assert_classify (C, Eh) db)
      (* headClass E Eh - syntax.l10:254.32-254.46 *)
      fun exec_117_2 (E, C) satu db =
         L10_Tables.fold_46
            (fn (x_1, db) => 
               exec_117_3 (x_1 (* Eh *), C) satu db)
            db (#2 db) E
      (* Dynamic world search: wExp E *)
      fun exec_117_1 (E, C) satu (flag, db) =
         exec_117_2 (E, C) satu (flag, satu (World.WExp E) db)
      (* signat C E _ - syntax.l10:254.18-254.30 *)
      fun exec_117 () satu db =
         L10_Tables.fold_45
            (fn ((x_0, x_1, x_2), db) => 
               exec_117_1 (x_1 (* E *), x_0 (* C *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:276.1-278.22 *)
      
      (* assert -- ruleSubord H1 H3 *)
      fun exec_120_2 (H1, H3) satu db =
         (L10_Tables.assert_ruleSubord (H1, H3) db)
      (* ruleSubord H2 H3 - syntax.l10:277.1-277.17 *)
      fun exec_120_1 (H1, H2) satu db =
         L10_Tables.fold_44
            (fn (x_1, db) => 
               exec_120_2 (H1, x_1 (* H3 *)) satu db)
            db (#2 db) H2
      (* ruleSubord H1 H2 - syntax.l10:276.1-276.17 *)
      fun exec_120 () satu db =
         L10_Tables.fold_43
            (fn ((x_0, x_1), db) => 
               exec_120_1 (x_0 (* H1 *), x_1 (* H2 *)) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:270.1-274.22 *)
      
      (* assert -- ruleSubord H1 H2 *)
      fun exec_119_7 (H1, H2) satu db =
         (L10_Tables.assert_ruleSubord (H1, H2) db)
      (* headNeg B2 H2 - syntax.l10:273.1-273.14 *)
      fun exec_119_6 (B2, H1) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_119_7 (H1, x_1 (* H2 *)) satu db)
            db (#2 db) B2
      (* Dynamic world search: wNeg B2 *)
      fun exec_119_5 (B2, H1) satu (flag, db) =
         exec_119_6 (B2, H1) satu (flag, satu (World.WNeg B2) db)
      (* headPos B1 H1 - syntax.l10:272.1-272.14 *)
      fun exec_119_4 (B1, B2) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_119_5 (B2, x_1 (* H1 *)) satu db)
            db (#2 db) B1
      (* Dynamic world search: wPos B1 *)
      fun exec_119_3 (B1, B2) satu (flag, db) =
         exec_119_4 (B1, B2) satu (flag, satu (World.WPos B1) db)
      (* subNeg A (neg (righti B1 B2)) - syntax.l10:271.1-271.30 *)
      fun exec_119_2 A satu db =
         L10_Tables.fold_42
            (fn ((x_1_0_0, x_1_0_1), db) => 
               exec_119_3 (x_1_0_0 (* B1 *), x_1_0_1 (* B2 *)) satu db)
            db (#2 db) A
      (* Dynamic world search: wNeg A *)
      fun exec_119_1 A satu (flag, db) =
         exec_119_2 A satu (flag, satu (World.WNeg A) db)
      (* rules C A - syntax.l10:270.1-270.10 *)
      fun exec_119 () satu db =
         L10_Tables.fold_38
            (fn ((x_0, x_1), db) => 
               exec_119_1 x_1 (* A *) satu db)
            db (#2 db) ()
      
      (* Rule at syntax.l10:264.1-268.22 *)
      
      (* assert -- ruleSubord H1 H2 *)
      fun exec_118_7 (H1, H2) satu db =
         (L10_Tables.assert_ruleSubord (H1, H2) db)
      (* headNeg B2 H2 - syntax.l10:267.1-267.14 *)
      fun exec_118_6 (B2, H1) satu db =
         L10_Tables.fold_41
            (fn (x_1, db) => 
               exec_118_7 (H1, x_1 (* H2 *)) satu db)
            db (#2 db) B2
      (* Dynamic world search: wNeg B2 *)
      fun exec_118_5 (B2, H1) satu (flag, db) =
         exec_118_6 (B2, H1) satu (flag, satu (World.WNeg B2) db)
      (* headPos B1 H1 - syntax.l10:266.1-266.14 *)
      fun exec_118_4 (B1, B2) satu db =
         L10_Tables.fold_40
            (fn (x_1, db) => 
               exec_118_5 (B2, x_1 (* H1 *)) satu db)
            db (#2 db) B1
      (* Dynamic world search: wPos B1 *)
      fun exec_118_3 (B1, B2) satu (flag, db) =
         exec_118_4 (B1, B2) satu (flag, satu (World.WPos B1) db)
      (* subNeg A (neg (lefti B1 B2)) - syntax.l10:265.1-265.29 *)
      fun exec_118_2 A satu db =
         L10_Tables.fold_39
            (fn ((x_1_0_0, x_1_0_1), db) => 
               exec_118_3 (x_1_0_0 (* B1 *), x_1_0_1 (* B2 *)) satu db)
            db (#2 db) A
      (* Dynamic world search: wNeg A *)
      fun exec_118_1 A satu (flag, db) =
         exec_118_2 A satu (flag, satu (World.WNeg A) db)
      (* rules C A - syntax.l10:264.1-264.10 *)
      fun exec_118 () satu db =
         L10_Tables.fold_38
            (fn ((x_0, x_1), db) => 
               exec_118_1 x_1 (* A *) satu db)
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
               (* Rule #121, default world *)
               (* syntax.l10:287.1-287.47 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_121 () saturate o exec
               
               (* Rule #122, default world *)
               (* syntax.l10:290.1-290.81 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_122 () saturate o exec
               
               (* Rule #123, default world *)
               (* syntax.l10:293.1-293.50 *)
               val db = saturate_wRuleSubord db
               val exec = L10_Consequence.exec_123 () saturate o exec
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
                     
                     (* Rule #22, world (wExp (pi X T E)) *)
                     (* syntax.l10:93.1-93.31 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_22 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #23, world (wExp (pi X T E)) *)
                     (* syntax.l10:94.1-94.31 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_23 (x_0_2, x_0_1, x_0_0) saturate o exec
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
                     
                     (* Rule #24, world (wExp (pii X T E)) *)
                     (* syntax.l10:95.1-95.32 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_24 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #25, world (wExp (pii X T E)) *)
                     (* syntax.l10:96.1-96.32 *)
                     (* { E |-> [ x_0_2 ],
                      *   T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_2 db
                     val exec = L10_Consequence.exec_25 (x_0_2, x_0_1, x_0_0) saturate o exec
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
                     
                     (* Rule #26, world (wExp (arrow E1 E2)) *)
                     (* syntax.l10:97.1-97.35 *)
                     (* { E1 |-> [ x_0_0 ],
                      *   E2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_26 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #27, world (wExp (arrow E1 E2)) *)
                     (* syntax.l10:98.1-98.35 *)
                     (* { E1 |-> [ x_0_0 ],
                      *   E2 |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_27 (x_0_0, x_0_1) saturate o exec
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
                     
                     (* Rule #28, world (wExp (var X _ Sp)) *)
                     (* syntax.l10:99.1-99.21 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ],
                      *   X |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_28 (x_0_1, x_0_2, x_0_0) saturate o exec
                     
                     (* Rule #29, world (wExp (var X _ Sp)) *)
                     (* syntax.l10:100.1-100.39 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wSpine x_0_2 db
                     val exec = L10_Consequence.exec_29 (x_0_1, x_0_2, x_0_0) saturate o exec
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
                     
                     (* Rule #30, world (wExp (con _ Sp)) *)
                     (* syntax.l10:101.1-101.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_30 (x_0_0, x_0_1) saturate o exec
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
                     
                     (* Rule #31, world (wExp (lam X E)) *)
                     (* syntax.l10:102.1-102.30 *)
                     (* { E |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_31 (x_0_1, x_0_0) saturate o exec
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
                     
                     (* Rule #32, world (wSpine (app E Sp)) *)
                     (* syntax.l10:105.1-105.36 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_32 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #33, world (wSpine (app E Sp)) *)
                     (* syntax.l10:106.1-106.42 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_33 (x_0_0, x_0_1) saturate o exec
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
                     
                     (* Rule #34, world (wSpine (appi E Sp)) *)
                     (* syntax.l10:107.1-107.37 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_34 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #35, world (wSpine (appi E Sp)) *)
                     (* syntax.l10:108.1-108.43 *)
                     (* { E |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_35 (x_0_0, x_0_1) saturate o exec
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
               (* Rule #36, world wMode *)
               (* syntax.l10:122.1-122.38 *)
               val exec = L10_Consequence.exec_36 () saturate o exec
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
                     (* Rule #37, world (wPos (pAtom _ _ Sp)) *)
                     (* syntax.l10:133.1-133.40 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ] } *)
                     val db = saturate_wSpine x_0_2 db
                     val exec = L10_Consequence.exec_37 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #57, world (wPos (pAtom _ _ Sp)) *)
                     (* syntax.l10:160.1-160.44 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   Sp |-> [ x_0_2 ] } *)
                     val db = saturate_wSpine x_0_2 db
                     val exec = L10_Consequence.exec_57 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0=(pAtom x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #92, world (wPos (pAtom P A Sp)) *)
                     (* syntax.l10:205.1-205.38 *)
                     (* { Sp |-> [ x_0_2 ],
                      *   A |-> [ x_0_1 ],
                      *   P |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_92 (x_0_2, x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0=(pAtom x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Down (x_0_0, x_0_1) =>
                  (* wPos (down x_0_0 x_0_1) *)
                  let
                     (* Rule #38, world (wPos (down _ A)) *)
                     (* syntax.l10:134.1-134.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_38 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #58, world (wPos (down _ A)) *)
                     (* syntax.l10:161.1-161.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_58 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0=(down x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #78, world (wPos (down _ A)) *)
                     (* syntax.l10:188.1-188.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_78 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #93, world (wPos (down P A)) *)
                     (* syntax.l10:206.1-206.30 *)
                     (* { A |-> [ x_0_1 ],
                      *   P |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_93 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0=(down x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Fuse (x_0_0, x_0_1) =>
                  (* wPos (fuse x_0_0 x_0_1) *)
                  let
                     (* Rule #39, world (wPos (fuse A _)) *)
                     (* syntax.l10:135.1-135.33 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_39 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #40, world (wPos (fuse _ A)) *)
                     (* syntax.l10:136.1-136.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_40 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #59, world (wPos (fuse A _)) *)
                     (* syntax.l10:162.1-162.37 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_59 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #60, world (wPos (fuse _ A)) *)
                     (* syntax.l10:163.1-163.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_60 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0=(fuse x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #79, world (wPos (fuse A _)) *)
                     (* syntax.l10:189.1-189.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_79 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #80, world (wPos (fuse _ A)) *)
                     (* syntax.l10:190.1-190.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_80 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #94, world (wPos (fuse A _)) *)
                     (* syntax.l10:207.1-207.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_94 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #95, world (wPos (fuse _ A)) *)
                     (* syntax.l10:208.1-208.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_1 db
                     val exec = L10_Consequence.exec_95 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0=(fuse x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Exists (x_0_0, x_0_1, x_0_2) =>
                  (* wPos (exists x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #41, world (wPos (exists X T A)) *)
                     (* syntax.l10:137.1-137.34 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_41 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #42, world (wPos (exists X T A)) *)
                     (* syntax.l10:138.1-138.45 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_42 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #61, world (wPos (exists X T A)) *)
                     (* syntax.l10:164.1-164.38 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_61 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #62, world (wPos (exists X T A)) *)
                     (* syntax.l10:165.1-165.41 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_62 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0=(exists x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #81, world (wPos (exists _ _ A)) *)
                     (* syntax.l10:191.1-191.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_81 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #96, world (wPos (exists _ _ A)) *)
                     (* syntax.l10:209.1-209.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wPos x_0_2 db
                     val exec = L10_Consequence.exec_96 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0=(exists x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | PosProp.Unif (x_0_0, x_0_1) =>
                  (* wPos (unif x_0_0 x_0_1) *)
                  let
                     (* Rule #43, world (wPos (unif T S)) *)
                     (* syntax.l10:139.1-139.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_43 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #44, world (wPos (unif T S)) *)
                     (* syntax.l10:140.1-140.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_44 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #63, world (wPos (unif T S)) *)
                     (* syntax.l10:166.1-166.34 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_0 db
                     val exec = L10_Consequence.exec_63 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #64, world (wPos (unif T S)) *)
                     (* syntax.l10:167.1-167.34 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_64 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0=(unif x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #97, world (wPos (unif T S)) *)
                     (* syntax.l10:210.1-210.30 *)
                     (* { T |-> [ x_0_0 ],
                      *   S |-> [ x_0_1 ] } *)
                     val exec = L10_Consequence.exec_97 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0=(unif x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | _ =>
                  (* wPos x_0 *)
                  let
                     (* Rule #77, world (wPos A) *)
                     (* syntax.l10:187.1-187.18 *)
                     (* { A |-> [ x_0 ] } *)
                     val exec = L10_Consequence.exec_77 x_0 saturate o exec
                     
                     (* Rule #116, world (wPos A) *)
                     (* syntax.l10:242.1-242.51 *)
                     (* { A |-> [ x_0 ] } *)
                     val exec = L10_Consequence.exec_116 x_0 saturate o exec
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
                     (* Rule #45, world (wNeg (nAtom _ Sp)) *)
                     (* syntax.l10:143.1-143.38 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_45 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #65, world (wNeg (nAtom _ Sp)) *)
                     (* syntax.l10:170.1-170.42 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   Sp |-> [ x_0_1 ] } *)
                     val db = saturate_wSpine x_0_1 db
                     val exec = L10_Consequence.exec_65 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #106, world (wNeg (nAtom A Sp)) *)
                     (* syntax.l10:223.1-223.34 *)
                     (* { Sp |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_106 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(nAtom x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Lax x_0_0 =>
                  (* wNeg (lax x_0_0) *)
                  let
                     (* Rule #46, world (wNeg (lax A)) *)
                     (* syntax.l10:144.1-144.30 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_46 x_0_0 saturate o exec
                     
                     (* Rule #66, world (wNeg (lax A)) *)
                     (* syntax.l10:171.1-171.34 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_66 x_0_0 saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #83, world (wNeg (lax A)) *)
                     (* syntax.l10:194.1-194.32 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_83 x_0_0 saturate o exec
                     
                     (* Rule #107, world (wNeg (lax A)) *)
                     (* syntax.l10:224.1-224.24 *)
                     (* { A |-> [ x_0_0 ] } *)
                     val exec = L10_Consequence.exec_107 x_0_0 saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(lax x_0_0) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Lefti (x_0_0, x_0_1) =>
                  (* wNeg (lefti x_0_0 x_0_1) *)
                  let
                     (* Rule #47, world (wNeg (lefti A _)) *)
                     (* syntax.l10:145.1-145.34 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_47 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #48, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:146.1-146.34 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_48 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #67, world (wNeg (lefti A _)) *)
                     (* syntax.l10:172.1-172.38 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_67 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #68, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:173.1-173.38 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_68 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #84, world (wNeg (lefti A _)) *)
                     (* syntax.l10:195.1-195.36 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_84 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #85, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:196.1-196.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_85 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #98, world (wNeg (lefti A B)) *)
                     (* syntax.l10:213.1-213.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_98 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #99, world (wNeg (lefti A B)) *)
                     (* syntax.l10:214.1-214.38 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_99 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #108, world (wNeg (lefti _ A)) *)
                     (* syntax.l10:225.1-225.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_108 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(lefti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Righti (x_0_0, x_0_1) =>
                  (* wNeg (righti x_0_0 x_0_1) *)
                  let
                     (* Rule #49, world (wNeg (righti A _)) *)
                     (* syntax.l10:147.1-147.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_49 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #50, world (wNeg (righti _ A)) *)
                     (* syntax.l10:148.1-148.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_50 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #69, world (wNeg (righti A _)) *)
                     (* syntax.l10:174.1-174.39 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_69 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #70, world (wNeg (righti _ A)) *)
                     (* syntax.l10:175.1-175.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_70 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #86, world (wNeg (righti A _)) *)
                     (* syntax.l10:197.1-197.37 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_86 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #87, world (wNeg (righti _ A)) *)
                     (* syntax.l10:198.1-198.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_87 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #100, world (wNeg (righti A B)) *)
                     (* syntax.l10:215.1-215.38 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wPos x_0_0 db
                     val exec = L10_Consequence.exec_100 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #101, world (wNeg (righti A B)) *)
                     (* syntax.l10:216.1-216.39 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_101 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #109, world (wNeg (righti _ A)) *)
                     (* syntax.l10:226.1-226.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_109 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(righti x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.With (x_0_0, x_0_1) =>
                  (* wNeg (with x_0_0 x_0_1) *)
                  let
                     (* Rule #51, world (wNeg (with A _)) *)
                     (* syntax.l10:149.1-149.33 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_51 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #52, world (wNeg (with _ A)) *)
                     (* syntax.l10:150.1-150.33 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_52 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #71, world (wNeg (with A _)) *)
                     (* syntax.l10:176.1-176.37 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_71 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #72, world (wNeg (with _ A)) *)
                     (* syntax.l10:177.1-177.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_72 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #88, world (wNeg (with A _)) *)
                     (* syntax.l10:199.1-199.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_88 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #89, world (wNeg (with _ A)) *)
                     (* syntax.l10:200.1-200.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_89 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #102, world (wNeg (with A B)) *)
                     (* syntax.l10:217.1-217.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_102 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #103, world (wNeg (with A B)) *)
                     (* syntax.l10:218.1-218.37 *)
                     (* { A |-> [ x_0_0 ],
                      *   B |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_103 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #110, world (wNeg (with A _)) *)
                     (* syntax.l10:227.1-227.35 *)
                     (* { USCORE_1 |-> [ x_0_1 ],
                      *   A |-> [ x_0_0 ] } *)
                     val db = saturate_wNeg x_0_0 db
                     val exec = L10_Consequence.exec_110 (x_0_1, x_0_0) saturate o exec
                     
                     (* Rule #111, world (wNeg (with _ A)) *)
                     (* syntax.l10:228.1-228.35 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   A |-> [ x_0_1 ] } *)
                     val db = saturate_wNeg x_0_1 db
                     val exec = L10_Consequence.exec_111 (x_0_0, x_0_1) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(with x_0_0 x_0_1) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.All (x_0_0, x_0_1, x_0_2) =>
                  (* wNeg (all x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #53, world (wNeg (all X T A)) *)
                     (* syntax.l10:151.1-151.31 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_53 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #54, world (wNeg (all X T A)) *)
                     (* syntax.l10:152.1-152.42 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_54 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #73, world (wNeg (all X T A)) *)
                     (* syntax.l10:178.1-178.35 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_73 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #74, world (wNeg (all X T A)) *)
                     (* syntax.l10:179.1-179.38 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_74 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #90, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:201.1-201.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_90 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #104, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:219.1-219.38 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_104 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #112, world (wNeg (all _ _ A)) *)
                     (* syntax.l10:229.1-229.36 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_112 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(all x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
                  in
                     loop exec db
                  end
             | NegProp.Alli (x_0_0, x_0_1, x_0_2) =>
                  (* wNeg (alli x_0_0 x_0_1 x_0_2) *)
                  let
                     (* Rule #55, world (wNeg (alli X T A)) *)
                     (* syntax.l10:153.1-153.32 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_55 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #56, world (wNeg (alli X T A)) *)
                     (* syntax.l10:154.1-154.43 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_56 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #75, world (wNeg (alli X T A)) *)
                     (* syntax.l10:180.1-180.36 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wExp x_0_1 db
                     val exec = L10_Consequence.exec_75 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #76, world (wNeg (alli X T A)) *)
                     (* syntax.l10:181.1-181.39 *)
                     (* { T |-> [ x_0_1 ],
                      *   X |-> [ x_0_0 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_76 (x_0_1, x_0_0, x_0_2) saturate o exec
                     
                     (* Rule #82, world (wNeg A) *)
                     (* syntax.l10:193.1-193.18 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_82 x_0 saturate o exec
                     
                     (* Rule #91, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:202.1-202.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_91 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #105, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:220.1-220.39 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_105 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #113, world (wNeg (alli _ _ A)) *)
                     (* syntax.l10:230.1-230.37 *)
                     (* { USCORE_1 |-> [ x_0_0 ],
                      *   USCORE_2 |-> [ x_0_1 ],
                      *   A |-> [ x_0_2 ] } *)
                     val db = saturate_wNeg x_0_2 db
                     val exec = L10_Consequence.exec_113 (x_0_0, x_0_1, x_0_2) saturate o exec
                     
                     (* Rule #114, world (wNeg A) *)
                     (* syntax.l10:240.1-240.39 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_114 x_0 saturate o exec
                     
                     (* Rule #115, world (wNeg A) *)
                     (* syntax.l10:241.1-241.46 *)
                     (* { A |-> [ x_0=(alli x_0_0 x_0_1 x_0_2) ] } *)
                     val exec = L10_Consequence.exec_115 x_0 saturate o exec
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
               (* Rule #117, world wSignat *)
               (* syntax.l10:254.1-254.47 *)
               val exec = L10_Consequence.exec_117 () saturate o exec
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
               (* Rule #118, world wRuleSubord *)
               (* syntax.l10:264.1-268.22 *)
               val db = saturate_wSignat db
               val exec = L10_Consequence.exec_118 () saturate o exec
               
               (* Rule #119, world wRuleSubord *)
               (* syntax.l10:270.1-274.22 *)
               val db = saturate_wSignat db
               val exec = L10_Consequence.exec_119 () saturate o exec
               
               (* Rule #120, world wRuleSubord *)
               (* syntax.l10:276.1-278.22 *)
               val exec = L10_Consequence.exec_120 () saturate o exec
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
      
      fun allvNeg (args, db: db) =
         case L10_Tables.assert_allvNeg args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun allvPos (args, db: db) =
         case L10_Tables.assert_allvPos args (false, #pristine db) of
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
      
      fun allvSpine (args, db: db) =
         case L10_Tables.assert_allvSpine args (false, #pristine db) of
            (false, _) => db
          | (true, new_db) => {pristine=new_db, public=ref new_db}
      
      fun allv (args, db: db) =
         case L10_Tables.assert_allv args (false, #pristine db) of
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
       ; L10_Tables.fold_37 f x public ())
      end
      val notSemanticEffects = fn x => notSemanticEffects (fn _ => true) false x
      
      fun weaklySemanticEffects f x (db: db) =
      let
         val public = L10_Search.saturate_world (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_36 f x public ())
      end
      val weaklySemanticEffects = fn x => weaklySemanticEffects (fn _ => true) false x
      
      fun semanticEffects f x (db: db) =
      let
         val public = L10_Search.saturate_world (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_35 f x public ())
      end
      val semanticEffects = fn x => semanticEffects (fn _ => true) false x
      
      fun ruleSubord f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wRuleSubord (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_34 f x public (x_0, x_1))
      end
      val ruleSubord = fn x => ruleSubord (fn _ => true) false x
      
      fun lookupClass f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_33 f x public x_0)
      end
      val lookupClassList = lookupClass (op ::) []
      
      fun classify f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_32 f x public (x_0, x_1))
      end
      val classify = fn x => classify (fn _ => true) false x
      
      fun lookupRule f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_31 f x public x_0)
      end
      val lookupRuleList = lookupRule (op ::) []
      
      fun lookup f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_30 f x public x_0)
      end
      val lookupList = lookup (op ::) []
      
      fun rules f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_29 f x public (x_0, x_1))
      end
      val rules = fn x => rules (fn _ => true) false x
      
      fun signat f x (db: db) (x_0, x_1, x_2) =
      let
         val public = L10_Search.saturate_wSignat (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_28 f x public (x_0, x_1, x_2))
      end
      val signat = fn x => signat (fn _ => true) false x
      
      fun headNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_27 f x public (x_0, x_1))
      end
      val headNeg = fn x => headNeg (fn _ => true) false x
      
      fun headPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_26 f x public (x_0, x_1))
      end
      val headPos = fn x => headPos (fn _ => true) false x
      
      fun negHeads f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_25 f x public x_0)
      end
      val negHeadsList = negHeads (op ::) []
      
      fun endNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_24 f x public (x_0, x_1))
      end
      val endNeg = fn x => endNeg (fn _ => true) false x
      
      fun subgoal f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_23 f x public (x_0, x_1))
      end
      val subgoal = fn x => subgoal (fn _ => true) false x
      
      fun endPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_22 f x public (x_0, x_1))
      end
      val endPos = fn x => endPos (fn _ => true) false x
      
      fun subNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_21 f x public (x_0, x_1))
      end
      val subNeg = fn x => subNeg (fn _ => true) false x
      
      fun subPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_20 f x public (x_0, x_1))
      end
      val subPos = fn x => subPos (fn _ => true) false x
      
      fun allvarsNeg f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_19 f x public x_0)
      end
      val allvarsNegList = allvarsNeg (op ::) []
      
      fun allvarsPos f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_18 f x public x_0)
      end
      val allvarsPosList = allvarsPos (op ::) []
      
      fun allvNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_17 f x public (x_0, x_1))
      end
      val allvNeg = fn x => allvNeg (fn _ => true) false x
      
      fun allvPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_16 f x public (x_0, x_1))
      end
      val allvPos = fn x => allvPos (fn _ => true) false x
      
      fun freevarsNeg f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_15 f x public x_0)
      end
      val freevarsNegList = freevarsNeg (op ::) []
      
      fun freevarsPos f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_14 f x public x_0)
      end
      val freevarsPosList = freevarsPos (op ::) []
      
      fun fvNeg f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wNeg x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_13 f x public (x_0, x_1))
      end
      val fvNeg = fn x => fvNeg (fn _ => true) false x
      
      fun fvPos f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wPos x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_12 f x public (x_0, x_1))
      end
      val fvPos = fn x => fvPos (fn _ => true) false x
      
      fun varMode f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wMode (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_11 f x public (x_0, x_1))
      end
      val varMode = fn x => varMode (fn _ => true) false x
      
      fun givenMode f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wMode (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_10 f x public (x_0, x_1))
      end
      val givenMode = fn x => givenMode (fn _ => true) false x
      
      fun allvarsSpine f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wSpine x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_9 f x public x_0)
      end
      val allvarsSpineList = allvarsSpine (op ::) []
      
      fun allvars f x (db: db) x_0 =
      let
         val public = L10_Search.saturate_wExp x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_8 f x public x_0)
      end
      val allvarsList = allvars (op ::) []
      
      fun allvSpine f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wSpine x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_7 f x public (x_0, x_1))
      end
      val allvSpine = fn x => allvSpine (fn _ => true) false x
      
      fun allv f x (db: db) (x_0, x_1) =
      let
         val public = L10_Search.saturate_wExp x_0 (!(#public db))
      in
       ( #public db := public
       ; L10_Tables.fold_6 f x public (x_0, x_1))
      end
      val allv = fn x => allv (fn _ => true) false x
      
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
