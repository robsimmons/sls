structure PrettyPrint =
struct
   fun lp true = "("
     | lp false = ""

   fun rp true = ")"
     | rp false = "" 

   fun symbol p = 
      case p of 
         Perm.Pers => "!"
       | Perm.Aff => "@"
       | Perm.Lin => "$"
       | Perm.Ord => ""

   fun perm p =
      case p of
         Perm.Pers => "pers"
       | Perm.Aff => "aff"
       | Perm.Lin => "lin" 
       | Perm.Ord => "ord"

   fun exp np tm = 
      case tm of 
         Exp.Knd => "kind"
       | Exp.Typ => "type"
       | Exp.NProp => "prop"
       | Exp.PProp p => "prop "^perm p
       | Exp.Pi (x, t, tm) => 
            lp np^"Pi "^x^": "^exp false t^". "^exp false tm^rp np
       | Exp.Pii (_, _, tm) => exp np tm
       | Exp.Arrow (t1, t2) => 
            lp np^exp true t1 ^" -> "^exp false t2^rp np
       | Exp.Var (x, _, Spine.Nil) => x
       | Exp.Var (x, _, sp) =>
            lp np^x^spine sp^rp np
       | Exp.Con (c, Spine.Nil) => Symbol.toValue c
       | Exp.Con (c, sp) => 
            lp np^Symbol.toValue c^spine sp^rp np
       | Exp.Lam (x, tm) =>
            lp np^"\\"^x^". "^exp false tm^rp np

   and spine sp =
      case sp of
         Spine.Nil => ""
       | Spine.Appi (_, sp) => spine sp
       | Spine.App (tm, sp) => " "^exp true tm^spine sp

   fun exp' (tm as Exp.Var _) = exp false tm
     | exp' (tm as Exp.Con _) = exp false tm
     | exp' tm = exp true tm

   fun pos np pprop = 
      case pprop of
         PosProp.PAtom (_, c, sp) => Symbol.toValue c^spine sp
       | PosProp.Down (p, nprop) =>
            symbol p^neg true nprop
       | PosProp.One => "1"
       | PosProp.Fuse (pprop1, pprop2) => 
            pos true pprop1^" * "^pos false pprop2
       | PosProp.Exists (x, t, pprop) => 
            lp np^"Exists "^x^": "^exp' t^". "^pos false pprop^rp np
       | PosProp.Unif (t1, t2) =>
            exp' t1^" == "^exp' t2

   and neg np nprop =
      case nprop of 
         NegProp.NAtom (c, sp) => Symbol.toValue c^spine sp
       | NegProp.Lax pprop => "{"^pos false pprop^"}"

       | NegProp.Lefti (PosProp.Down (Perm.Pers, nprop1), nprop2) =>
            lp np^neg true nprop1^" -> "^neg false nprop2^rp np
       | NegProp.Lefti (PosProp.Down (Perm.Aff, nprop1), nprop2) =>
            lp np^neg true nprop1^" -@ "^neg false nprop2^rp np
       | NegProp.Lefti (PosProp.Down (Perm.Lin, nprop1), nprop2) =>
            lp np^neg true nprop1^" -o "^neg false nprop2^rp np
       | NegProp.Lefti (pprop1, nprop2) =>
            lp np^pos true pprop1^" >-> "^neg false nprop2^rp np

       | NegProp.Righti (PosProp.Down (Perm.Pers, nprop1), nprop2) =>
            lp np^neg true nprop1^" -> "^neg false nprop2^rp np
       | NegProp.Righti (PosProp.Down (Perm.Aff, nprop1), nprop2) =>
            lp np^neg true nprop1^" -@ "^neg false nprop2^rp np
       | NegProp.Righti (PosProp.Down (Perm.Lin, nprop1), nprop2) =>
            lp np^neg true nprop1^" -o "^neg false nprop2^rp np
       | NegProp.Righti (pprop1, nprop2) => 
            lp np^pos true pprop1^" ->> "^neg false nprop2^rp np

       | NegProp.With (nprop1, nprop2) =>
            lp np^neg true nprop1^" & "^neg true nprop2^rp np
       | NegProp.All (x, t, nprop) =>
            lp np^"All "^x^": "^exp' t^". "^neg false nprop^rp np
       | NegProp.Alli (x, t, nprop) => neg np nprop

   val cProp = Symbol.fromValue "prop"
   val cOrd = Symbol.fromValue "ord"
   val cAff = Symbol.fromValue "aff"
   val cLin = Symbol.fromValue "lin"
   val cPers = Symbol.fromValue "pers"
   val cType = Symbol.fromValue "type"
   fun printCondec (c, tm, _) = 
      if Exp.eq (Exp.Typ, tm) 
         andalso (Symbol.eq (c, cProp) orelse Symbol.eq (c, cOrd)
                  orelse Symbol.eq (c, cAff) orelse Symbol.eq (c, cLin)
                  orelse Symbol.eq (c, cPers) orelse Symbol.eq (c, cType))
      then () 
      else print (Symbol.toValue c^": "^exp false tm^".\n")

   fun init () = 
      {syntax = ignore,
       condec = printCondec,
       rule = fn (r, nprop) => 
                   print (Symbol.toValue r^": "^neg false nprop^".\n"),
       reset = ignore}
end
