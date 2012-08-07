structure Signature = 
struct
 
   val reserved_names = 
   let val fakepos = (fn c => Pos.pos c c) (Coord.init "<sls core>")
   in 
      List.foldr
         (fn (name, dict) => 
             SymbolRedBlackDict.insert dict (Symbol.fromValue name) fakepos)
         SymbolRedBlackDict.empty
         ["(", ")", "{", "}", 
          "All", "Pi", "Exists", "\\",
          "&", "<-<", "<<-", "o-", "<-", "->>", "-o", "->", ">->", "*",
          "==", "!", "@", "$", 
          "one" (*, "type", "prop", "ord", "lin", "aff", "pers" *)]
   end

   val empty = Syntax.empty (* Useful for memoizing *)
   val signat = ref Syntax.empty
   val used_names = ref reserved_names

   fun register cid pos = 
   let fun errmsg pos' = "Cannot reserve identifier "^Symbol.toValue cid^" \
                         \at "^Pos.toString pos^" - identifier was already \
                         \reserved at "^Pos.toString pos'
   in
      used_names := #3 (SymbolRedBlackDict.operate (!used_names) cid
                           (fn () => pos)
                           (fn pos' => raise Fail (errmsg pos')))
   end

   fun registered cid = SymbolRedBlackDict.find (!used_names) cid 

   fun find cid = 
      case Syntax.Query.lookupList (!signat) cid of
         [] => NONE
       | (x, _) :: _ => SOME x

   fun findClass cid = 
      case Syntax.Query.lookupClassList (!signat) cid of
         [] => NONE
       | x :: _ => SOME x

   fun lookup cid = 
      case Syntax.Query.lookupList (!signat) cid of
         [] => raise Fail ("Failed type lookup on "^Symbol.toValue cid) 
       | (x, _) :: _ => x

   fun isPosPred cid = 
      case Syntax.Query.lookupClassList (!signat) cid of
         [] => raise Fail ("Failed lookup on "^Symbol.toValue cid) 
       | (Exp.PProp _ :: _) => true
       | _ => false

   fun isNegPred cid = 
      case Syntax.Query.lookupClassList (!signat) cid of
         [] => raise Fail ("Failed lookup on "^Symbol.toValue cid) 
       | (Exp.NProp :: _) => true
       | _ => false

   fun handleCondec (cid, exp, Exp.Knd) = 
         signat := Syntax.Assert.signat ((cid, exp, Exp.Knd), !signat)
     | handleCondec (cid, exp, Exp.Typ) =
         signat := Syntax.Assert.signat ((cid, exp, Exp.Typ), !signat)
     | handleCondec (_, _, class) =  
         raise Fail ("Bad class: "^Exp.toString class)

   fun init () =
      {syntax = ignore,
       condec = handleCondec,
       rule = ignore,
       reset = fn () => (signat := Syntax.empty; used_names := reserved_names)}
end
