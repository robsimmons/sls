structure Signature = 
struct
 
   val signat = ref Syntax.empty

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
       reset = fn () => signat := Syntax.empty}
end
