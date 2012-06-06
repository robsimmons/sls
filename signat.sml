structure Signature = 
struct
 
   val signat = ref Syntax.empty

   fun lookup cid = 
      case Syntax.Query.lookupList (!signat) cid of
         [] => raise Fail ("Failed type lookup on "^Symbol.toValue cid) 
       | (x, _) :: _ => x

   fun handleCondec (cid, exp, Exp.Knd) = 
         signat := Syntax.Assert.signat ((cid, exp, Exp.Knd), !signat)
     | handleCondec (cid, exp, Exp.Typ) =
         signat := Syntax.Assert.signat ((cid, exp, Exp.Typ), !signat)
     | handleCondec (_, _, class) =  
         raise Fail ("Bad class: "^Exp.toString class)

   fun init () =
      {syntax = ignore,
       condec = handleCondec,
       rule = ignore}
end
