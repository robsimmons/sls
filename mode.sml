signature MODE =
sig
   val handler: Handle.handler
end

structure Mode =
struct

   fun handleMode (dats, pos) =
    ( print ("#mode ")
    ; List.app (fn dat => (PosDatum.print dat)) dats
    ; print ".\n")
 
   fun modeCheck _ = ()

   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("mode", dats, pos)]) => handleMode (dats, pos)
            | _ => ()),
       condec = ignore,
       rule = modeCheck}
end
