(* Reconstruction handler (triggers the syntax/condec/rule handlers *)

signature RECON =
sig
   val handler: Handle.handler
end

structure Recon =
struct
   fun handleCondec (s, dats, pos) = 
    ( print (s^": ")
    ; List.app (fn dat => (PosDatum.print dat)) dats
    ; print ".\n")

   val handler =
      {syntax = 
          (fn (PosDatum.List [ ("condec", [PosDatum.Atom (s, _)], pos1), 
                               (":", dats, pos2)]) =>
                 handleCondec (s, dats, Pos.union pos1 pos2)
            | _ => ()),
       condec = ignore,
       rule = ignore}
end
