structure Frontend =
struct
   fun init () = 
    ( Handle.register "type reconstruction" 0 (Recon.init ())
    ; Handle.register "signature storage/analysis" 5 (Signature.init ())
    ; Handle.register "mode checking" 5 (Modes.init ())
    ; Handle.register "pretty-printing syntax" 5 (PrettyPrint.init ())
    ; Handle.register "operationalize" 10 (Operationalize.init ())
    ; ())

   fun loop str =
   let in
     (case Stream.front str of
         Stream.Nil => OS.Process.success
       | Stream.Cons (toplevel, str) =>
            (Handle.syntax toplevel; loop str))
  handle Parse.Parse (pos, msg) => 
             ( print ("Parse error: "^Pos.toString pos^"\n"^msg^"\n")
             ; OS.Process.failure; raise Match)
          | exn => 
             ( print ("Unhandled exception "^exnName exn^":\n")
             ; print (exnMessage exn^"\n")
             ; OS.Process.failure; raise Match) 
   end

   fun load file =
      loop (Parse.parse (Lex.tokenizeFile file))

   fun read str = 
      loop (Parse.parse (Lex.tokenizeString str))

   fun reset () = Handle.reset ()
end
