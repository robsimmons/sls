structure Frontend =
struct
   fun init () = 
    ( Handle.register "type reconstruction" 0 (Recon.init ())
    ; Handle.register "signature storage/analysis" 5 (Signature.init ())
    ; Handle.register "mode checking" 5 (Mode.init ())
    ; Handle.register "pretty-printing syntax" 5 (PrettyPrint.init ())
    ; ())

   fun loop str =
   let in
     (case Stream.front str of
         Stream.Nil => OS.Process.success
       | Stream.Cons (toplevel, str) =>
            (Handle.syntax toplevel; loop str))
(*  handle Parse.Parse (pos, msg) => 
             ( print ("Parse error: "^Pos.toString pos^"\n"^msg^"\n")
             ; OS.Process.failure)
          | exn => 
             ( print ("Unhandled exception "^exnName exn^":\n")
             ; print (exnMessage exn^"\n")
             ; OS.Process.failure) *)
   end

   fun load file =
      loop (Parse.parse (Lex.tokenizeFile file))

   fun reset () = Handle.reset ()
end
