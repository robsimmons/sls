structure Frontend =
struct
   fun init () = 
    ( Handle.register "type reconstruction" 0 (Recon.init ())
    ; Handle.register "signature storage/analysis" 5 (Signature.init ())
    ; Handle.register "mode checking" 5 (Modes.init ())
    ; Handle.register "pretty-printing syntax" 5 (PrettyPrint.init ())
    ; Handle.register "operationalize" 10 (Operationalize.init ())
    ; Handle.register "defunctionalize" 10 (Defunctionalize.init ())
    ; Handle.register "destadd" 10 (DestAdd.init ())
    ; ())

   fun loop str =
     (case Stream.front str of
         Stream.Nil => ()
       | Stream.Cons (toplevel, str) =>
            (Handle.syntax toplevel; loop str))

   fun handler exn = 
      case exn of 
         Parse.Parse (pos, msg) => 
          ( print ("Parse error: "^Pos.toString pos^"\n"^msg^"\n"))
       | exn => 
          ( print ("Unhandled exception "^exnName exn^":\n")
          ; print (exnMessage exn^"\n"))

   fun load file =
      loop (Parse.parse 
              ((*Stream.map (fn t => (print ("Tok: "^(#1 t)^"\n"); t)) *)
                 (Lex.tokenizeFile file)))

   fun read str = 
      loop (Parse.parse 
              ((*Stream.map (fn t => (print ("Tok: "^(#1 t)^"\n"); t)) *)
                 (Lex.tokenizeString str)))

   fun reset () = Handle.reset ()
end
