(* Magic-character enabled lexing: LexCorTwelf *)
(* Rob Simmons *)

(* Scheme-like lexing:
 * 
 * `#' is special:
 * `#|...|#` is a nestable multiline comment
 * `#' followed by anything else is a token
 * `;...\n` is a single-line comment
 * 
 * Reserved characters (`reserved c` returns `true`) are lexed individually.
 * All other characters are tokenized until whitespace, a reserved character,
 * or whitespaces arises. *)
structure LexSharp = 
struct
   type to_resume = int
   val initial = 0
   exception Resumable of to_resume * Coord.coord

   fun tokenize reserved n coord cs = 
   let
      (* Invariant: n > 0. `coord` is the last seen coordinate *)
      (* Returns the stream after reading n closing braces *)
      fun multi (coord, cs) n = 
         case Stream.front cs of
            Stream.Nil => raise Resumable (n, coord)
          | Stream.Cons ((#"|", coord'), cs) =>
              (case Stream.front cs of 
                  Stream.Nil => raise Resumable (n, coord')
                | Stream.Cons ((#"#", coord''), cs) => 
                     if n = 1 then (coord'', cs) else multi (coord', cs) (n-1) 
                | _ => multi (coord', cs) n)
          | Stream.Cons ((_, coord'), cs) => multi (coord', cs) n

      (* Returns the stream after reading `\n` (or an end-of-file). *)
      fun single (coord, cs) = 
         case Stream.front cs of
            Stream.Nil => (coord, cs)
          | Stream.Cons ((#"\n", coord'), cs) => (coord', cs)
          | Stream.Cons ((_, coord'), cs) => single (coord', cs)

      (* Looks for the beginning of a token *)
      fun next (coord, cs) () = 
         case Stream.front cs of
            Stream.Nil => Stream.Nil
          | Stream.Cons ((#"#", coord'), cs) => sharp coord (coord', cs)
          | Stream.Cons ((#";", coord'), cs) => next (single (coord', cs)) ()
          | Stream.Cons ((#"\"", coord'), cs) => 
               string coord' [#"\""] (coord', cs) ()
          | Stream.Cons ((c, coord'), cs) =>
               if reserved c 
               then Stream.Cons ((str c, Pos.pos coord coord'), 
                                 Stream.lazy (next (coord', cs)))
               else if Char.isSpace c
               then next (coord', cs) ()
               else token coord [c] (coord', cs)

      (* Handles a stream following a sharp sign *)
      and sharp sharp_coord (coord, cs) =
         case Stream.front cs of
            Stream.Nil => Stream.Nil
          | Stream.Cons ((#"|", coord'), cs) => next (multi (coord', cs) 1) ()
          | Stream.Cons ((c, coord'), cs) => 
               if Char.isSpace c 
               then next (single (coord', cs)) ()
               else token sharp_coord [c, #"#"] (coord', cs) 
      
      (* Looks for the completion of a non-reserved token *)
      and token start chars (coord, cs) = 
         case Stream.front cs of
            Stream.Nil =>
               Stream.Cons ((implode (rev chars), Pos.pos start coord), 
                            Stream.eager Stream.Nil)
          | Stream.Cons ((#"\^D", coord'), cs) => Stream.Nil
          | Stream.Cons ((#"#", coord'), cs) =>
               Stream.Cons ((implode (rev chars), Pos.pos start coord), 
                            Stream.lazy (fn () => sharp coord (coord', cs)))
          | Stream.Cons ((#";", coord'), cs) => 
               Stream.Cons ((implode (rev chars), Pos.pos start coord),
                            Stream.lazy (next (single (coord', cs))))
          | Stream.Cons ((#"\"", coord'), cs) => 
               Stream.Cons ((implode (rev chars), Pos.pos start coord),
                            Stream.lazy (string coord' [#"\""] (coord', cs)))
          | Stream.Cons ((c, coord'), cs) => 
               if Char.isSpace c 
               then Stream.Cons ((implode (rev chars), Pos.pos start coord), 
                      Stream.lazy (next (coord', cs)))
               else if reserved c 
               then Stream.Cons ((implode (rev chars), Pos.pos start coord),
                      Stream.eager
                        (Stream.Cons ((str c, Pos.pos coord coord'),
                           Stream.lazy (next (coord', cs)))))
               else token start (c :: chars) (coord', cs)

      (* XXX add escape chars *)
      and string quote_coord chars (coord, cs) () =
         case Stream.front cs of 
            Stream.Nil => raise Fail "End of file in string"
          | Stream.Cons ((#"\^D", coord'), cs) => 
               raise Fail "End of file in string"
          | Stream.Cons ((#"\"", coord'), cs) =>
               Stream.Cons ((implode (rev chars), Pos.pos quote_coord coord'),
                  Stream.lazy (next (coord', cs)))
          | Stream.Cons ((c, coord'), cs) => 
               string quote_coord (c :: chars) (coord', cs) ()
   in 
      if n = 0 
      then Stream.lazy (next (coord, cs))
      else Stream.lazy (next (multi (coord, cs) n))
   end
end

(* SLS lexer *)
structure Lex =
MakeLexer
  (struct
      open LexSharp
      val tokenize = 
         tokenize (fn #"(" => true | #")" => true | #":" => true
                    | #"[" => true | #"]" => true | #"." => true
                    | #"{" => true | #"}" => true | #"\\" => true
                    | #"!" => true | #"@" => true | #"$" => true
                    | _ => false)
   end)
