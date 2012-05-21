signature PARSE =
sig
   exception Parse of Pos.t * string
   val parse: (string * Pos.t) Stream.stream -> string PosDatum.t Stream.stream
end

structure Parse:> PARSE = 
struct
   structure Parse = 
   ParseDatumFn
     (structure Datum = PosDatumFn (type whitespace = unit)
      structure Tok = StringHashable
      type name = unit)

   fun series [] = raise Fail "Invariant (series)"
     | series [x] = (x, Schema.DONE ())
     | series (x :: xs) = (x, Schema.MUST_SEE [ series xs ])

   fun series_longest [] = raise Fail "Invariant (series_longest)"
     | series_longest [x] = (x, Schema.MAY_SEE ([], ()))
     | series_longest (x :: xs) = (x, Schema.MUST_SEE [ series_longest xs ]) 

   val optional_annotation_binding = 
      Schema.MUST_SEE 
       [ (".", Schema.MAY_SEE ([], ())),
         (":", Schema.MUST_SEE [ (".", Schema.MAY_SEE ([], ())) ]) ]

   val sls_schema = 
      [
        series ["(", ")"],
        series ["{", "}"],

        ("All", optional_annotation_binding),
        ("Pi", optional_annotation_binding),
        ("Exists", optional_annotation_binding),
        ("\\", optional_annotation_binding)
      ]

   exception Parse of Pos.pos * string

   fun demand tok pos str = 
      case str of 
         Stream.Nil => 
            raise Parse (pos, "'"^tok^"' expected, found end of input")
       | Stream.Cons ((s, pos), str) =>  
            if s = tok then Stream.front str
            else raise Parse (pos, "'"^tok^"' expected, found '"^s^"'")

   (* Turns a stream of tokens into a stream of declarations. *)
   fun stream_transform str = 
      Stream.lazy (fn () => (
      case str of
         Stream.Nil => Stream.Nil
       | Stream.Cons ((s, pos), str) => 
           (if String.sub (s, 0) = #"#"
            then (* DIRECTIVE: do hierarchical parsing, then expect "." *)
            let 
               val s = String.extract (s, 1, NONE)
               val (ds, str) = Parse.parseMany (sls_schema, ["."]) 
                                  (Stream.front str)
               val ds_pos = PosDatum.poss ds
            in Stream.Cons 
                  (PosDatum.List [ (s, ds, Pos.union pos ds_pos) ],
                   stream_transform (demand "." ds_pos str)) 
            end
            else (* CONDEC: expect a ":", then do hierarchical parsing *) 
            let
               val str = demand ":" pos (Stream.front str)
               val (ds, str) = Parse.parseMany (sls_schema, ["."]) str
               val ds_pos = PosDatum.poss ds
            in 
               Stream.Cons
                  (PosDatum.List [ ("condec", [PosDatum.Atom (s, pos)], pos),
                                   (":", ds, ds_pos) ],
                   stream_transform (demand "." ds_pos str))
            end)))

   fun parse str = 
      Stream.lazy (fn () => (
      Stream.front (stream_transform (Stream.front str))))
end
