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

   fun optional_annotation_binding extras = 
      Schema.MUST_SEE 
       [ (".", Schema.MAY_SEE ([], extras, ())),
         (":", Schema.MUST_SEE [ (".", Schema.MAY_SEE ([], extras, ())) ]) ]

   val sls_schema = 
      [
        series ["(", ")"],
        series ["{", "}"],

        ("All", optional_annotation_binding []),
        ("Pi", optional_annotation_binding []),
        ("Exists", optional_annotation_binding []),
        ("\\", optional_annotation_binding 
                  [">->", "->>", "-o", "->", "<-<", "<<-", "o-", "<-", "=="]),

        (* Fixity 1 *)
        ("&", Schema.DONE ()),
        
        (* Fixity 2 *)
        ("<-<", Schema.DONE ()),
        ("<<-", Schema.DONE ()),
        ("o-", Schema.DONE ()),
        ("<-", Schema.DONE ()),

        (* Fixity 3 *)
        ("->>", Schema.DONE ()),
        ("-o", Schema.DONE ()),
        ("->", Schema.DONE ()),
        (">->", Schema.DONE ()),

        (* Fixity 4 *)
        ("*", Schema.DONE ()),

        (* Fixity 5 *)
        ("==", Schema.DONE ()),
        ("!", Schema.DONE ()),
        ("@", Schema.DONE ()),
        ("$", Schema.DONE ()),

        (* Application is fixity 6 *)

        ("type", Schema.DONE ()),
        ("one", Schema.DONE ()),
        ("prop", Schema.MAY_SEE ([], [], ())),
        ("ord", Schema.DONE ()),
        ("lin", Schema.DONE ()),
        ("aff", Schema.DONE ()),
        ("pers", Schema.DONE ())
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
