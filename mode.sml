signature MODES =
sig
   val handler: Handle.handler
   val find: Symbol.symbol -> Mode.t list option
   val lookup: Symbol.symbol -> Mode.t list 
end

structure Modes =
struct
   val preModeTable: Mode.t list SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty
   val modeTable: Mode.t list SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty

   fun find s = SymbolRedBlackDict.find (!modeTable) s
   fun lookup s = SymbolRedBlackDict.lookup (!modeTable) s



   (* handleMode
    * 
    * The mode declaration must come before the proposition
    * declaration (contra Twelf), and adds the preliminary mode
    * structure to preModeTable. *)

   fun handleMode' (s, dats, pos) =
   let 
      fun readMode (PosDatum.Atom ("+", _)) = Mode.Input
        | readMode (PosDatum.Atom ("-", _)) = Mode.Output
        | readMode dat = 
             raise Fail ("Invalid mode: "^Pos.toString (PosDatum.pos dat))
   in
    ( preModeTable := 
         SymbolRedBlackDict.insertMerge (!preModeTable) s (map readMode dats)
            (fn modes' => 
                raise Fail ("Predicate '"^Symbol.toValue s^"' already \
                            \assigned mode"))
    ; print ("#mode "^Symbol.toValue s^" ")
    ; List.app (fn dat => (PosDatum.print dat)) dats
    ; print ".\n")
   end 

   fun handleMode (PosDatum.Atom (s,_) :: dats, pos) = 
       let val s' = Symbol.fromValue s
       in case Signature.find s' of
             SOME _ => raise Fail ("Predicate '"^s^"' already defined")
           | NONE => handleMode' (s', dats, pos)
       end
     | handleMode ([], pos) = 
          raise Fail ("No predicate and no modes given: "^Pos.toString pos)
     | handleMode (dat :: _, pos) =
          raise Fail ("Not a predicate: "^Pos.toString (PosDatum.pos dat))



   (* handleCondec
    *
    * When a proposition with declared mode is finally declared, we
    * check that the mode declaration made sense and put a real entry
    * into the mode table. *)

   fun handleCondec (s, k, class) =
   let
      fun dbModes ((Exp.NProp, []), db) = ([], db)
        | dbModes ((exp, md :: mds), db) =
            (case exp of 
                Exp.Pi (x, t, k) => 
                let
                   val (mds, db) = dbModes ((k, mds), db)
                   val db = Syntax.Assert.givenMode ((t, md), db)
                in if md = Mode.Output
                      andalso Syntax.Query.varMode db (x, Mode.Input)
                   then raise Fail ("Mode declaration for dependent '"^x
                                    ^"' expected to be input (+)")
                   else (md :: mds, db)
                end 
              | Exp.Pii (x, t, k) => 
                let
                   val (mds, db) = dbModes ((k, mds), db)
                   val md = 
                      if Syntax.Query.varMode db (x, Mode.Input)
                      then Mode.Input else Mode.Output 
                   val db = Syntax.Assert.givenMode ((t, md), db)
                in (md :: mds, db) 
                end
              | Exp.Arrow (t, k) => 
                let
                   val (mds, db) = dbModes ((k, mds), db)
                   val db = Syntax.Assert.givenMode ((t, md), db)
                in (md :: mds, db) 
                end
              | _ => raise Fail ("Too many mode arguments for '"
                                 ^Symbol.toValue s^"'"))
        | dbModes ((exp, []), db) = 
            (case exp of 
                Exp.Pi _ => raise Fail ("Not enough modes for '"
                                        ^Symbol.toValue s^"'")
              | Exp.Pii _ => raise Fail ("Not enough modes for '"
                                        ^Symbol.toValue s^"'")
              | Exp.Arrow _ => raise Fail ("Not enough modes for '"
                                        ^Symbol.toValue s^"'")
              | _ => raise Fail ("Modes can only be given to negative \
                                 \predicates; but '"^Symbol.toValue s
                                 ^"' is a constructor for '"
                                 ^PrettyPrint.exp false exp^"'"))

   in if not (Exp.eq (class, Exp.Knd)) then ()
      else case SymbolRedBlackDict.find (!preModeTable) s of 
              NONE => ()
            | SOME modes => 
                (modeTable := 
                    SymbolRedBlackDict.insert (!modeTable) s
                       (#1 (dbModes ((k, modes), Syntax.empty))))
   end 

   fun init () = 
      {syntax = 
          (fn (PosDatum.List [("mode", dats, pos)]) => handleMode (dats, pos)
            | _ => ()),
       condec = handleCondec,
       rule = ignore,
       reset = fn () => 
                 (preModeTable := SymbolRedBlackDict.empty 
                ; modeTable := SymbolRedBlackDict.empty)}
end
