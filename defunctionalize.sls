structure Defunctionalize =
struct
   val db = Syntax.empty (* Caching *)

   val forwardChain: (Symbol.symbol * Symbol.symbol) 
                     SymbolRedBlackDict.dict ref = 
      ref SymbolRedBlackDict.empty

   val file: TextIO.outstream option ref = ref NONE

   fun print' s = Option.app (fn f => TextIO.output (f, s)) (!file)
