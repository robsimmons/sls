signature HANDLE =
sig
   type handler =
      {syntax: string PosDatum.t -> unit,

       (* t:K:kind. *)
       (* a:K:kind. *)
       (* c:τ:type. *)
       condec: Symbol.symbol * Exp.t * Exp.t -> unit,

       (* r:A:prop. *)
       rule: Symbol.symbol * NegProp.t -> unit}
       
   val register: string -> int -> handler -> unit
   val syntax: string PosDatum.t -> unit
   val condec: Symbol.symbol * Exp.t * Exp.t -> unit
   val rule: Symbol.symbol * NegProp.t -> unit
end

structure Handle:> HANDLE = 
struct
   type handler =
      {rawsyntax: string PosDatum.t -> unit,
       condec: Symbol.symbol * Exp.t * Exp.t -> unit,
       rule: Symbol.symbol * NegProp.t -> unit}

   val table: (string * handler) list IntRedBlackDict.dict ref 
      = ref IntRedBlackDict.empty

   fun registerSyntax name order handler = 
      table := 
      IntRedBlackDict.insertMerge (!table) order
         [ (name, handler) ]
         (fn handlers => (name, handler) :: handlers)
   
   fun syntax datum = 
      IntRedBlackDict.foldl 
         (fn (_,handlers,()) => app (fn (_,f) => #syntax f datum) handlers)
         () (!table)

   fun condec datum = 
      IntRedBlackDict.foldl 
         (fn (_,handlers,()) => app (fn (_,f) => #condec f datum) handlers)
         () (!table)

   fun rule datum = 
      IntRedBlackDict.foldl 
         (fn (_,handlers,()) => app (fn (_,f) => #rule f datum) handlers)
         () (!table)
end
