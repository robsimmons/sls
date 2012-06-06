signature HANDLE =
sig
   type handler =
      {syntax: string PosDatum.t -> unit,

       (* t:K:kind. *)
       (* a:K:kind. *)
       (* c:τ:type. *)
       condec: Symbol.symbol * Exp.t * Exp.t -> unit,

       (* r:A:prop. *)
       rule: Symbol.symbol * NegProp.t -> unit,
       reset: unit -> unit}
       
   val register: string -> int -> handler -> unit
   val syntax: string PosDatum.t -> unit (* Called from frontend.sml *)
   val condec: Symbol.symbol * Exp.t * Exp.t -> unit (* Called from recon.sml *)
   val rule: Symbol.symbol * NegProp.t -> unit (* Called from recon.sml *)
   val reset: unit -> unit (* Called from frontend.sml *)
end

structure Handle:> HANDLE = 
struct
   type handler =
      {syntax: string PosDatum.t -> unit,
       condec: Symbol.symbol * Exp.t * Exp.t -> unit,
       rule: Symbol.symbol * NegProp.t -> unit,
       reset: unit -> unit}

   val table: (string * handler) list IntRedBlackDict.dict ref 
      = ref IntRedBlackDict.empty

   fun register name order handler = 
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

   fun reset () = 
      IntRedBlackDict.foldl 
         (fn (_,handlers,()) => app (fn (_,f) => #reset f ()) handlers)
         () (!table)
end
