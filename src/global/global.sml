(* Global parameters *)
(* Author: Frank Pfenning *)

structure Global :> GLOBAL =
struct

  val chatter = ref 3
  val maxCid = 9999
  val maxMid = 999
  val maxCSid = 49
  val doubleCheck = ref true
  val unsafe = ref false

  fun chPrint n s = if !chatter >= n then print (s ()) else ()
end;  (* structure Global *)
