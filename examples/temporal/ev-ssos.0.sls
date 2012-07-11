;; Output of the automatic derivation from ev.sls
;; Some re-formatting, reordering, and indentation

#| Frames and atomic propositions |#

frame: type.
app1: exp -> frame.
app2: (exp -> exp) -> frame.
pair1: exp -> frame.
pair2: exp -> frame.
fst1: frame.
snd1: frame.
succ1: frame.
case1: exp -> (exp -> exp) -> frame.

cont: frame -> prop ord.
eval: exp -> prop ord.
retn: exp -> prop ord.
var: exp -> prop pers.
casen: exp -> exp -> (exp -> exp) -> prop ord.
evn: nat -> exp -> exp -> prop. ;; Not operationalized!

#| Lambda calculus fragment - Time 0 |#

ev/lam:   eval (lam (\x. E x)) >-> {retn (lam (\x. E x))}.

ev/app:   eval (app E1 E2) >-> {eval E1 * cont (app1 E2)}.
ev/app1:  retn (lam (\x. E x)) * cont (app1 E2) >-> {eval E2 * cont (app2 E)}.
ev/app2:  retn V2 * cont (app2 E) >-> {eval (E V2)}.

#| Lambda calculus fragment - Time n+1 |#

ev/var':  evn N X X <-< var X.
ev/lam':  evn N (lam (\x. E x)) (lam (\x. V x))
           <-  (All x: exp. var x >-> evn N (E x) (V x)).
ev/app':  evn N (app E1 E2) (app V1 V2)
           <- evn N E1 V1
           <- evn N E2 V2.

#| Mini-ML fragment - Time 0 |#

ev/fix:   eval (fix (\x. E x)) >-> {eval (E (fix (\x. E x)))}.

ev/pair:  eval (pair E1 E2) >-> {eval E1 * cont (pair1 E2)}.
ev/pair1: retn V1 * cont (pair1 E2) >-> {eval E2 * cont (pair2 V1)}.
ev/pair2: retn V2 * cont (pair2 V1) >-> {retn (pair V1 V2)}.

ev/fst:   eval (fst E) >-> {eval E * cont fst1}.
ev/fst1:  retn (pair V X1) * cont fst1 >-> {retn V}.

ev/snd1:  retn (pair X1 V) * cont snd1 >-> {retn V}.
ev/snd:   eval (snd E) >-> {eval E * cont snd1}.

ev/zero:  eval zero >-> {retn zero}.

ev/succ1: retn V * cont succ1 >-> {retn (succ V)}.
ev/succ:  eval (succ E) >-> {eval E * cont succ1}.

ev/case1: retn V' * cont (case1 Ez Es) >-> {casen V' Ez (\x. Es x)}.
ev/case:  eval (case E Ez (\x. Es x)) >-> {eval E * cont (case1 Ez Es)}.
casen/z:  casen zero Ez (\x. Es x) >-> {eval Ez}.
casen/s:  casen (succ V') Ez (\x. Es x) >-> {eval (Es V')}.

#| Mini-ML fragment - Time n+1 |#

ev/fix':  evn N (fix (\x. E x)) (fix (\x. V x)).
           <- (All x: exp. var x >-> evn N (E x) (V x)).
ev/pair': evn N (pair E1 E2) (pair V1 V2)
           <- evn N E1 V1
           <- evn N E2 V2.
ev/fst':  evn N (fst E) (fst V).
           <- evn N E V.
ev/snd':  evn N (snd E) (snd V)
           <- evn N E V.
ev/zero': evn N zero zero.
ev/succ': evn N (succ E) (succ V) 
           <- evn N E V. 
ev/case': evn N (case E Ez (\x. Es x)) (case V Vz (\x. Vs x)).
           <- evn N E V 
           <- evn N Ez Vz
           <- (All x: exp. var x >-> evn N (Es x) (Vs X)).

#| Temporal fragment |# 

ev/next:  eval (next E) >-> All V: exp. !evn z E V 
           >-> {retn (next V)}.

ev/next': evn N (next E) (next V) 
           <- evn (s N) E V.
ev/prev:  evn z (prev E) V
           <- (eval E >-> {retn (next V)}).
ev/prev': evn (s N) (prev E) (prev V)
           <- evn N E V
