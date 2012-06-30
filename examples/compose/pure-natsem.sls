#mode ev + -.
ev: exp -> exp -> prop.

ev/lam:   ev (lam \x. E x) (lam \x. E x).

ev/app:   ev (app E1 E2) V 
           <- ev E1 (lam \x. E x)
           <- ev E2 V2
           <- ev (E V2) V.

ev/true:  ev true true.

ev/false: ev false false. 

#mode selectb + + + -.
selectb: exp -> exp -> exp -> exp -> prop.
selectb/true: selectb true Et Ef Et.
selectb/false: selectb false Et Ef Ef.

ev/ite:   ev (ite E Et Ef) V
           <- ev E V'
           <- selectb V' Et Ef E'
           <- ev E' V.

ev/zero:  ev zero zero.

ev/succ:  ev (succ E) (succ V)
           <- ev E V.

#mode selectn + + + -.
selectn: exp -> exp -> (exp -> exp) -> exp -> prop.
selectn/zero: selectn zero Ez (\x. Es x) Ez.
selectn/succ: selectn (succ V) Ez (\x. Es x) (Es V).

ev/case:  ev (case E Ez \x. Es x) V
           <- ev E V'
           <- selectn V' Ez (\x. Es x) E'
           <- ev E' V.

ev/unit:  ev unit unit.

ev/pair:  ev (pair E1 E2) (pair V1 V2)
           <- ev E1 V1
           <- ev E2 V2.

ev/fst:   ev (fst E) V1
           <- ev E (pair V1 V2).

ev/snd:   ev (fst E) V2
           <- ev E (pair V1 V2).

ev/fix:   ev (fix \x. E x) V
           <- ev (E (fix \x. E x)) V.