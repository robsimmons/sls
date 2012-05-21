exp: type.
lam: (exp -> exp) -> exp.
app: exp -> exp -> exp.
junk: exp.


#|
  Example 1: 
  Straightforward encoding of natural 
  semantics. 
|#

value: exp -> prop.
vlam: value (lam \x. E x).

ev: exp -> exp -> prop. 
#mode ev + -.

ev/lam: 
  ev (lam \x. E x) (lam \x. E x).
ev/app: 
  ev (app E1 E2) V.
    <<- ev E1 (lam \x. E x)
    <<- ev E2 V2
    <<- ev (E V2) V.


#|
  Example 2: 
  Derivations carry a witness that they 
  are values. 
|#

evd: exp -> {v: exp} value v -> prop.
#mode evd + - -.

evd/lam: 
  evd (lam \x. E x) (lam \x. E x) vlam.

evd/app: 
  evd (app E1 E2) V D
    <<- ev E1 (lam \x. E x) vlam
    <<- ev E2 V2 _
    <<- ev (E V2) V D.


#|
  Example 3:
  Stuck states happen elsewhere, using
  equality.
|#

ev': exp -> exp -> prop.
#mode ev' + -.

ev'/lam:
  ev (lam \x. E x) (lam \x. E x).
ev'/app:
  ev (app E1 E2) V
    <<- ev E1 V1
    <<- ev E2 V2
    <<- V1 == lam \x. E x
    <<- ev (E V2) V.      
