nat: type.
z: nat.
s: nat -> nat.

exp: type.

;; Lambda calculus
lam: (exp -> exp) -> exp.
app: exp -> exp -> exp.

;; Mini-ML
fix: (exp -> exp) -> exp.
pair: exp -> exp -> exp.
fst: exp -> exp.
snd: exp -> exp.
zero: exp.
succ: exp -> exp.
case: exp -> exp -> (exp -> exp) -> exp.

;; Temporal
next: exp -> exp.
prev: exp -> exp.