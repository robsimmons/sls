;; -*- mode: twelf; -*-

#operationalize "cbneed.auto.sls"
    (eval  ~> ev_eval  retn)
    (apply ~> ev_apply retn)
    (bind  ~> ev_bind  retn)
    (force ~> ev_force retn).

ide: type.
z: ide.
s: ide -> ide.

exp: type.
lam: (exp -> exp) -> exp.
app: exp -> exp -> exp.
var: ide -> exp.
let: ide -> exp -> exp -> exp.

ctx: type.
cemp: ctx.
capp: ctx -> exp -> ctx.
clet: ide -> exp -> ctx -> ctx.
cvar: ide -> ctx -> ctx -> ctx.

res: type.
rans: exp -> res.
rvar: ide -> ctx -> res.

#mode recomp + + -.
recomp: ctx -> exp -> exp -> prop.
recomp/emp: recomp cemp E E.
recomp/app: recomp (capp C E2) E1 (app E1' E2)
   <- recomp C E1 E1'.
recomp/let: recomp (clet X E1 C) E (let X E1 E')
   <- recomp C E E'.
recomp/var: recomp (cvar X C Cx) E1 (let X E1' E)
   <- recomp C E1 E1'
   <- recomp Cx (var X) E.

#mode eval + + - -.
eval: exp -> ide -> ide -> res -> prop.

#mode apply + + + - -.
apply: res -> exp -> ide -> ide -> res -> prop.

#mode bind + + + + - -.
bind: ide -> exp -> res -> ide -> ide -> res -> prop.

#mode force + + + + - -.
force: ide -> res -> ctx -> ide -> ide -> res -> prop.

eval/var: eval (var X) Xs Xs (rvar X cemp).
eval/lam: eval (lam \x. E x) Xs Xs (rans (lam \x. E x)).
eval/app: eval (app E1 E2) Xs Xs'' R
   <- eval E1 Xs Xs' R1
   <- apply R1 E2 Xs' Xs'' R.
eval/let: eval (let X E1 T) Xs Xs'' R'
   <- eval T Xs Xs' R
   <- bind X E1 R Xs' Xs'' R'.

apply/var: apply (rvar X C) E2 Xs Xs (rvar X (capp C E2)).
apply/lam: apply (rans (lam \x. E x)) E2 X Xs'' R'
   <- eval (E (var X)) (s X) Xs' R
   <- bind X E2 R Xs' Xs'' R'.
apply/let: apply (rans (let X E1 A)) E2 Xs Xs'' R'
   <- apply (rans A) E2 Xs Xs' R
   <- bind X E1 R Xs' Xs'' R'.

bind/ans: bind X E2 (rans A) Xs Xs (rans (let X E2 A)).
bind/eq: bind X E2 (rvar X C) Xs Xs'' R
   <- eval E2 Xs Xs' R2
   <- force X R2 C Xs' Xs'' R.
bind/neq: bind X E2 (rvar Y C) Xs Xs (rvar Y (clet X E2 C)).

force/lam: force X (rans (lam \x. E x)) C Xs Xs'' R'
   <- recomp C (lam \x. E x) E'
   <- eval E' Xs Xs' R
   <- bind X (lam \x. E x) R Xs' Xs'' R'.
force/let: force X (rans (let Y E1 A)) C Xs Xs'' R'
   <- force X (rans A) C Xs Xs' R
   <- bind Y E1 R Xs' Xs'' R'.
force/var: force X (rvar Y C1) C Xs Xs (rvar Y (cvar X C1 C)).

#operationalize stop.
