;; First refinement: eliminate redundent frame constructors and rules

frame: type.
cont: frame -> prop ord.
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
recomp: ctx -> exp -> exp -> prop.
recomp/emp: recomp cemp E E.
recomp/app: recomp C E1 E1' -> recomp (capp C E2) E1 (app E1' E2).
recomp/let: recomp C E E' -> recomp (clet X E1 C) E (let X E1 E').
recomp/var: recomp Cx (var X) E -> recomp C E1 E1' -> recomp (cvar X C Cx) E1 (let X E1' E).

;; Derived frame constructors
;; (ie, now just: ([] E) | (let x = E in []) | (let x = [] in C[x]))

app1: exp -> frame.
let1: ide -> exp -> frame.
eq1:  ide -> ctx -> frame.

;; All of the following contexts are mapped identically to let1
;; (with lam2 being wrapped in a lam)

; lam1: exp -> ide -> frame.
; let2: ide -> exp -> frame.
; lam2: ide -> (exp -> exp) -> frame.
; let3: ide -> exp -> frame.

;; Derived evaluation relation and rules

ev_eval:  exp -> ide -> prop ord.
ev_apply: res -> exp -> ide -> prop ord.
ev_bind:  ide -> exp -> res -> ide -> prop ord.
ev_force: ide -> res -> ctx -> ide -> prop ord.
retn:     ide -> res -> prop ord.

eval/var: ev_eval (var X)         Xs >-> {retn Xs (rvar X cemp)}.
eval/lam: ev_eval (lam (\x. E x)) Xs >-> {retn Xs (rans (lam (\x. E x)))}.
eval/app: ev_eval (app E1 E2)     Xs >-> {ev_eval E1 Xs * cont (app1 E2)}.
eval/let: ev_eval (let X E1 T)    Xs >-> {ev_eval T Xs * cont (let1 X E1)}.

apply/lam: ev_apply (rans (lam (\x. E x))) E2 X  >-> {ev_eval (E (var X)) (s X) * cont (let1 X E2)}.
apply/let: ev_apply (rans (let X E1 A))    E2 Xs >-> {ev_apply (rans A) E2 Xs * cont (let1 X E1)}.
apply/var: ev_apply (rvar X C)             E2 Xs >-> {retn Xs (rvar X (capp C E2))}.

bind/ans: ev_bind X E2 (rans A)   Xs >-> {retn Xs (rans (let X E2 A))}.
bind/eq:  ev_bind X E2 (rvar X C) Xs >-> {ev_eval E2 Xs * cont (eq1 X C)}.
bind/neq: ev_bind X E2 (rvar Y C) Xs >-> {retn Xs (rvar Y (clet X E2 C))}.

force/lam: ev_force X (rans (lam (\x. E x))) C Xs >-> All E': exp. recomp C (lam (\x. E x)) E' -> {ev_eval E' Xs * cont (let1 X (lam (\x. E x)))}.
force/let: ev_force X (rans (let Y E1 A))    C Xs >-> {ev_force X (rans A) C Xs * cont (let1 Y E1)}.
force/var: ev_force X (rvar Y C1)            C Xs >-> {retn Xs (rvar Y (cvar X C1 C))}.

eval/app1:  retn Xs' R1 * cont (app1 E2)   >-> {ev_apply R1 E2 Xs'}.
eval/let1:  retn Xs' R  * cont (let1 X E1) >-> {ev_bind X E1 R Xs'}.
bind/eq1:   retn Xs' R2 * cont (eq1 X C)   >-> {ev_force X R2 C Xs'}.

; apply/lam1: retn Xs' R  * cont (lam1 E2 X) >-> {ev_bind X E2 R Xs'}.
; apply/let1: retn Xs' R  * cont (let2 X E1) >-> {ev_bind X E1 R Xs'}.
; force/lam1: retn Xs' R  * cont (lam2 X E)  >-> {ev_bind X (lam (\x. E x)) R Xs'}.
; force/let1: retn Xs' R  * cont (let3 Y E1) >-> {ev_bind Y E1 R Xs'}.
