;; Third refinement: split retn into retn_ans and retn_var

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

app1: exp -> frame.
let1: ide -> exp -> frame.
eq1:  ide -> ctx -> frame.

;; Derived evaluation relation and rules

ev_eval:  exp -> ide -> prop ord.
retn_ans: ide -> exp -> prop ord.
retn_var: ide -> ide -> ctx -> prop ord.

;; These rules are the <_,_>term rules of [Fig. 7, Danvy-al:TCS12]

eval/var: ev_eval (var X)         Xs >-> {retn_var Xs X cemp}.
eval/lam: ev_eval (lam (\x. E x)) Xs >-> {retn_ans Xs (lam (\x. E x))}.
eval/app: ev_eval (app E1 E2)     Xs >-> {ev_eval E1 Xs * cont (app1 E2)}.
eval/let: ev_eval (let X E1 T)    Xs >-> {ev_eval T Xs  * cont (let1 X E1)}.

;; These rules are the <_,_>context rules of [Fig. 7, Danvy-al:TCS12]

apply/lam: retn_ans X  (lam (\x. E x)) * cont (app1 E2)   >-> {ev_eval (E (var X)) (s X) * cont (let1 X E2)}.
apply/let: retn_ans Xs (let X E1 A)    * cont (app1 E2)   >-> {retn_ans Xs A * cont (app1 E2) * cont (let1 X E1)}.
bind/ans:  retn_ans Xs A               * cont (let1 X E2) >-> {retn_ans Xs (let X E2 A)}.
force/lam: retn_ans Xs (lam (\x. E x)) * cont (eq1 X C)   >-> ({ev_eval E' Xs * cont (let1 X (lam (\x. E x)))}
                                                               <- recomp C (lam (\x. E x)) E').
force/let: retn_ans Xs (let Y E1 A)    * cont (eq1 X C)   >-> {retn_ans Xs A * cont (eq1 X C) * cont (let1 Y E1)}.

;; These rules are the <_,_>reroot rules of [Fig. 7, Danvy-al:TCS12]

bind/eq:   retn_var Xs X C  * cont (let1 X E2) >-> {ev_eval E2 Xs * cont (eq1 X C)}.
apply/var: retn_var Xs X C  * cont (app1 E2)   >-> {retn_var Xs X (capp C E2)}.
bind/neq:  retn_var Xs Y C  * cont (let1 X E2) >-> {retn_var Xs Y (clet X E2 C)}.
force/var: retn_var Xs Y C1 * cont (eq1 X C)   >-> {retn_var Xs Y (cvar X C1 C)}.
