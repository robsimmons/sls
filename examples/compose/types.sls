exp: type.
frame: type.
locvar: type.
channel: type.
dest: type.


#| Pure fragment, defined in pure-natsem.sls |#

lam: (exp -> exp) -> exp.                ; λx.e
app: exp -> exp -> exp.                  ; e₁(e₂)

true: exp.                               ; tt
false: exp.                              ; ff
ite: exp -> exp -> exp -> exp.           ; if e then et else ef
zero: exp.                               ; z
succ: exp -> exp.                        ; s(e)
case: exp -> exp -> (exp -> exp) -> exp. ; case e of z => ez | s x => es
unit: exp.                               ; <>
pair: exp -> exp -> exp.                 ; <e₁, e₂>
fst: exp -> exp.                         ; π₁ e
snd: exp -> exp.                         ; π₂ e

fix: (exp -> exp) -> exp.                ; fix x.e


#| Imperative fragment, defined in imp-ordmachine.sls |#

loc: locvar -> exp.                      ; (no concrete syntax)
ref: exp -> exp.                         ; ref e
get: exp -> exp.                         ; !e
set: exp -> exp -> exp.                  ; e₁ := e₂

issusp: locvar -> exp.                   ; (no concrete syntax)
thunk: (exp -> exp) -> exp.              ; thunk x.e
force: exp -> exp.                       ; force e


#| Sequential control fragment, defined in control-ordmachine.sls |#

raise: exp -> exp.                       ; raise e
handle: exp -> (exp -> exp) -> exp.      ; try e catch x.ef 

raise1: frame.


#| Concurrent fragment, defined in concur-natsem.sls & concur-dest.sls |#

letpar: exp -> exp -> (exp -> exp -> exp) -> exp. 
                                         ; let x = e₁ | y = e₂ in e

spawn: exp -> exp.                       ; spawn e
exit: exp.                               ; exit.
newch: exp.                              ; channel
chan: channel -> exp.                    ; (no concrete syntax)
sync: exp -> exp.                        ; sync e
send: exp -> exp -> exp.                 ; sync c e
recv: exp -> exp.                        ; recv c
always: exp -> exp.                      ; always e
choose: exp -> exp -> exp.               ; e1 + e2
never: exp.                              ; 0 
wrap: exp -> (exp -> exp) -> exp.        ; wrap e in x.e'

letpar1: (exp -> exp -> exp) -> frame.   
sync1: frame.