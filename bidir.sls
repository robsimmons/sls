ty: type.
arrow: ty -> ty -> ty.
base: ty.

atom: type.
norm: type.
app: atom -> norm -> atom.
anno: norm -> ty -> atom.
lam: (atom -> norm) -> norm.
inc: atom -> norm.

check: norm -> ty -> prop.
#mode check + +.

synth: atom -> ty -> prop.
#mode synth + -.

#rule of/app: 
  synth (app R N) T2
    <- synth R (arrow T1 T2)
    <- check N T1.

#rule of/anno:
  synth (anno N T) T
    <- check N T.

#rule of/lam:
  check (lam \x. N x) (arrow T1 T2)
    <- All x:atom. synth x T1 -> check (N x) T2.

#rule of/inc:
  check (inc R) base 
    <- synth R base.