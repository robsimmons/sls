ty: type.
arrow: ty -> ty -> ty.
base: ty.

atom: type.
norm: type.
app: atom -> norm -> atom.
anno: norm -> ty -> atom.
lam: (atom -> norm) -> norm.
inc: atom -> norm.

check: norm -> ty -> type.

synth: atom -> ty -> type.

of/app: 
  synth (app R N) T2
    <- synth R (arrow T1 T2)
    <- check N T1.

of/anno:
  synth (anno N T) T
    <- check N T.

of/lam:
  check (lam \x. N x) (arrow T1 T2)
    <- Pi x:atom. synth x T1 -> check (N x) T2.

of/inc:
  check (inc R) base 
    <- synth R base.

foo: (atom -> atom -> atom -> atom -> atom -> norm) -> prop.
bar: foo (\foo. \foo. \bar1. \bar1. \bar1. inc bar1).

baz: norm -> prop.
bee: baz (lam (\x. E x)).