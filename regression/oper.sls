;test 

#operationalize "oper-test.auto.sls" (plus ~> add_in add_out).

nat: type.
z: nat.
s: nat -> nat.

#mode plus + + -.
plus: nat -> nat -> nat -> prop.

pz: plus z N N.
ps: plus (s N) M (s P) <- plus N M P.

#operationalize stop.
