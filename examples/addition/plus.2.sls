#|
   To get Frank's machine from 
   http://www.cs.cmu.edu/~fp/courses/15816-s12/lectures/16-ordchain.pdf
   we observe that in specification plus.1.sls, a cont carrybit, once 
   evaluated, produces a (cont append0) frame. We can instead produce the
   (cont append0) frame early, in rule plus/b11, instead of late, in rule
   plus/carry (renamed to cont/carry).
|#

frame: type.
append0: frame.
append1: frame.
carry: frame.  

cont: frame -> prop ord.
inc: nat -> prop ord.
retn: nat -> prop ord.
plus: nat -> nat -> prop ord.

inc/eps:    inc eps >-> {retn (c eps b1)}.
inc/b0:     inc (c N b0) >-> {retn (c N b1)}.
inc/b1:     inc (c N b1) >-> {inc N * cont append0}.

plus/eN:    plus eps N >-> {retn N}.
plus/Me:    plus N eps >-> {retn N}.

plus/b00:   plus (c M b0) (c N b0) >-> {plus M N * cont append0}.
plus/b01:   plus (c M b0) (c N b1) >-> {plus M N * cont append1}.
plus/b10:   plus (c M b1) (c N b0) >-> {plus M N * cont append1}.
plus/b11:   plus (c M b1) (c N b1) >-> {plus M N * cont carry * cont append0}.

cont/0:     retn R * cont append0 >-> {retn (c R b0)}.
cont/1:     retn R * cont append1 >-> {retn (c R b1)}.
cont/carry: retn K * cont carry >-> {inc K}.
