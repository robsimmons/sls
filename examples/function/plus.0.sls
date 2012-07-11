;; Output of the automatic derivation from plus.sls
;; Some re-formatting, reordering, and indentation

frame: type.
cont: frame -> prop ord.
inc: nat -> prop ord.
retn: nat -> prop ord.
inc/eps: inc eps >-> {retn (c eps b1)}.
inc/0: inc (c N b0) >-> {retn (c N b1)}.
11: frame.
inc/11: retn R * cont 11 >-> {retn (c R b0)}.
inc/1: inc (c N b1) >-> {inc N * cont 11}.
plus: nat -> nat -> prop ord.
retn: nat -> prop ord.
plus/eN: plus eps N >-> {retn N}.
plus/Me: plus N eps >-> {retn M}.
b001: frame.
plus/b001: retn R * cont b001 >-> {retn (c R b0)}.
plus/b00: plus (c M b0) (c N b0) >-> {plus M N * cont b001}.
b011: frame.
plus/b011: retn R * cont b011 >-> {retn (c R b1)}.
plus/b01: plus (c M b0) (c N b1) >-> {plus M N * cont b011}.
b101: frame.
plus/b101: retn R * cont b101 >-> {retn (c R b1)}.
plus/b10: plus (c M b1) (c N b0) >-> {plus M N * cont b101}.
b111: frame.
b112: frame.
plus/b112: retn R * cont b112 >-> {retn (c R b0)}.
plus/b111: retn K * cont b111 >-> {inc K * cont b112}.
plus/b11: plus (c M b1) (c N b1) >-> {plus M N * cont b111}.
