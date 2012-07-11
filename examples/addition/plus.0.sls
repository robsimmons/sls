;; Output of the automatic derivation from plus.sls
;; Some re-formatting, reordering, and indentation

frame: type.
b11: frame. b001: frame. b112: frame.
b011: frame. b101: frame.
b111: frame.

cont: frame -> prop ord.
inc: nat -> prop ord.
retn: nat -> prop ord.
plus: nat -> nat -> prop ord.

inc/eps:   inc eps >-> {retn (c eps b1)}.
inc/b0:    inc (c N b0) >-> {retn (c N b1)}.
inc/b1:    inc (c N b1) >-> {inc N * cont b11}.

plus/eN:   plus eps N >-> {retn N}.
plus/Me:   plus N eps >-> {retn N}.

plus/b00:  plus (c M b0) (c N b0) >-> {plus M N * cont b001}.
plus/b01:  plus (c M b0) (c N b1) >-> {plus M N * cont b011}.
plus/b10:  plus (c M b1) (c N b0) >-> {plus M N * cont b101}.
plus/b11:  plus (c M b1) (c N b1) >-> {plus M N * cont b111}.
plus/b111: retn K * cont b111 >-> {inc K * cont b112}.

;; These three frames do the same thing: restore the bit 0 to the end
inc/b11:   retn R * cont b11  >-> {retn (c R b0)}.
plus/b001: retn R * cont b001 >-> {retn (c R b0)}.
plus/b112: retn R * cont b112 >-> {retn (c R b0)}.

;; These two frames do the same thing: restore the bit 1 to the end
plus/b011: retn R * cont b011 >-> {retn (c R b1)}.
plus/b101: retn R * cont b101 >-> {retn (c R b1)}.