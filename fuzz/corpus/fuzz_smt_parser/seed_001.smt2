(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (= (bvxor x x) (_ bv0 32)))
(check-sat)
