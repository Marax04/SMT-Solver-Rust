(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 10.5))
(check-sat)
