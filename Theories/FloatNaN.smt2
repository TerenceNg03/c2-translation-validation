
(set-option :dump_models true)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :solver.proof.log Theories/FloatNaN.proof.smt2)
(set-option :pp.fp_real_literals true)

; Variable Declarations
(declare-const x Float32)
(declare-const y Float32)
(declare-const z1 Float32)
(declare-const z2 Float32)

; VC Parameters
(assert (= x (fp #b1 #b11111111 #b11000000000000000000000)))
(assert (= z2 (fp.add roundNearestTiesToEven y x)))
(assert (not (= x z2)))

(check-sat)