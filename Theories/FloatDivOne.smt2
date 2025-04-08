
(set-option :dump_models true)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :pp.fp_real_literals true)

; Variable Declarations
(declare-const x Float32)
(declare-const y Float32)
(declare-const z2 Float32)

; VC Parameters
(assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= z2 (fp.div roundNearestTiesToEven y x)))
(assert (not (= y z2)))

(check-sat)