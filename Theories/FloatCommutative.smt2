(set-option :dump_models true)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)

; Variable Declarations
(declare-const x Float32)
(declare-const y Float32)
(declare-const z1 Float32)
(declare-const z2 Float32)

; VC Parameters
(assert (= z1 (fp.add roundNearestTiesToEven y x)))
(assert (= z2 (fp.add roundNearestTiesToEven x y)))
(assert (not (= z1 z2)))

(check-sat)