(set-option :dump_models true)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
; (set-option :pp.fp_real_literals true)
(set-option :pp.decimal true)

; Variable Declarations
(declare-const xDiv Float32)
(declare-const xMul Float32)
(declare-const y Float32)
(declare-const z1 Float32)
(declare-const z2 Float32)

; VC Parameters
; (assert (= y ((_ to_fp 8 24) roundNearestTiesToEven 11214)))
; (assert (= xDiv ((_ to_fp 8 24) roundNearestTiesToEven (^ 2 125))))
; (assert (= xMul (fp.div roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven 1) xDiv)))
; (assert (= z1 (fp.div roundNearestTiesToEven y xDiv)))
; (assert (= z2 (fp.mul roundNearestTiesToEven y xMul)))
; (assert (not (= z1 z2)))

(check-sat)