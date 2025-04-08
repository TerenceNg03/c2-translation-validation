
(set-option :dump_models true)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :pp.fp_real_literals true)

; Variable Declarations
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const mul1 (_ BitVec 16))
(declare-const mul2 (_ BitVec 16))
(declare-const z (_ BitVec 16))

; VC Parameters
(assert (= mul1 (bvmul (bvadd x y) z)))
(assert (= mul2 (bvadd (bvmul x z) (bvmul y z))))
(assert (not (= mul1 mul2)))

(check-sat)