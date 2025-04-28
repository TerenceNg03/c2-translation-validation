
(set-option :dump_models true)
(set-option :pp.fp_real_literals true)

; Variable Declarations
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const mul1 (_ BitVec 32))
(declare-const mul2 (_ BitVec 32))
(declare-const z (_ BitVec 32))

; VC Parameters
(assert (= mul1 (bvmul (bvmul x y) z)))
(assert (= mul2 (bvmul (bvmul x) (bvmul y z))))
(assert (not (= mul1 mul2)))

(check-sat)