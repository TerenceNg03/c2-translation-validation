import Lean.Data.RBTree

namespace Z3

inductive IntTerm where
| Var (name : String)

instance : ToString IntTerm where
    toString | .Var t => t

inductive BoolTerm where
| EqI (t1 : IntTerm) (t2: IntTerm)
| Eq (r1 : String) (r2: String)
| Not  (b : BoolTerm)

instance : ToString BoolTerm where
  toString :=
    let rec toStr
      | .EqI t1 t2 => s!"(= {t1} {t2})"
      | .Eq s1 s2 => s!"(= {s1} {s2})"
      | .Not b => s!"(not {toStr b})"
    toStr

inductive Stat where
| Assert (x : BoolTerm)
| CheckSAT
| GetModel

instance : ToString Stat where
  toString
    | .Assert x => s!"(assert {x})"
    | .CheckSAT => "(check-sat)"
    | .GetModel => "(get-model)"

inductive Program where
| Program (intVars : Lean.RBTree String compare) (stats : Array Stat)

def Program.join (p₁ : Z3.Program) (p₂ : Z3.Program) : Z3.Program :=
  let .Program i₁ s₁ := p₁
  let .Program i₂ s₂ := p₂
  Program.Program (Lean.RBTree.union i₁ i₂) (Array.append s₁ s₂)

def Program.empty : Z3.Program :=
  Program.Program Lean.RBTree.empty Array.empty

instance : ToString Program where
  toString
  | .Program intVars stats =>
  let declInt xs x := s!"(declare-const {x} Int)\n{xs}"
  let decls := Lean.RBTree.fold declInt "" intVars
  let stats := Array.foldl (λ xs x ↦ s!"{xs}\n{x}") "" stats
  decls ++ stats


infixl:65 "∨" => Program.join
