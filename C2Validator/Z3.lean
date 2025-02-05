import Lean.Data.RBTree
import C2Validator.ValError

open ValError

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

def validate (path : System.FilePath) (program : Program) : IO (Error PUnit) := do
  IO.println s!"[INFO] Generating SMT file..."
  let path ← IO.FS.realPath path
  let smt := path.withExtension "smt"
  IO.FS.writeFile smt s!"{program}"
  IO.println s!"[INFO] Running Z3 prover..."
  let command : IO.Process.SpawnArgs :=
  { cmd := "z3"
  , args := #[s!"{smt}"]
  , stdout := .piped
  }
  let child ← IO.Process.spawn command
  let rec wait t := do
    let code ← IO.Process.Child.tryWait child
    match code with
      | some code =>
        let out ← child.stdout.readToEnd
        match code with
        | 0 => pure $ throw $ ValError.CounterExample out
        | 127 => pure ∘ throw $ ValError.Plain "`z3` is not executable."
        | 1 => pure $ pure ()
        | x => pure ∘ throw $ ValError.Plain "z3 command returns code {x}."
      | none =>
        if t ≤ 0 then
          do
            IO.Process.Child.kill child
            pure $ throw ValError.Timeout
        else
          do
            IO.sleep 100
            wait (t - 100)
  wait 5000
