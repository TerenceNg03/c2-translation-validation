import Lean.Data.RBTree
import C2Validator.ValError

open ValError

namespace Z3

inductive Z3Type where
| Int
| Bool
deriving Inhabited, BEq

instance : ToString Z3Type where
  toString | .Int => "(_ BitVec 32)"
           | .Bool => "Bool"

inductive Term where
| Var (name : String)
| Eq (t1 : Term) (t2: Term)
| Not  (b : Term)
| AddI (t1 : Term) (t2 : Term)

instance : ToString Term where
  toString :=
    let rec toStr
      | .Var t => t
      | .Eq t1 t2 => s!"(= {toStr t1} {toStr t2})"
      | .Not b => s!"(not {toStr b})"
      | .AddI t1 t2 => s!"(bvadd {toStr t1} {toStr t2})"
    toStr

inductive Stat where
| Assert (x : Term)
| CheckSAT
| GetModel

instance : ToString Stat where
  toString
    | .Assert x => s!"(assert {x})"
    | .CheckSAT => "(check-sat)"
    | .GetModel => "(get-model)"

inductive Program where
| Program (vars : Lean.RBMap String Z3Type compare) (stats : Array Stat)

def Program.empty : Z3.Program :=
  Program.Program Lean.RBMap.empty Array.empty

instance : ToString Program where
  toString
  | .Program vars stats =>
  let decl xs x t := s!"(declare-const {x} {t})\n{xs}"
  let decls := Lean.RBMap.fold decl "" vars
  let stats := Array.foldl (λ xs x ↦ s!"{xs}\n{x}") "" stats
  decls ++ stats ++ "\n\n(check-sat)\n(get-model)"

infixl:65 "∨" => Program.join

def validate (path : System.FilePath) (program : Program) : ExceptT ValError IO PUnit := do
  IO.println s!"[INFO] Generating SMT file..."
  let path ← IO.FS.realPath path
  let smt := path.withExtension "smt"
  IO.FS.writeFile smt s!"{program}"
  IO.println s!"[INFO] Running Z3 prover..."
  let command : IO.Process.SpawnArgs :=
  { cmd := "z3"
  , args := #[s!"-T:5", s!"{smt}"]
  }
  let .mk _ output _ ← IO.Process.output command
  if "unsat".isPrefixOf output
    then pure ()
  else if "sat".isPrefixOf output
    then throw $ ValError.CounterExample (output.drop 4)
  else if "timeout".isPrefixOf output
    then throw $ ValError.Timeout
  else throw $ ValError.Z3 output
