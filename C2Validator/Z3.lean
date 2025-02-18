import Lean.Data.RBTree
import C2Validator.ValError

open ValError

namespace Z3

inductive Z3Type where
| Int
| Long
| Bool
deriving Inhabited, BEq

instance : ToString Z3Type where
  toString | .Int => "(_ BitVec 32)"
           | .Long => "(_ BitVec 64)"
           | .Bool => "Bool"

inductive Term where
| Var (name : String)
| Int (val : Int)
| Long (val : Int)
| True
| False
| Eq (t1 : Term) (t2: Term)
| If (cond : Term) (t1 : Term) (t2: Term)
| Not (b : Term)
| And (t1 : Term) (t2 : Term)
| Add (t1 : Term) (t2 : Term)
| Sub (t1 : Term) (t2 : Term)
| Shl (t1 : Term) (t2 : Term)
| Shr (t1 : Term) (t2 : Term)
| Mul (t1 : Term) (t2 : Term)
| Div (t1 : Term) (t2 : Term)
| L2I (t: Term)
| I2L (t: Term)
instance : ToString Term where
  toString :=
    let rec toStr
      | .Var t => t
      | .Int v => s!"#x{v.toInt32.toBitVec.toHex}"
      | .Long v => s!"#x{v.toInt64.toBitVec.toHex}"
      | .True => "true"
      | .False => "false"
      | .Eq t1 t2 => s!"(= {toStr t1} {toStr t2})"
      | .If cond t1 t2 => s!"(if {toStr cond} {toStr t1} {toStr t2})"
      | .Not b => s!"(not {toStr b})"
      | .And t1 t2 => s!"(and {toStr t1} {toStr t2})"
      | .Add t1 t2 => s!"(bvadd {toStr t1} {toStr t2})"
      | .Sub t1 t2 => s!"(bvsub {toStr t1} {toStr t2})"
      | .Mul t1 t2 => s!"(bvmul {toStr t1} {toStr t2})"
      | .Div t1 t2 => s!"(bvsdiv {toStr t1} {toStr t2})"
      | .Shl t1 t2 => s!"(bvshl {toStr t1} {toStr t2})"
      | .Shr t1 t2 => s!"(bvashr {toStr t1} {toStr t2})"
      | .I2L t => s!"((_ sign_extend 32) {toStr t})"
      | .L2I t => s!"((_ extract 31 0) {toStr t})"
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
| Program (vars : Lean.RBMap String Z3Type compare) (stats : Array Stat) (conditions : Array Term)

def Program.empty : Z3.Program :=
  Program.Program Lean.RBMap.empty Array.empty Array.empty

instance : ToString Program where
  toString
  | .Program vars stats conds =>
  let decl xs x t := s!"(declare-const {x} {t})\n{xs}"
  let decls := Lean.RBMap.fold decl "" vars
  let stats := Array.foldl (λ xs x ↦ s!"{xs}\n{x}") "" stats
  let conds := Array.foldl (λ xs x ↦ s!"{xs}\n    {x}") "" conds
  s!"{decls}{stats}\n\n(assert (not (and{conds}\n)))\n\n(check-sat)\n(get-model)\n"

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
