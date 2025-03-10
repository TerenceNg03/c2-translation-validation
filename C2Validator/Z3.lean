import Lean.Data.RBTree
import C2Validator.ValError

open ValError

namespace Z3

inductive Z3TypeBasic where
| Int
| Long
| Bool
| SideEffect
deriving Ord, BEq

instance : ToString Z3TypeBasic where
  toString
        | .Int => "(_ BitVec 32)"
        | .Long => "(_ BitVec 64)"
        | .Bool => "Bool"
        | .SideEffect => "Int"


inductive Z3Type where
| Basic (val : Z3TypeBasic)
| Tuple (val : List Z3TypeBasic)
deriving BEq

instance : Ord Z3Type where
  compare
    | .Basic x, .Basic y   => compare x y
    | .Basic _, .Tuple _   => Ordering.lt
    | .Tuple _, .Basic _   => Ordering.gt
    | .Tuple x, .Tuple y   =>
      if List.lex x y λ x y ↦ compare x y == .lt then .lt else if x == y then .eq else .gt


instance : ToString Z3Type where
  toString
      | .Basic val => s!"{val}"
      | .Tuple arr =>
            let arr := arr.map (λ x ↦ s!"{x}")
            let arr := arr.map (λ t ↦ t.toList.filter Char.isAlphanum)
            let arr := arr.map String.mk
            let arr := String.intercalate "-" arr
            s!"T-{arr}"

def ZInt := Z3Type.Basic Z3TypeBasic.Int
def ZLong := Z3Type.Basic Z3TypeBasic.Long
def ZBool := Z3Type.Basic Z3TypeBasic.Bool
def ZSideEffect := Z3Type.Basic Z3TypeBasic.SideEffect


inductive Term where
| Var (name : String)
| IdentitySideEffect
| Int (val : Int)
| Long (val : Int)
| True
| False
| Mk (ty : Z3Type) (params : List Term)
| Index (t : Term) (idx : Nat)
| Eq (t1 : Term) (t2: Term)
| If (cond : Term) (t1 : Term) (t2: Term)
| Not (b : Term)
| And (t1 : Term) (t2 : Term)
| AndAll (ts: List Term)
| Add (t1 : Term) (t2 : Term)
| Sub (t1 : Term) (t2 : Term)
| Shl (t1 : Term) (t2 : Term)
| Shr (t1 : Term) (t2 : Term)
| Mul (t1 : Term) (t2 : Term)
| Div (t1 : Term) (t2 : Term)
| L2I (t: Term)
| I2L (t: Term)
| App (func: String) (params : List Term)

partial def toStrTerm : Term → String
      | .Var t => t
      | .Int v => s!"#x{v.toInt32.toBitVec.toHex}"
      | .IdentitySideEffect => "0"
      | .Long v => s!"#x{v.toInt64.toBitVec.toHex}"
      | .True => "true"
      | .False => "false"
      | .Mk ty params =>
        let params := String.intercalate " " $ params.map toStrTerm
        s!"(mk-{ty} {params})"
      | .Index t n => s!"(_{n} {toStrTerm t})"
      | .Eq t1 t2 => s!"(= {toStrTerm t1} {toStrTerm t2})"
      | .If cond t1 t2 => s!"(if {toStrTerm cond} {toStrTerm t1} {toStrTerm t2})"
      | .Not b => s!"(not {toStrTerm b})"
      | .And t1 t2 => s!"(and {toStrTerm t1} {toStrTerm t2})"
      | .AndAll ts =>
          let ts := String.intercalate " " $ ts.map λ x ↦ s!"\n{toStrTerm x}"
          s!"(and {ts})"
      | .Add t1 t2 => s!"(bvadd {toStrTerm t1} {toStrTerm t2})"
      | .Sub t1 t2 => s!"(bvsub {toStrTerm t1} {toStrTerm t2})"
      | .Mul t1 t2 => s!"(bvmul {toStrTerm t1} {toStrTerm t2})"
      | .Div t1 t2 => s!"(bvsdiv {toStrTerm t1} {toStrTerm t2})"
      | .Shl t1 t2 => s!"(bvshl {toStrTerm t1} {toStrTerm t2})"
      | .Shr t1 t2 => s!"(bvashr {toStrTerm t1} {toStrTerm t2})"
      | .I2L t => s!"((_ sign_extend 32) {toStrTerm t})"
      | .L2I t => s!"((_ extract 31 0) {toStrTerm t})"
      | .App func params =>
        let params := String.intercalate " " $ params.map toStrTerm
        s!"({func} {params})"

instance : ToString Term where
  toString := toStrTerm

inductive Stat where
| Assert (x : Term)
| DeclVar (name : String) (ty : Z3Type)
| DeclDataType (ty : Z3Type)
| DeclFunc (name : String) (params: List Z3Type) (ret: Z3Type)
| CheckSAT
| GetModel

instance : ToString Stat where
  toString
    | .Assert x => s!"(assert {x})"
    | .DeclVar name ty => s!"(declare-const {name} {ty})"
    | .DeclDataType ty@(.Tuple ts)=>
        let constructors := (ts.zipIdx 1).map (λ (t, idx) ↦ s!"(_{idx} {t})")
        let constructors := String.intercalate " " constructors
        s!"(declare-datatypes () (({ty} (mk-{ty} {constructors}))))"
    | .DeclDataType _ => ""
    | .DeclFunc name params ret =>
      let params := String.intercalate " " $ params.map λ param ↦ s!"{param}"
      s!"(declare-fun {name} ({params}) {ret})"
    | .CheckSAT => "(check-sat)"
    | .GetModel => "(get-model)"

structure Program where
    (types : Lean.RBTree Z3Type compare)
    (funcs: Lean.RBMap String (List Z3Type × Z3Type) compare)
    (vars : Lean.RBMap String Z3Type compare)
    (precondition : List Term)
    (postcondition : List Stat)
    (parameter : List Stat)
    (outputPre : List Term)
    (outputPost : List Term)

def Program.empty : Z3.Program :=
    {types := default
    , funcs := (Lean.RBMap.fromList [("join", ([ZSideEffect, ZSideEffect], ZSideEffect))] compare)
    , vars := default
    , precondition := default
    , postcondition := default
    , parameter := default
    , outputPre := default
    , outputPost := default
    }

def collectSideEffects : List Term →  Term
  | [] => .IdentitySideEffect
  | (x::xs) => .App "join" [x, collectSideEffects xs]

def axioms : String := "(assert (forall ((x Int)) (= x (join x 0))))\n(assert (forall ((x Int)) (= x (join 0 x))))"

instance : ToString Program where
  toString p :=
  let types := p.types.toList.map Stat.DeclDataType
  let funcs := p.funcs.toList.map λ (x,y,z) ↦ Stat.DeclFunc x y z
  let vars := p.vars.toList.map $ Function.uncurry Stat.DeclVar
  let oPre := collectSideEffects p.outputPre
  let oPost := collectSideEffects p.outputPost
  let postrequisite := Term.AndAll $ Term.Eq oPre oPost :: p.precondition
  let vc := Stat.Assert $ .Not postrequisite
  let join (xs: List Stat) := String.intercalate "\n" $ xs.map λ x ↦ s!"{x}"
  s!"; Type Declarations\n{join types}\n\n"
    ++ s!"; Function Declarations\n{join funcs}\n\n"
    ++ s!"; Side Effect Axioms\n{axioms}\n\n"
    ++ s!"; Variable Declarations\n{join vars}\n\n"
    ++ s!"; VC Parameters\n{join p.parameter}\n\n"
    ++ s!"; VC Postconditions\n{join p.postcondition}\n\n"
    ++ s!"; VC\n{vc}\n\n"
    ++ s!"{Stat.CheckSAT}\n{Stat.GetModel}"

infixl:65 "∨" => Program.join

def validate (path : System.FilePath) (program : Program) : IO (Error PUnit) := do
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
    then pure $ pure ()
  else if "sat".isPrefixOf output
    then do
      let outputFile := path.withExtension "ce.smt"
      IO.FS.writeFile outputFile (output.drop 4)
      pure $ throw $ ValError.CounterExample outputFile
  else if "timeout".isPrefixOf output
    then pure $ throw $ ValError.Timeout
  else pure $ throw $ ValError.Z3 output
