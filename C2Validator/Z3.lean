import Lean.Data.RBTree
import C2Validator.ValError
import C2Validator.SoN.Float

open ValError

namespace Z3

inductive Z3TypeBasic where
| Int
| Long
| FP32
| FP64
| Bool
| SideEffect
| Unit
deriving Ord, BEq

def basicTypeZ3Repr : Z3TypeBasic → String
| .Int => "(_ BitVec 32)"
| .Long => "(_ BitVec 64)"
| .FP32 => "Float32"
| .FP64 => "Float64"
| .Bool => "Bool"
| .SideEffect => "IO"
| .Unit => "Unit"

def basicTypeName : Z3TypeBasic → String
| .Int => "I32"
| .Long => "I64"
| .FP32 => "Float32"
| .FP64 => "Float64"
| .Bool => "Bool"
| .SideEffect => "IO"
| .Unit => "Unit"

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

def typeZ3Repr : Z3Type → String
| .Basic val => basicTypeZ3Repr val
| .Tuple arr =>
      let arr := arr.map basicTypeName
      let arr := arr.map (λ t ↦ t.toList.filter Char.isAlphanum)
      let arr := arr.map String.mk
      let arr := String.intercalate "-" arr
      s!"T-{arr}"

def typeName : Z3Type → String
| .Basic val => basicTypeName val
| .Tuple arr =>
      let arr := arr.map basicTypeName
      let arr := arr.map (λ t ↦ t.toList.filter Char.isAlphanum)
      let arr := arr.map String.mk
      let arr := String.intercalate "-" arr
      s!"T-{arr}"

def ZInt := Z3Type.Basic Z3TypeBasic.Int
def ZLong := Z3Type.Basic Z3TypeBasic.Long
def ZFP32 := Z3Type.Basic Z3TypeBasic.FP32
def ZFP64 := Z3Type.Basic Z3TypeBasic.FP64
def ZBool := Z3Type.Basic Z3TypeBasic.Bool
def ZSideEffect := Z3Type.Basic Z3TypeBasic.SideEffect

inductive Term where
| Var (name : String)
| IdentitySideEffect
| Int (val : Int)
| Long (val : Int)
| FP32 (val : SoN.FP32)
| FP64 (val : SoN.FP64)
| True
| False
| Mk (ty : Z3Type) (params : List Term)
| Index (t : Term) (idx : Nat)
| Eq (t1 : Term) (t2: Term)
| If (cond : Term) (t1 : Term) (t2: Term)
| Not (b : Term)
| AndLogic (t1 : Term) (t2 : Term)
| AndAll (ts: List Term)
| Add (t1 : Term) (t2 : Term)
| Sub (t1 : Term) (t2 : Term)
| Mul (t1 : Term) (t2 : Term)
| MulHiL (t1 : Term) (t2 : Term)
| Div (t1 : Term) (t2 : Term)
| AddFP (t1 : Term) (t2 : Term)
| SubFP (t1 : Term) (t2 : Term)
| MulFP (t1 : Term) (t2 : Term)
| DivFP (t1 : Term) (t2 : Term)
| And (t1 : Term) (t2 : Term)
| Or (t1 : Term) (t2 : Term)
| ShlI (t1 : Term) (t2 : Term)
| ShlL (t1 : Term) (t2 : Term)
| ShrI (t1 : Term) (t2 : Term)
| ShrL (t1 : Term) (t2 : Term)
| I2L (t: Term)
| I2F (t: Term)
| I2D (t: Term)
| L2I (t: Term)
| L2F (t: Term)
| L2D (t: Term)
| F2D (t: Term)
| F2I (t: Term)
| F2L (t: Term)
| D2I (t: Term)
| D2L (t: Term)
| D2F (t: Term)
| App (func: String) (params : List Term)

partial def toStrTerm : Term → String
      | .Var t => t
      | .Int v => s!"((_ int2bv 32) {v})"
      | .IdentitySideEffect => "(mkIO 0)"
      | .Long v => s!"((_ int2bv 64) {v})"
      | .FP32 s => s!"(fp #b{s.take 1} #b{(s.drop 1).take 8} #b{s.drop 9})"
      | .FP64 s => s!"(fp #b{s.take 1} #b{(s.drop 1).take 11} #b{s.drop 12})"
      | .True => "true"
      | .False => "false"
      | .Mk ty params =>
        let params := String.intercalate " " $ params.map toStrTerm
        s!"(mk-{typeName ty} {params})"
      | .Index t n => s!"(_{n} {toStrTerm t})"
      | .Eq t1 t2 => s!"(= {toStrTerm t1} {toStrTerm t2})"
      | .If cond t1 t2 => s!"(if {toStrTerm cond} {toStrTerm t1} {toStrTerm t2})"
      | .Not b => s!"(not {toStrTerm b})"
      | .AndLogic t1 t2 => s!"(and {toStrTerm t1} {toStrTerm t2})"
      | .AndAll ts =>
          let ts := String.intercalate " " $ ts.map λ x ↦ s!"\n{toStrTerm x}"
          s!"(and {ts})"
      | .Add t1 t2 => s!"(bvadd {toStrTerm t1} {toStrTerm t2})"
      | .Sub t1 t2 => s!"(bvsub {toStrTerm t1} {toStrTerm t2})"
      | .Mul t1 t2 => s!"(bvmul {toStrTerm t1} {toStrTerm t2})"
      | .And t1 t2 => s!"(bvand {toStrTerm t1} {toStrTerm t2})"
      | .Or t1 t2 => s!"(bvor {toStrTerm t1} {toStrTerm t2})"
      | .MulHiL t1 t2 => s!"((_ extract 127 64) (bvmul ((_ sign_extend 64) {toStrTerm t1}) ((_ sign_extend 64) {toStrTerm t2})))"
      | .Div t1 t2 => s!"(bvsdiv {toStrTerm t1} {toStrTerm t2})"
      | .AddFP t1 t2 => s!"(fp.add roundNearestTiesToEven {toStrTerm t1} {toStrTerm t2})"
      | .SubFP t1 t2 => s!"(fp.sub roundNearestTiesToEven {toStrTerm t1} {toStrTerm t2})"
      | .MulFP t1 t2 => s!"(fp.mul roundNearestTiesToEven {toStrTerm t1} {toStrTerm t2})"
      | .DivFP t1 t2 => s!"(fp.div roundNearestTiesToEven {toStrTerm t1} {toStrTerm t2})"
      | .ShlI t1 t2 => s!"(bvshl {toStrTerm t1} (bvand #x0000001f {toStrTerm t2}))"
      | .ShrI t1 t2 => s!"(bvashr {toStrTerm t1} (bvand #x0000001f {toStrTerm t2}))"
      | .ShlL t1 t2 => s!"(bvshl {toStrTerm t1} (bvand #x000000000000003f  {toStrTerm t2}))"
      | .ShrL t1 t2 => s!"(bvashr {toStrTerm t1} (bvand #x000000000000003f {toStrTerm t2}))"
      | .I2L t => s!"((_ sign_extend 32) {toStrTerm t})"
      | .F2L t | .D2L t => s!"((_ fp.to_sbv 64) roundNearestTiesToEven {toStrTerm t})"
      | .F2I t | .D2I t => s!"((_ fp.to_sbv 32) roundNearestTiesToEven {toStrTerm t})"
      | .L2I t => s!"((_ extract 31 0) {toStrTerm t})"
      | .I2F t | .L2F t | .D2F t=> s!"((_ to_fp 8 24) roundNearestTiesToEven {toStrTerm t})"
      | .I2D t | .L2D t | .F2D t => s!"((_ to_fp 11 53) roundNearestTiesToEven {toStrTerm t})"
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
    | .DeclVar name ty => s!"(declare-const {name} {typeZ3Repr ty})"
    | .DeclDataType ty@(.Tuple ts)=>
        let constructors := (ts.zipIdx 1).map (λ (t, idx) ↦ s!"(_{idx} {basicTypeZ3Repr t})")
        let constructors := String.intercalate " " constructors
        s!"(declare-datatypes () (({typeName ty} (mk-{typeName ty} {constructors}))))"
    | .DeclDataType _ => ""
    | .DeclFunc name params ret =>
      let params := String.intercalate " " $ params.map typeZ3Repr
      s!"(declare-fun {name} ({params}) {typeZ3Repr ret})"
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

def axioms : String := "(assert (forall ((x IO)) (= x (join x (mkIO 0)))))\n(assert (forall ((x IO)) (= x (join (mkIO 0) x))))"

def z3Opts : String := "(set-option :dump_models true)\n(set-option :pp.bv_literals false)\n\n"

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
  z3Opts
    ++ s!"; Type Declarations\
          \n(declare-datatypes () ((Unit mkUnit)))\
          \n(declare-datatypes () ((IO (mkIO (io Int)))))\
          \n{join types}\n\n"
    ++ s!"; Function Declarations\n{join funcs}\n\n"
    ++ s!"; Side Effect Axioms\n{axioms}\n\n"
    ++ s!"; Variable Declarations\n{join vars}\n\n"
    ++ s!"; VC Parameters\n{join p.parameter}\n\n"
    ++ s!"; VC Postconditions\n{join p.postcondition}\n\n"
    ++ s!"; VC\n{vc}\n\n"
    ++ s!"{Stat.CheckSAT}"

infixl:65 "∨" => Program.join

def runZ3 (path : System.FilePath) (timeout : Int) (smt : Bool): IO (Error PUnit) := do
  IO.println s!"[INFO] Running Z3 prover ..."
  let command : IO.Process.SpawnArgs :=
  { cmd := "z3"
  , args := #[s!"sat.smt={smt}", s!"-T:{timeout}", s!"{path}"]
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

def validate (path : System.FilePath) (program : Program) (timeout : Int): IO (Error PUnit) := do
  IO.println s!"[INFO] Generating SMT file ..."
  let path ← IO.FS.realPath path
  let smtFile := path.withExtension "smt"
  IO.FS.writeFile smtFile s!"{program}"
  IO.println s!"[INFO] Trying with default setting ..."
  let err ← runZ3 smtFile timeout false
  match err with
    | .error .Timeout => do
      IO.println s!"[INFO] Retrying with \"sat.smt=true\" option ..."
      runZ3 smtFile timeout true
    | _ => pure err
