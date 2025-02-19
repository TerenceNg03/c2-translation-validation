import C2Validator.SoN
import C2Validator.Z3
import Lean.Data.RBTree
import C2Validator.ValError

open ValError
open SoN
open Z3

namespace VC

open Stat
open Term

inductive Stage where
| pre
| post

instance : ToString Stage where
  toString
    | .pre => "pre"
    | .post => "post"

abbrev VC := ReaderT Stage (StateT Program Error)

def registerVar (idx : Nat) (ty : Z3Type): VC String := do
  let stage ← read
  let var := s!"{stage}_{idx}"
  let .Program vars stats conds ← get
  let ty' := Lean.RBMap.find? vars var
  match ty' with
  | some ty' =>
    if not (ty' == ty) then
      throw $ ValError.VC s!"Var {var} has conflicting type {ty} and {ty'}."
    else pure ()
  | none => pure ()
  let vars := Lean.RBMap.insert vars var ty
  set $ Program.Program vars stats conds
  pure var

def registerCtrlVar (idx : Nat) : VC String := do
  let stage ← read
  let var := s!"{stage}_{idx}_ctrl"
  let .Program vars stats conds ← get
  let ty := Z3Type.Bool
  let ty' := Lean.RBMap.find? vars var
  match ty' with
  | some ty' =>
    if not (ty' == ty) then
      throw $ ValError.VC s!"Var {var} has conflicting type {ty} and {ty'}."
    else pure ()
  | none => pure ()
  let vars := Lean.RBMap.insert vars var ty
  set $ Program.Program vars stats conds
  pure var

def newStat (stat : Stat) : VC PUnit :=
  modify $ λ (.Program vars stats conds) ↦ Program.Program vars (Array.push stats stat) conds

def newCond (cond : Term) : VC PUnit :=
  modify $ λ (.Program vars stats conds) ↦ Program.Program vars stats (Array.push conds cond)

def genNodeVar' (idx : Nat) : Node → VC (String × Z3Type)
| .Return _ _ => throw $ ValError.VC s!"Call genNodeVar on return node."
| .ParmInt
| .AddI _ _
| .SubI _ _
| .MulI _ _
| .DivI _ _
| .LShiftI _ _
| .ConvL2I _
| .RShiftI _ _
| .ConI _ => do
  let name ← registerVar idx Z3Type.Int
  pure (name, Z3Type.Int)
| .RShiftL _ _
| .ConvI2L _
| .MulL _ _
| .ConL _ => do
  let name ← registerVar idx Z3Type.Long
  pure (name, Z3Type.Long)
| .IfTrue _
| .IfFalse _
| .CmpResult _ _
| .ConB _ => do
  let name ← registerVar idx Z3Type.Bool
  pure (name, Z3Type.Bool)
| .If _ _  => do
  let name ← registerVar idx Z3Type.IfResult
  pure (name, Z3Type.IfResult)
def genNodeVar := Function.uncurry genNodeVar'

def genRet (idx : Nat) (ty : Z3Type) : Node → VC String
| .Return _ _ => registerVar idx ty
| _ => throw $ ValError.VC s!"Call genRet on Node {idx}, which is not a return node."

def genNode (idx : Nat) (node : Node) : VC PUnit :=
  match node with
  | .ParmInt => pure ()
  | .AddI x y => bin x y Add
  | .SubI x y => bin x y Sub
  | .LShiftI x y => bin x y Shl
  | .MulL x y | .MulI x y => bin x y Mul
  | .DivI x y => bin x y Div
  | .RShiftI x y => bin x y Shr
  | .If prev cond => do
    let prev ← genNodeVar prev
    let cond ← genNodeVar cond
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (BuildIf (Var prev.fst) (Var cond.fst))
  | .IfTrue i => do
    let x ← genNodeVar i
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (And (Prev (Var x.fst)) (Cond (Var x.fst)))
  | .IfFalse i => do
    let x ← genNodeVar i
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (And (Prev (Var x.fst)) (Not (Cond (Var x.fst))))
  | .ConB b => do
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (if b then True else False)
  /- RShiftL take Long << Int in java and requires conversion. -/
  | .RShiftL x y => do
    let x ← genNodeVar x
    let y ← genNodeVar y
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq
      (Var this.fst) (Shr (Var x.fst) (I2L (Var y.fst)))
  | .ConvL2I i => do
    let x ← genNodeVar i
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (L2I (Var x.fst))
  | .ConvI2L i => do
    let x ← genNodeVar i
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (I2L (Var x.fst))
  | .ConI v => do
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (Int v)
  | .ConL v => do
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (Long v)
  | .CmpResult v .Ne => do
    let x ← genNodeVar v
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq (Var this.fst) (Not (Eq (Var x.fst) (Int 0)))
  | .Return cond prev => do
    let thisCond ← registerCtrlVar idx
    let (prev, ty) ← genNodeVar prev
    let (cond, _) ← genNodeVar cond
    let this ← genRet idx ty node
    newStat $ Assert $ Eq (Var thisCond) (Var cond)
    newStat $ Assert $ Eq (Var prev) (Var this)
  where
    bin (x : Nat × Node) (y : Nat × Node) (op : Term → Term → Term): VC PUnit := do
    let x ← genNodeVar x
    let y ← genNodeVar y
    let this ← genNodeVar (idx, node)
    newStat $ Assert $ Eq
      (Var this.fst) (op (Var x.fst) (Var y.fst))

def genNodes : Graph → VC PUnit
| .Graph _ nodes => Lean.RBMap.forM genNode nodes

def withPre : VC α → VC α := ReaderT.adapt λ _ => Stage.pre
def withPost : VC α → VC α := ReaderT.adapt λ _ => Stage.post

def connectGraphs : Graph → VC PUnit
| .Graph _ nodes =>
  flip Lean.RBMap.forM nodes λ idx node ↦ do
    match node with
    | .ParmInt => do
        let pre ← withPre $ genNodeVar (idx, node)
        let post ← withPost $ genNodeVar (idx, node)
        newStat $ Assert $ Eq (Var pre.fst) (Var post.fst)

    | .Return _ (idx', node') => do
        let ty ← Prod.snd <$> genNodeVar (idx', node')
        let pre ← withPre $ genRet idx ty node
        let post ← withPost $ genRet idx ty node
        let preCond ← withPre $ registerCtrlVar idx
        let postCond ← withPost $ registerCtrlVar idx
        /- Return nodes should have the same control flow condition and have the same value if they are reached.-/
        newCond $ Eq (Var preCond) (Var postCond)
        newCond $ If (Var preCond) (Eq (Var pre) (Var post)) True
    | _ => pure ()

def vcGen (g₁ : Graph) (g₂ : Graph) : Error Program :=
    let gen := do
        withPre $ genNodes g₁
        withPost $ genNodes g₂
        connectGraphs g₁
    let m := StateT.run (ReaderT.run gen Stage.pre) Program.empty
    Prod.snd <$> m
