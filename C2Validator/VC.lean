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
deriving BEq

instance : ToString Stage where
  toString
    | .pre => "pre"
    | .post => "post"

abbrev VC := ReaderT Stage (StateT Program Error)

def registerType : Z3Type → VC PUnit
  | t@(.Tuple _) => modify λ p ↦ {p with types := p.types.insert t}
  | _ => pure ()


def registerVar (idx : Nat) (ty : Z3Type): VC String := do
  let stage ← read
  let var := s!"{stage}_{idx}"
  let p  ← get
  let vars := p.vars
  let ty' := Lean.RBMap.find? vars var
  match ty' with
  | some ty' =>
    if not (ty' == ty) then
      throw $ ValError.VC s!"Var {var} has conflicting type {ty} and {ty'}."
    else pure ()
  | none => pure ()
  let vars := Lean.RBMap.insert vars var ty
  set $ {p with vars := vars}
  pure var

def ifResult : Z3Type := .Tuple [.Bool, .Bool]

def genNodeVar (node : Nat × Node) : VC (String × Z3Type) :=
  let (idx, node) := node
  match node with
    | .Return _ _ => do
      let name ← registerVar idx ZSideEffect
      pure (name, ZSideEffect)
    | .ParmInt
    | .AddI _ _
    | .SubI _ _
    | .MulI _ _
    | .DivI _ _
    | .LShiftI _ _
    | .ConvL2I _
    | .RShiftI _ _
    | .ConI _ => do
      let name ← registerVar idx ZInt
      pure (name, ZInt)
    | .RShiftL _ _
    | .ConvI2L _
    | .MulL _ _
    | .ConL _ => do
      let name ← registerVar idx ZLong
      pure (name, ZLong)
    | .IfTrue _
    | .IfFalse _
    | .CmpResult _ _
    | .ConB _ => do
      let name ← registerVar idx ZBool
      pure (name, ZBool)
    | .If _ _  => do
      let name ← registerVar idx ifResult
      pure (name, ifResult)

def genNodeVar' (node : Nat × Node) : VC String := Prod.fst <$> genNodeVar node

def registerPostCond (x : Stat) : VC PUnit :=
  modify λ p ↦ {p with postcondition := x :: p.postcondition}

def registerFunction (name : String) (params : List Z3Type) (ret : Z3Type) : VC PUnit :=
  modify λ p ↦ {p with funcs := p.funcs.insert name (params, ret)}

def withPre : VC α → VC α := ReaderT.adapt λ _ => Stage.pre
def withPost : VC α → VC α := ReaderT.adapt λ _ => Stage.post

def genNode (idx : Nat) (node : Node) : VC PUnit :=
  match node with
  | .ParmInt => do
    let stage ← read
    if stage == .pre then
      let pre ← withPre $ genNodeVar' (idx, node)
      let post ← withPost $ genNodeVar' (idx, node)
      modify λ p ↦ {p with parameter := Assert (Eq (Var pre) (Var post)) :: p.parameter }
    else pure ()
  | .AddI x y => bin x y Add
  | .SubI x y => bin x y Sub
  | .LShiftI x y => bin x y Shl
  | .MulL x y | .MulI x y => bin x y Mul
  | .DivI x y => do
    bin x y Div
    let y ← genNodeVar' y
    modify λ p ↦ {p with precondition := (Not (Eq (Var y) (Int 0))) :: p.precondition}
  | .RShiftI x y => bin x y Shr
  | .If prev cond => do
    let prev ← genNodeVar' prev
    let cond ← genNodeVar' cond
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Mk ifResult [(Var prev), (Var cond)])
  | .IfTrue i => do
    let x ← genNodeVar' i
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (And (Index (Var x) 1) (Index (Var x) 2))
  | .IfFalse i => do
    let x ← genNodeVar' i
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (And (Index (Var x) 1) (Not (Index (Var x) 2)))
  | .ConB b => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (if b then True else False)
  /- RShiftL take Long << Int in java and requires conversion. -/
  | .RShiftL x y => do
    let x ← genNodeVar' x
    let y ← genNodeVar' y
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq
      (Var this) (Shr (Var x) (I2L (Var y)))
  | .ConvL2I i => do
    let x ← genNodeVar' i
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (L2I (Var x))
  | .ConvI2L i => do
    let x ← genNodeVar' i
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (I2L (Var x))
  | .ConI v => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Int v)
  | .ConL v => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Long v)
  | .CmpResult v .Ne => do
    let x ← genNodeVar' v
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Not (Eq (Var x) (Int 0)))
  | .Return cond val => do
    let (val, ty) ← genNodeVar val
    let (cond, _) ← genNodeVar cond
    let (this, _) ← genNodeVar (idx, node)
    registerFunction "return!" [ty] ZSideEffect
    registerPostCond $ Assert $ Eq (Var this) (If (Var cond) (App "return!" [Var val]) IdentitySideEffect)
    let stage ← read
    match stage with
      | .pre => modify λ p ↦ {p with outputPre := Var this :: p.outputPre}
      | .post => modify λ p ↦ {p with outputPost := Var this :: p.outputPost}
  where
    bin (x : Nat × Node) (y : Nat × Node) (op : Term → Term → Term): VC PUnit := do
    let x ← genNodeVar' x
    let y ← genNodeVar' y
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq
      (Var this) (op (Var x) (Var y))

def genNodes : Graph → VC PUnit
| .Graph _ nodes => Lean.RBMap.forM genNode nodes

def vcGen (g₁ : Graph) (g₂ : Graph) : Error Program :=
    let gen := do
        withPre $ genNodes g₁
        withPost $ genNodes g₂
    let m := StateT.run (ReaderT.run gen Stage.pre) Program.empty
    Prod.snd <$> m
