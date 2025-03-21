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
      throw $ ValError.VC s!"Var {var} has conflicting type {typeName ty} and {typeName ty'}."
    else pure var
  | none => do
    set $ {p with vars := vars.insert var ty}
    registerType ty
    pure var

def ifResult : Z3Type := .Tuple [.Bool, .Bool]

-- Generate the Node name and return type
def genNodeVar (node : Nat × Node) : VC (String × Z3Type) :=
  let (idx, node) := node
  match node with
    | .Return _ _ _ => do
      let name ← registerVar idx ZSideEffect
      pure (name, ZSideEffect)
    | .CallStaticJava _ ty _ _ _ => do
      let ty := Z3Type.Tuple [.Bool, .SideEffect, ty]
      registerType ty
      let name ← registerVar idx ty
      pure (name, ty)
    | .ParmInt
    | .AddI _ _
    | .SubI _ _
    | .MulI _ _
    | .DivI _ _ _
    | .LShiftI _ _
    | .ConvL2I _
    | .ConvF2I _
    | .ConvD2I _
    | .RShiftI _ _
    | .ConI _ => do
      let name ← registerVar idx ZInt
      pure (name, ZInt)
    | .ParmIO => do
      let name ← registerVar idx ZSideEffect
      pure (name, ZSideEffect)
    | .RShiftL _ _
    | .LShiftL _ _
    | .ConvI2L _
    | .ConvF2L _
    | .ConvD2L _
    | .AddL _ _
    | .SubL _ _
    | .MulL _ _
    | .DivL _ _ _
    | .ParmLong
    | .ConL _ => do
      let name ← registerVar idx ZLong
      pure (name, ZLong)
    | .IfTrue _
    | .IfFalse _
    | .CmpResult _ _
    | .ConB _ => do
      let name ← registerVar idx ZBool
      pure (name, ZBool)
    | .ParmFloat
    | .ConvI2F _
    | .ConvL2F _
    | .ConvD2F _
    | .ConF _
    | .AddF _ _
    | .SubF _ _
    | .MulF _ _
    | .DivF _ _ => do
      let name ← registerVar idx ZFP32
      pure (name, ZFP32)
    | .ParmDouble
    | .ConvI2D _
    | .ConvL2D _
    | .ConvF2D _
    | .ConD _
    | .AddD _ _
    | .SubD _ _
    | .MulD _ _
    | .DivD _ _ => do
      let name ← registerVar idx ZFP64
      pure (name, ZFP64)
    | .If _ _  => do
      let name ← registerVar idx ifResult
      pure (name, ifResult)

def genNodeVar' (node : Nat × Node) : VC String := Prod.fst <$> genNodeVar node

def registerPostCond (x : Stat) : VC PUnit :=
  modify λ p ↦ {p with postcondition := x :: p.postcondition}

def registerFunction (name : String) (params : List Z3Type) (ret : Z3Type) : VC PUnit := do
  let p  ← get
  match p.funcs.find? name with
  | some ty' =>
    if not (ty' == (params, ret)) then
      throw $ ValError.VC s!"Function {name} has conflicting type {ty'.map (List.map typeName) typeName} and {(params, ret).map (List.map typeName) typeName}."
    else pure ()
  | none => set {p with funcs := p.funcs.insert name (params, ret)}

def withPre : VC α → VC α := ReaderT.adapt λ _ => Stage.pre
def withPost : VC α → VC α := ReaderT.adapt λ _ => Stage.post

def genNode (idx : Nat) (node : Node) : VC PUnit :=
  match node with
  | .ParmInt
  | .ParmLong
  | .ParmFloat
  | .ParmDouble => genParm
  | .ParmIO => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) IdentitySideEffect
  | .AddI x y => bin x y Add
  | .SubI x y => bin x y Sub
  | .MulI x y => bin x y Mul
  | .DivI ctrl x y => do
    bin x y Div
    let y ← genNodeVar' y
    let ctrl ← genNodeVar' ctrl
    modify λ p ↦ {p with precondition := (Not (And (Var ctrl) $ Eq (Var y) (Int 0))) :: p.precondition}
  | .AddL x y => bin x y Add
  | .SubL x y => bin x y Sub
  | .MulL x y => bin x y Mul
  | .DivL ctrl x y => do
    bin x y Div
    let y ← genNodeVar' y
    let ctrl ← genNodeVar' ctrl
    modify λ p ↦ {p with precondition := (Not (And (Var ctrl) $ Eq (Var y) (Long 0))) :: p.precondition}
  | .AddF x y => bin x y AddFP
  | .SubF x y => bin x y SubFP
  | .MulF x y => bin x y MulFP
  | .DivF x y => bin x y DivFP
  | .AddD x y => bin x y AddFP
  | .SubD x y => bin x y SubFP
  | .MulD x y => bin x y MulFP
  | .DivD x y => bin x y DivFP
  | .LShiftI x y => bin x y ShlI
  | .RShiftI x y => bin x y ShrI
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
      (Var this) (ShrL (Var x) (I2L (Var y)))
  /- LShiftL take Long << Int in java and requires conversion. -/
  | .LShiftL x y => do
    let x ← genNodeVar' x
    let y ← genNodeVar' y
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq
      (Var this) (ShlL (Var x) (I2L (Var y)))
  | .ConvD2F v => genConv v D2F
  | .ConvD2I v => genConv v D2I
  | .ConvD2L v => genConv v D2L
  | .ConvF2D v => genConv v F2D
  | .ConvF2I v => genConv v F2I
  | .ConvF2L v => genConv v F2L
  | .ConvI2D v => genConv v I2D
  | .ConvI2F v => genConv v I2F
  | .ConvI2L v => genConv v I2L
  | .ConvL2D v => genConv v L2D
  | .ConvL2F v => genConv v L2F
  | .ConvL2I v => genConv v L2I
  | .ConI v => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Int v)
  | .ConL v => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (Long v)
  | .ConF f => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (FP32 f)
  | .ConD f => do
    let this ← genNodeVar' (idx, node)
    registerPostCond $ Assert $ Eq (Var this) (FP64 f)
  | .CmpResult v .Ne => do
    let (x, ty) ← genNodeVar v
    let this ← genNodeVar' (idx, node)
    let zero ← match ty with
      | .Basic .Int => pure (Int 0)
      | .Basic .Long => pure (Long 0)
      | _ => throw $ ValError.Unsupported s!"Node {idx} Compare result for type {typeName ty}"
    registerPostCond $ Assert $ Eq (Var this) (Not (Eq (Var x) zero))
  | .Return ctrl io val => do
    let ctrl ← genNodeVar' ctrl
    let io ← genNodeVar' io
    let this ← genNodeVar' (idx, node)
    match val with
    | some val => do
      let (val, ty) ← genNodeVar val
      registerFunction "return!" [ty] ZSideEffect
      registerPostCond $ Assert $ Eq (Var this) (If (Var ctrl) (App "join" [Var io, App "return!" [Var val]]) IdentitySideEffect)
    | none => do
      registerFunction "return!" [] ZSideEffect
      registerPostCond $ Assert $ Eq (Var this) (If (Var ctrl) (App "join" [Var io, App "return!" []]) IdentitySideEffect)
    let stage ← read
    match stage with
      | .pre => modify λ p ↦ {p with outputPre := Var this :: p.outputPre}
      | .post => modify λ p ↦ {p with outputPost := Var this :: p.outputPost}
  | .CallStaticJava name _ ctrl io params => do
    let ctrl ← genNodeVar' ctrl
    let io ← genNodeVar' io
    let params ← params.mapM genNodeVar
    let paramsName := ctrl :: io :: params.map Prod.fst
    let paramsTy := ZBool :: ZSideEffect :: params.map Prod.snd
    let (this, retTy) ← genNodeVar (idx, node)
    -- Fix function with same name but different time
    let nameFix := String.intercalate "-" $ (paramsTy.drop 2).map typeName
    let name := name ++ nameFix ++ "!"
    registerFunction name paramsTy retTy
    registerPostCond $ Assert $ Eq (Var this) (App name $ Var <$> paramsName)
    if name.startsWith "trap-" then
     let stage ← read
     match stage with
      | .pre => modify λ p ↦ {p with outputPre := App "_2" [Var this] :: p.outputPre}
      | .post => modify λ p ↦ {p with outputPost := App "_2" [Var this] :: p.outputPost}
    else
      pure ()
  where
    genParm := do
      let stage ← read
      if stage == .pre then
        let pre ← withPre $ genNodeVar' (idx, node)
        let post ← withPost $ genNodeVar' (idx, node)
        modify λ p ↦ {p with parameter := Assert (Eq (Var pre) (Var post)) :: p.parameter }
      else pure ()
    genConv i op := do
      let x ← genNodeVar' i
      let this ← genNodeVar' (idx, node)
      registerPostCond $ Assert $ Eq (Var this) (op (Var x))
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
