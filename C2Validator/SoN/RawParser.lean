import Lean.Data.Xml
import C2Validator.SoN.XMLParser
import C2Validator.ValError
import C2Validator.SoN.Float
import C2Validator.Z3

open ValError
open Lean.Xml
open Except
open Z3

namespace SoN

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive Cmp where
| Ne
deriving Repr

inductive NodeRaw where
| ParmInt
| ParmLong
| ParmFloat
| ParmDouble
| ParmCtrl
| ParmIO
| Return
| AddI
| AddL
| AddF
| AddD
| SubI
| SubL
| SubF
| SubD
| MulI
| MulL
| MulF
| MulD
| MulHiL
| DivI
| DivL
| DivF
| DivD
| LShiftI
| LShiftL
| RShiftI
| RShiftL
| ConvD2F
| ConvD2I
| ConvD2L
| ConvF2D
| ConvF2I
| ConvF2L
| ConvI2D
| ConvI2F
| ConvI2L
| ConvL2D
| ConvL2F
| ConvL2I
| CmpI
| CmpL
| Bool (cmp : Cmp)
| ConI (val: Int)
| ConL (val: Int)
| ConF (val: FP32)
| ConD (val: FP64)
| ProjCtrl
| If
| IfFalse
| IfTrue
| CallStaticJava (name : String) (ty : Z3TypeBasic)

structure GraphRaw where
 (name : String) (edges : Array Edge) (nodes : Lean.RBMap Nat NodeRaw compare)

/- Extract property from node -/
def propertyP (name : String) : Parser String :=
  content "properties" hasNameAttr
  where hasNameAttr := contentFilteredHead (eAttr? "name" λ x ↦ some $ x == name) contentString

def propertyP? (name: String) : Parser (Option String) :=
  MonadExcept.tryCatch (some <$> propertyP name) (Function.const _ $ pure none)

def nodeP : Parser (Option (Nat × NodeRaw)) := do
  let idx ← eAttr? "id" String.toNat?
  let name ← propertyP "name"
  let type ← propertyP "type"
  match name with
    | "Return" => pure $ (idx, NodeRaw.Return)
    | "Parm" => do
      let bottomType ← propertyP? "bottom_type"
      match Option.getD bottomType type with
        | "int" => pure $ some (idx, NodeRaw.ParmInt)
        | "long" => pure $ some (idx, NodeRaw.ParmLong)
        | "float" => pure $ some (idx, NodeRaw.ParmFloat)
        | "double" => pure $ some (idx, NodeRaw.ParmDouble)
        | "control" => pure $ some (idx, NodeRaw.ParmCtrl)
        | "abIO" => pure $ some (idx, NodeRaw.ParmIO)
        | "rawptr:BotPTR"
        | "return_address"
        | "memory" => pure none
        | name => throw $ ValError.Unsupported s!"Unknown param node {name} with index {idx}."
    | "Proj" => do
      match type with
        | "control" => pure $ some (idx, NodeRaw.ProjCtrl)
        | name => throw $ ValError.Unsupported s!"Unknown node {name} with index {idx}."
    | "AddI" => pure $ some (idx, NodeRaw.AddI)
    | "AddL" => pure $ some (idx, NodeRaw.AddL)
    | "AddF" => pure $ some (idx, NodeRaw.AddF)
    | "AddD" => pure $ some (idx, NodeRaw.AddD)

    | "SubI" => pure $ some (idx, NodeRaw.SubI)
    | "SubL" => pure $ some (idx, NodeRaw.SubL)
    | "SubF" => pure $ some (idx, NodeRaw.SubF)
    | "SubD" => pure $ some (idx, NodeRaw.SubD)

    | "MulI" => pure $ some (idx, NodeRaw.MulI)
    | "MulL" => pure $ some (idx, NodeRaw.MulL)
    | "MulF" => pure $ some (idx, NodeRaw.MulF)
    | "MulD" => pure $ some (idx, NodeRaw.MulD)
    | "MulHiL" => pure $ some (idx, NodeRaw.MulHiL)

    | "DivI" => pure $ some (idx, NodeRaw.DivI)
    | "DivL" => pure $ some (idx, NodeRaw.DivL)
    | "DivF" => pure $ some (idx, NodeRaw.DivF)
    | "DivD" => pure $ some (idx, NodeRaw.DivD)

    | "LShiftI" => pure $ some (idx, NodeRaw.LShiftI)
    | "LShiftL" => pure $ some (idx, NodeRaw.LShiftL)
    | "RShiftI" => pure $ some (idx, NodeRaw.RShiftI)
    | "RShiftL" => pure $ some (idx, NodeRaw.RShiftL)

    | "ConvD2F" => pure $ some (idx, NodeRaw.ConvD2F)
    | "ConvD2I" => pure $ some (idx, NodeRaw.ConvD2I)
    | "ConvD2L" => pure $ some (idx, NodeRaw.ConvD2L)
    | "ConvF2D" => pure $ some (idx, NodeRaw.ConvF2D)
    | "ConvF2I" => pure $ some (idx, NodeRaw.ConvF2I)
    | "ConvF2L" => pure $ some (idx, NodeRaw.ConvF2L)
    | "ConvI2D" => pure $ some (idx, NodeRaw.ConvI2D)
    | "ConvI2F" => pure $ some (idx, NodeRaw.ConvI2F)
    | "ConvI2L" => pure $ some (idx, NodeRaw.ConvI2L)
    | "ConvL2D" => pure $ some (idx, NodeRaw.ConvL2D)
    | "ConvL2F" => pure $ some (idx, NodeRaw.ConvL2F)
    | "ConvL2I" => pure $ some (idx, NodeRaw.ConvL2I)

    | "CmpI" => pure $ some (idx, NodeRaw.CmpI)
    | "CmpL" => pure $ some (idx, NodeRaw.CmpL)
    | "CallStaticJava" => do
      let name ← propertyP "dump_spec"
      let name := name.takeWhile (λ c ↦ c ≠ ' ')
      let name := name.replace "::" "-"
      let name := name.map λ c ↦ if c.isAlphanum then c else '-'
      let ty ← propertyP "bottom_type"
      let ty := ty.dropWhile (λ x ↦ x ≠ '5')
      let ty := ty.drop 1
      let ty := ty.takeWhile Char.isAlpha
      let ty ← match ty with
      | "int" => pure Z3TypeBasic.Int
      | "float" => pure Z3TypeBasic.FP32
      | "" => pure Z3TypeBasic.Unit
      | _ => throw $ ValError.Parse s!"Unknown CallStaticJava return type {ty} at Node {idx}."
      pure $ some (idx, NodeRaw.CallStaticJava name ty)
    | "If" => pure $ some (idx, NodeRaw.If)
    | "IfFalse" => pure $ some (idx, NodeRaw.IfFalse)
    | "IfTrue" => pure $ some (idx, NodeRaw.IfTrue)
    | "Bool" => do
      let spec ← propertyP "dump_spec"
      let cmp ← match spec with
      | "[ne]" => pure Cmp.Ne
      | cmp => throw $ ValError.Parse s!"Unknown bool node dump_spec {cmp} at Node {idx}"
      pure $ some (idx, NodeRaw.Bool cmp)
    | "ConI" => do
      let bottomType ← propertyP "bottom_type"
      let val ← match String.toInt? $ bottomType.drop 4 with
        | some i => pure $ some (idx, NodeRaw.ConI i)
        | none => throw $ ValError.Parse s!"Node {idx} ConI has no valid constant value."
    | "ConL" => do
      let bottomType ← propertyP "bottom_type"
      let val ← match String.toInt? $ bottomType.drop 5 with
        | some i => pure $ some (idx, NodeRaw.ConL i)
        | none => throw $ ValError.Parse s!"Node {idx} ConL has no valid constant value."
    | "ConF" => do
      let bottomType ← propertyP "bottom_type"
      let val ← match toFP32? $ bottomType.drop 6 with
        | some f => pure $ some (idx, NodeRaw.ConF f)
        | none => throw $ ValError.Parse s!"Node {idx} ConF has no valid constant value."
    | "ConD" => do
      let bottomType ← propertyP "bottom_type"
      let val ← match toFP64? $ bottomType.drop 7 with
        | some f => pure $ some (idx, NodeRaw.ConD f)
        | none => throw $ ValError.Parse s!"Node {idx} ConD has no valid constant value."
    | "Root" | "Con" | "Start" | "Halt" => pure none
    | name => throw $ ValError.Unsupported s!"Unknown node {name} with index {idx}."

def edgeP : Parser Edge :=
  Edge.Edge <$> natAttr "from"
            <*> natAttr "to"
            <*> natAttr "index"

def readGraphRaw : Parser GraphRaw := do
  let nodes ← content "nodes" (Array.filterMap id <$> contentArray "node" nodeP)
  let edges ← content "edges" (contentArray "edge" edgeP)
  let edges := flip Array.filterMap edges λ e@(Edge.Edge p₁ p₂ _) ↦
    let nodeValid := Array.contains $ Array.map Prod.fst nodes
    if nodeValid p₁ ∧ nodeValid p₂ then some e else none
  let name ← strAttr "name"
  pure $ GraphRaw.mk name edges $ Lean.RBMap.fromArray nodes compare

def parseRaw (elem : Element) : Error (GraphRaw × GraphRaw) := do
  let graphs ← content "group" (contentFiltered filter readGraphRaw) elem
  match (Array.get? graphs 0, Array.get? graphs 1) with
  | (some g1, some g2) => pure $ if g1.name == "After Parsing" then (g1, g2) else (g2, g1)
  | _ => throw $ ValError.Parse "«After Parsing» or «Before matching» phase missing."
where
  filter := List.and <$> sequence
      [ (λ x ↦ x == "graph") <$> eName
      , eAttr? "name" λ x ↦ some $ x == "After Parsing" || x == "Before matching"
      ]
  sequence := List.mapM id
