import Lean.Data.Xml
import C2Validator.SoN.XMLParser
import C2Validator.ValError
import C2Validator.SoN.Float

open ValError
open Lean.Xml
open Except

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
| ParmCtrl
| ParmIO
| Return
| AddI
| AddL
| ConI (val: Int)
| ConF (val: FP32)
| SubI
| SubF
| LShiftI
| RShiftI
| RShiftL
| LShiftL
| ConvI2L
| ConvL2I
| MulL
| MulI
| DivI
| CmpI
| Bool (cmp : Cmp)
| ConL (val: Int)
| ProjCtrl
| If
| IfFalse
| IfTrue
deriving Repr

inductive GraphRaw where
| Graph (name : String) (edges : Array Edge) (nodes : Lean.RBMap Nat NodeRaw compare)
deriving Repr

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
    | "SubI" => pure $ some (idx, NodeRaw.SubI)
    | "SubF" => pure $ some (idx, NodeRaw.SubF)
    | "LShiftI" => pure $ some (idx, NodeRaw.LShiftI)
    | "RShiftI" => pure $ some (idx, NodeRaw.RShiftI)
    | "RShiftL" => pure $ some (idx, NodeRaw.RShiftL)
    | "LShiftL" => pure $ some (idx, NodeRaw.LShiftL)
    | "ConvI2L" => pure $ some (idx, NodeRaw.ConvI2L)
    | "ConvL2I" => pure $ some (idx, NodeRaw.ConvL2I)
    | "MulL" => pure $ some (idx, NodeRaw.MulL)
    | "MulI" => pure $ some (idx, NodeRaw.MulI)
    | "CmpI" => pure $ some (idx, NodeRaw.CmpI)
    | "DivI" => pure $ some (idx, NodeRaw.DivI)
    | "CallStaticJava" => pure none
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
  pure $ GraphRaw.Graph name edges $ Lean.RBMap.fromArray nodes compare

def parseRaw (elem : Element) : Error (GraphRaw × GraphRaw) := do
  let graphs ← content "group" (contentFiltered filter readGraphRaw) elem
  match (Array.get? graphs 0, Array.get? graphs 1) with
  | (some g1, some g2) => pure $ (g1, g2)
  | _ => throw $ ValError.Parse "«After Parsing» or «Before matching» phase missing."
where
  filter := List.and <$> sequence
      [ (λ x ↦ x == "graph") <$> eName
      , eAttr? "name" λ x ↦ some $ x == "After Parsing" || x == "Before matching"
      ]
  sequence := List.mapM id
