import Lean.Data.Xml
import C2Validator.SoN.XMLParser
import C2Validator.ValError

open ValError
open Lean.Xml
open Except

namespace SoN

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive NodeRaw where
| ParmInt
| Return
| AddI
| ConI (val: Int)
| SubI
| LShiftI
| RShiftI
| RShiftL
| ConvI2L
| ConvL2I
| MulL
| MulI
| ConL (val: Int)
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
        | "control"
        | "abIO"
        | "rawptr:BotPTR"
        | "return_address"
        | "memory" => pure none
        | name => throw $ ValError.Unsupported s!"Unknown node {name} with index {idx}."
    | "AddI" => pure $ some (idx, NodeRaw.AddI)
    | "SubI" => pure $ some (idx, NodeRaw.SubI)
    | "LShiftI" => pure $ some (idx, NodeRaw.LShiftI)
    | "RShiftI" => pure $ some (idx, NodeRaw.RShiftI)
    | "RShiftL" => pure $ some (idx, NodeRaw.RShiftL)
    | "ConvI2L" => pure $ some (idx, NodeRaw.ConvI2L)
    | "ConvL2I" => pure $ some (idx, NodeRaw.ConvL2I)
    | "MulL" => pure $ some (idx, NodeRaw.MulL)
    | "MulI" => pure $ some (idx, NodeRaw.MulI)
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
    | "Root" | "Con" | "Start" => pure none
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
