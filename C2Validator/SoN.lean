import Lean.Data.Xml
import C2Validator.XMLParser

open Lean.Xml
open Except
open XMLParser

namespace SoN

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive Node where
| Unknown (name : String)
| ParmInt
| Return
deriving Repr

inductive Graph where
| Graph (name : String) (edges : Array Edge) (nodes : Lean.RBMap Nat Node compare)
deriving Repr

/- Extract property from node -/
def propertyP (name : String) : Parser String :=
  content "properties" hasNameAttr
  where hasNameAttr := contentFilteredHead (eAttr? "name" λ x ↦ some $ x == name) contentString

def propertyP? (name: String) : Parser (Option String) :=
  MonadExcept.tryCatch (some <$> propertyP name) (Function.const _ $ pure none)

def nodeP : Parser (Option (Nat × Node)) := do
  let idx ← eAttr? "id" String.toNat?
  let name ← propertyP "name"
  match name with
    | "Return" => pure $ (idx, Node.Return)
    | "Parm" => do
      let bottomType ← propertyP? "bottom_type"
      pure $ match bottomType with
        | some "int" => (idx, Node.ParmInt)
        | _ => none
    | _ => pure none

def edgeP : Parser Edge :=
  Edge.Edge <$> natAttr "from"
            <*> natAttr "to"
            <*> natAttr "index"

def readGraph : Parser Graph := do
  let nodes ← content "nodes" (Array.filterMap id <$> contentArray "node" nodeP)
  let edges ← content "edges" (contentArray "edge" edgeP)
  let edges := flip Array.filterMap edges λ e@(Edge.Edge p₁ p₂ _) ↦
    let nodeValid := Array.contains $ Array.map Prod.fst nodes
    if nodeValid p₁ ∧ nodeValid p₂ then some e else none
  let name ← strAttr "name"
  pure $ Graph.Graph name edges $ Lean.RBMap.fromArray nodes compare


def parseSoN (elem : Element) : Except String (Graph × Graph) := do
  let graphs ← content "group" (contentFiltered filter readGraph) elem
  match (Array.get? graphs 0, Array.get? graphs 1) with
  | (some g1, some g2) => pure $ (g1, g2)
  | _ => throw "[Error] «After Parsing» or «Optimize finished» phase missing."
where
  filter := List.and <$> sequence
      [ (λ x ↦ x == "graph") <$> eName
      , eAttr? "name" λ x ↦ some $ x == "After Parsing" || x == "Optimize finished"
      ]
  sequence := List.mapM id
