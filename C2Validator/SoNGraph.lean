import Lean.Data.Xml
import C2Validator.XMLParser

open Lean.Xml
open Except

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive Node where
| Start (id: Nat)
| ParmInt (id: Nat)
| Return (id: Nat)
deriving Repr

def getIdx (node: Node) : Nat :=
  match node with
  | .Start i => i
  | .ParmInt i => i
  | .Return i => i

inductive Graph where
| Graph (name : String) (edges : Array Edge) (nodes : Array Node)
deriving Repr

/- Extract property from node -/
def propertyP (name : String) : Parser String :=
  content "properties" hasNameAttr
  where hasNameAttr := contentFilteredHead (eAttr? "name" λ x ↦ some $ x == name) contentString

def propertyP? (name: String) : Parser (Option String) :=
  MonadExcept.tryCatch (some <$> propertyP name) (λ _ ↦ pure none)

def nodeP : Parser (Option Node) := do
  let idx ← eAttr? "id" String.toNat?
  let name ← propertyP "name"
  match name with
    | "Start" => pure $ Node.Start idx
    | "Return" => pure $ Node.Return idx
    | "Parm" => do
      let bottomType ← propertyP? "bottom_type"
      pure $ match bottomType with
        | some "int" => Node.ParmInt idx
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
    let nodeValid := Array.contains $ Array.map getIdx nodes
    if nodeValid p₁ ∧ nodeValid p₂ then some e else none
  let name ← strAttr "name"
  pure $ Graph.Graph name edges nodes


def parseSoN : Element → Except String (Array Graph) := content "group" $ contentFiltered filter readGraph
where
  filter := List.and <$> sequence
      [ (λ x ↦ x == "graph") <$> eName
      , eAttr? "name" λ x ↦ some $ x == "After Parsing" -- || x == "Optimize finished"
      ]
  sequence := List.mapM id
