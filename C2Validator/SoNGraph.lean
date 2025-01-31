import Lean.Data.Xml
import C2Validator.XMLParser

open Lean.Xml
open Except

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive Node where
| Node (id: Nat) (name : String) (type : String)
deriving Repr

inductive Graph where
| Graph (name : String) (edges : Array Edge) (nodes : Array Node)
deriving Repr

def nodeP : Parser Node :=
  Node.Node
    <$> eAttr? "id" String.toNat?
    <*> content "properties" (hasNameAttr "name")
    <*> content "properties" (hasNameAttr "type")
  where hasNameAttr s := contentFilteredHead (eAttr? "name" λ x ↦ some $ x == s) contentString

def edgeP : Parser Edge :=
  Edge.Edge <$> natAttr "from"
            <*> natAttr "to"
            <*> natAttr "index"


def readGraph : Parser Graph :=
  Graph.Graph
      <$> strAttr "name"
      <*> content "edges" (contentArray "edge" edgeP)
      <*> content "nodes" (contentArray "node" nodeP)

def parseSoN : Element → Except String (Array Graph) := content "group" $ contentFiltered filter readGraph
where
  filter := List.and <$> sequence
      [ (λ x ↦ x == "graph") <$> eName
      , eAttr? "name" λ x ↦ some $ x == "After Parsing" -- || x == "Optimize finished"
      ]
  sequence := List.mapM id
