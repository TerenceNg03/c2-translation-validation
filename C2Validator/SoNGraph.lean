import Lean.Data.Xml
import C2Validator.XMLParser

open Lean.Xml
open Except

inductive Edge where
| Edge (src : Nat) (des : Nat) (index : Nat)
deriving Repr

inductive Node where
| Node (id: Nat)
deriving Repr

inductive Graph where
| Graph (name : String) (edges : Array Edge) (nodes : Array Node)
deriving Repr

def nodeP : Parser Node := Node.Node <$> attr "id" String.toNat?

def edgeP : Parser Edge :=
  Edge.Edge <$> natAttr "from"
            <*> natAttr "to"
            <*> natAttr "index"


def readGraph : Parser Graph :=
  Graph.Graph
      <$> strAttr "name"
      <*> content "edges" (contentArray "edge" edgeP)
      <*> content "nodes" (contentArray "node" nodeP)

def parseSoN : Element → Except String (Array Graph) := content "group" $ contentArrayAttrFilter "graph" filter readGraph
where
  filter (attrs : Lean.RBMap String String compare) :=
    let arr := Lean.RBMap.toArray attrs
    arr.contains ("name", "After Parsing") || arr.contains ("name", "Optimize finshed")
