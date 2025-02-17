import Lean.Data.Xml
import C2Validator.XMLParser
import C2Validator.ValError
import C2Validator.SoN.RawParser

open ValError
open Lean.Xml
open Except
open XMLParser

namespace SoN

inductive Node where
| ParmInt
| Return (val : Nat × Node)
| AddI (x : Nat × Node) (y : Nat × Node)
deriving Repr, Nonempty

inductive Graph where
| Graph (name : String) (nodes : Lean.RBMap Nat Node compare)
deriving Repr

abbrev BuildM := ReaderT (Lean.RBMap Nat NodeRaw compare × Array Edge) (StateT (Lean.RBMap Nat Node compare) Error)

mutual
partial def expectNode (des : Nat) (idx : Nat) : BuildM (Nat × Node) := do
  let (_, edges) ← read
  let src := Array.find? (λ (.Edge _ des' idx') ↦ des == des' ∧ idx == idx') edges
  match src with
  | some (.Edge src _ _) => do
    let node ← buildNode src
    pure (src, node)
  | none => throw $ ValError.Parse s!"Missing edge to Node {des} targeting slot {idx}."

/- Recursively build nodes and save the result-/
partial def buildNode (idx : Nat) :  BuildM Node := do
  let parsed ← get
  let (nodes, _) ← read
  match Lean.RBMap.find? parsed idx with
  | some node => pure node
  | none => do
    match Lean.RBMap.find? nodes idx with
    | none => throw $ ValError.Parse s!"Edge pointing to missing node {idx}."
    | some node => do
      let node ← buildNode' idx node
      modify $ λ m ↦ Lean.RBMap.insert m idx node
      pure node

partial def buildNode' (idx : Nat) : NodeRaw → BuildM Node
| .ParmInt => pure $ Node.ParmInt
| .AddI => do
  let x ← expectNode idx 1
  let y ← expectNode idx 2
  pure $ Node.AddI x y
| .Return => do
  let input ← expectNode idx 5
  pure $ Node.Return input
end

def buildAllNodes : BuildM PUnit := do
  let (nodes, _) ← read
  let _ ← List.mapM buildNode (Prod.fst <$> Lean.RBMap.toList nodes)
  pure ()

def buildGraph : GraphRaw → Error Graph
| .Graph name edges nodes => do
  let nodes ← StateT.run (ReaderT.run buildAllNodes (nodes, edges)) Lean.RBMap.empty
  pure $ Graph.Graph name $ nodes.snd
