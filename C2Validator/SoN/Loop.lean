import C2Validator.SoN.RawParser
import C2Validator.ValError
import Lean.Data.RBTree

open ValError

namespace SoN

abbrev Edges := Lean.RBMap Nat (Lean.RBTree Nat compare) compare

inductive NodeState where
| Untouched
| Visited
| Done

abbrev State := Lean.RBMap Nat NodeState compare

partial def loopDetectM (node : Nat) : ReaderT Edges (StateT State Error) PUnit := do
  let state ← get
  match state.findD node NodeState.Untouched with
  | .Visited => throw $ ValError.Undecidable
  | .Done => pure ()
  | .Untouched => do
    modify λ state ↦ state.insert node NodeState.Visited
    let edges ← read
    let edges := edges.findD node Lean.RBTree.empty
    edges.forM λ des ↦ loopDetectM des
    modify λ state ↦ state.insert node NodeState.Done

def loopDetect : GraphRaw → Error PUnit
| .mk _ edges nodes =>
  let edges : Edges := edges.foldl (
      λ map (.Edge src des _) ↦
        match map.find? src with
        | some tree => map.insert src (tree.insert des)
        | none => map.insert src (Lean.RBTree.fromList [des] compare)
        ) Lean.RBMap.empty
  let nodes := Prod.fst <$> nodes.toList
  let stateM := ReaderT.run (nodes.forM loopDetectM) edges
  StateT.run stateM Lean.RBMap.empty >>= λ _ ↦ pure ()
