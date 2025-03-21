import Lean.Data.Xml
import C2Validator.ValError
import C2Validator.SoN.RawParser

open ValError
open Lean.Xml
open Except
open Z3

namespace SoN

inductive Node where
| ParmInt
| ParmLong
| ParmFloat
| ParmDouble
| ParmIO
| Return (ctrl : Nat × Node) (io : Nat × Node) (val : Option (Nat × Node))
| AddI (x : Nat × Node) (y : Nat × Node)
| AddL (x : Nat × Node) (y : Nat × Node)
| AddF (x : Nat × Node) (y : Nat × Node)
| AddD (x : Nat × Node) (y : Nat × Node)
| SubI (x : Nat × Node) (y : Nat × Node)
| SubL (x : Nat × Node) (y : Nat × Node)
| SubF (x : Nat × Node) (y : Nat × Node)
| SubD (x : Nat × Node) (y : Nat × Node)
| MulI (x : Nat × Node) (y : Nat × Node)
| MulL (x : Nat × Node) (y : Nat × Node)
| MulF (x : Nat × Node) (y : Nat × Node)
| MulD (x : Nat × Node) (y : Nat × Node)
| DivI (ctrl : Nat × Node) (x : Nat × Node) (y : Nat × Node)
| DivL (ctrl : Nat × Node) (x : Nat × Node) (y : Nat × Node)
| DivF (x : Nat × Node) (y : Nat × Node)
| DivD (x : Nat × Node) (y : Nat × Node)
| LShiftI (x : Nat × Node) (y : Nat × Node)
| RShiftI (x : Nat × Node) (y : Nat × Node)
| RShiftL (x : Nat × Node) (y : Nat × Node)
| LShiftL (x : Nat × Node) (y : Nat × Node)
| ConvD2F (x : Nat × Node)
| ConvD2I (x : Nat × Node)
| ConvD2L (x : Nat × Node)
| ConvF2D (x : Nat × Node)
| ConvF2I (x : Nat × Node)
| ConvF2L (x : Nat × Node)
| ConvI2D (x : Nat × Node)
| ConvI2F (x : Nat × Node)
| ConvI2L (x : Nat × Node)
| ConvL2D (x : Nat × Node)
| ConvL2F (x : Nat × Node)
| ConvL2I (x : Nat × Node)
| ConL (val: Int)
| ConI (val : Int)
| ConF (val : FP32)
| ConD (val : FP32)
| ConB (val : Bool)
| If (prev : Nat × Node) (cond : Nat × Node)
| CmpResult (prev : Nat × Node) (cmp : Cmp)
| IfTrue (prev : Nat × Node)
| IfFalse (prev : Nat × Node)
| CallStaticJava (name : String) (ty : Z3TypeBasic) (ctrl : Nat × Node) (io : Nat × Node) (parms : List (Nat × Node))
deriving Nonempty

inductive Graph where
| Graph (name : String) (nodes : Lean.RBMap Nat Node compare)

abbrev BuildM := ReaderT (Lean.RBMap Nat NodeRaw compare × Array Edge) (StateT (Lean.RBMap Nat Node compare) Error)

mutual
partial def expectNode (des : Nat) (idx : Nat) : BuildM (Nat × Node) := do
  let (_, edges) ← read
  let src := Array.find? (λ (.Edge _ des' idx') ↦ des == des' ∧ idx == idx') edges
  match src with
  | some (.Edge src _ _) => do
    let node ← buildNode src
    match node with
    | some node => pure (src, node)
    | none => throw $ ValError.Parse s!"Node {idx} does not generate value but required by an edge from {des}."
  | none => throw $ ValError.Parse s!"Missing edge to Node {des} targeting slot {idx}."

/- Recursively build nodes and save the result-/
partial def buildNode (idx : Nat) :  BuildM (Option Node) := do
  let parsed ← get
  let (nodes, _) ← read
  match Lean.RBMap.find? parsed idx with
  | some node => pure node
  | none => do
    match Lean.RBMap.find? nodes idx with
    | none => throw $ ValError.Parse s!"Edge pointing to missing node {idx}."
    | some node => do
      let node ← buildNode' idx node
      match node with
      | some node => modify $ λ m ↦ Lean.RBMap.insert m idx node
      | none => pure ()
      pure node

partial def buildNode' (idx : Nat) : NodeRaw → BuildM (Option Node)
| .ParmInt => pure $ Node.ParmInt
| .ParmLong => pure $ Node.ParmLong
| .ParmFloat => pure $ Node.ParmFloat
| .ParmDouble => pure $ Node.ParmDouble
| .ParmIO => pure $ Node.ParmIO
| .Return => do
  let ctrl ← expectNode idx 0
  let io ← expectNode idx 1
  let input ← tryCatch (some <$> expectNode idx 5) λ _ ↦ pure none
  pure $ Node.Return ctrl io input
| .CallStaticJava name ty => do
  let ctrl ← expectNode idx 0
  let io ← expectNode idx 1
  let params ← ((List.range 30).drop 5).mapM λ slot ↦ tryCatch (some <$> expectNode idx slot) λ _ ↦ pure none
  let params := params.filterMap (id)
  pure $ Node.CallStaticJava name ty ctrl io params
| .AddI => bin Node.AddI
| .AddL => bin Node.AddL
| .AddF => bin Node.AddF
| .AddD => bin Node.AddD
| .SubI => bin Node.SubI
| .SubL => bin Node.SubL
| .SubF => bin Node.SubF
| .SubD => bin Node.SubD
| .MulI => bin Node.MulI
| .MulL => bin Node.MulL
| .MulF => bin Node.MulF
| .MulD => bin Node.MulD
| .DivF => bin Node.AddF
| .DivD => bin Node.AddD
| .CmpI => bin Node.SubI
| .CmpL => bin Node.SubL
| .LShiftI => bin Node.LShiftI
| .RShiftI => bin Node.RShiftI
| .RShiftL => bin Node.RShiftL
| .LShiftL => bin Node.LShiftL
| .DivI => do
  let ctrl ← expectNode idx 0
  let x ← expectNode idx 1
  let y ← expectNode idx 2
  pure $ Node.DivI ctrl x y
| .DivL => do
  let ctrl ← expectNode idx 0
  let x ← expectNode idx 1
  let y ← expectNode idx 2
  pure $ Node.DivL ctrl x y
| .ConvD2F => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvD2F
| .ConvD2I => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvD2I
| .ConvD2L => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvD2L
| .ConvF2D => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvF2D
| .ConvF2I => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvF2I
| .ConvF2L => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvF2L
| .ConvI2D => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvI2D
| .ConvI2F => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvI2F
| .ConvI2L => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvI2L
| .ConvL2D => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvL2D
| .ConvL2F => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvL2F
| .ConvL2I => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvL2I
| .Bool cmp => do
    let x ← expectNode idx 1
    pure $ Node.CmpResult x cmp
| .If => do
    let x ← expectNode idx 0
    let y ← expectNode idx 1
    pure $ Node.If x y
| .ConI v => pure $ Node.ConI v
| .ConL v => pure $ Node.ConL v
| .ConF v => pure $ Node.ConF v
| .ConD v => pure $ Node.ConD v
| .ProjCtrl | .ParmCtrl => pure $ Node.ConB true
| .IfTrue => expectNode idx 0 >>= pure ∘ some ∘ Node.IfTrue
| .IfFalse => expectNode idx 0 >>= pure ∘ some ∘ Node.IfFalse
where
  bin (op : Nat × Node → Nat × Node → Node) : BuildM Node := do
  let x ← expectNode idx 1
  let y ← expectNode idx 2
  pure $ op x y

end

def buildAllNodes : BuildM PUnit := do
  let (nodes, _) ← read
  let _ ← List.mapM buildNode (Prod.fst <$> Lean.RBMap.toList nodes)
  pure ()

def buildGraph : GraphRaw → Error Graph
| .mk name edges nodes => do
  let nodes ← StateT.run (ReaderT.run buildAllNodes (nodes, edges)) Lean.RBMap.empty
  pure $ Graph.Graph name $ nodes.snd
