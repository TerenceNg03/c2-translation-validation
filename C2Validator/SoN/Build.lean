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
| ParmIO
| Return (ctrl : Nat × Node) (io : Nat × Node) (val : Option (Nat × Node))
| AddI (x : Nat × Node) (y : Nat × Node)
| AddL (x : Nat × Node) (y : Nat × Node)
| SubI (x : Nat × Node) (y : Nat × Node)
| SubF (x : Nat × Node) (y : Nat × Node)
| LShiftI (x : Nat × Node) (y : Nat × Node)
| RShiftI (x : Nat × Node) (y : Nat × Node)
| RShiftL (x : Nat × Node) (y : Nat × Node)
| LShiftL (x : Nat × Node) (y : Nat × Node)
| ConvI2L (x : Nat × Node)
| ConvL2I (x : Nat × Node)
| MulL (x : Nat × Node) (y : Nat × Node)
| MulI (x : Nat × Node) (y : Nat × Node)
| DivI (ctrl : Nat × Node) (x : Nat × Node) (y : Nat × Node)
| ConL (val: Int)
| ConI (val : Int)
| ConF (val : FP32)
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
| .SubI |.CmpI => bin Node.SubI
| .SubF => bin Node.SubF
| .LShiftI => bin Node.LShiftI
| .RShiftI => bin Node.RShiftI
| .RShiftL => bin Node.RShiftL
| .LShiftL => bin Node.LShiftL
| .MulL => bin Node.MulL
| .MulI => bin Node.MulI
| .DivI => do
  let ctrl ← expectNode idx 0
  let x ← expectNode idx 1
  let y ← expectNode idx 2
  pure $ Node.DivI ctrl x y
| .ConvI2L => expectNode idx 1 >>= pure ∘ some ∘ Node.ConvI2L
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
| .Graph name edges nodes => do
  let nodes ← StateT.run (ReaderT.run buildAllNodes (nodes, edges)) Lean.RBMap.empty
  pure $ Graph.Graph name $ nodes.snd
