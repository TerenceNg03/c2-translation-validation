import Lean.Data.RBTree
namespace fuzzer

structure FuzzState where
(depth : Nat)
(vars : Nat)

inductive Expr
| Plus (e1 : Expr) (e2 : Expr)
| Sub (e1 : Expr) (e2 : Expr)
| Mul (e1 : Expr) (e2 : Expr)
| Div (e1 : Expr) (e2 : Expr)
| And (e1 : Expr) (e2 : Expr)
| Or (e1 : Expr) (e2 : Expr)
| ConI (val : Int)
| ConL (val : Int)
| ConF (val : String)
| ConD (val : String)
| LShift (e1 : Expr) (e2 : Expr)
| RShift (e1 : Expr) (e2 : Expr)
| VarI (idx : Nat)
| VarL (idx : Nat)
| VarF (idx : Nat)
| VarD (idx : Nat)

open Expr

abbrev FuzzM := ReaderT Nat (StateT FuzzState IO)

def randBool : FuzzM Bool := do
  let rand ← IO.rand 0 1
  pure $ if rand == 0 then false else true

def fuzzIntLeaf : FuzzM Expr := do
  let rand ← IO.rand 0 20
  let op ← randBool
  if rand <= 10 then
    let op := pure ∘ if op then ConI else ConL
    match rand with
    | 0 => op 0
    | 1 => op 31
    | 2 => op 63
    | 3 => op $ 2^31 - 1
    | 4 => op $ 1 - 2^31
    | 5 => op $ 2^63 - 1
    | 6 => op $ 1 - 2^63
    | _ => do
      let val ← IO.rand 0 (2^63 - 1)
      op val
  else
    let stat ← get
    let rand ← IO.rand 0 stat.vars
    let op := if op then VarI else VarL
    if rand < stat.vars then
      pure $ op rand
    else
      set {stat with vars := stat.vars + 1}
      pure $ op stat.vars

def fuzzFloatLeaf : FuzzM Expr := do
  let rand ← IO.rand 0 20
  let op ← randBool
  if rand <= 10 then
    let op := pure ∘ if op then ConF else ConD
    match rand with
    | 0 => op "0.0"
    | 1 => op "(0.0/0)"
    | 2 => op "(1.0/0)"
    | 3 => op "(-1.0/0)"
    | 4 => op "(-0.0)"
    | 5 => op "(-0.0/0)"
    | _ => do
      let val ← IO.rand 0 (2^31 - 1)
      let val2 ← IO.rand 0 (2^31 - 1)
      op s!"{val}.{val2}"
  else
    let stat ← get
    let rand ← IO.rand 0 stat.vars
    let op := if op then VarI else VarL
    if rand < stat.vars then
      pure $ op rand
    else
      set {stat with vars := stat.vars + 1}
      pure $ op stat.vars

partial def fuzzInt : FuzzM Expr := do
  let stat ← get
  let maxDepth ← read
  if maxDepth == stat.depth then
    fuzzIntLeaf
  else
    let rand ← IO.rand 0 9
    if rand == 9 then
      fuzzIntLeaf
    else
      let op := match rand with
      | 0 => Plus
      | 1 => Sub
      | 2 => Mul
      | 3 => Div
      | 5 => LShift
      | 6 => And
      | 7 => Or
      | _ => RShift
      let depth := stat.depth + 1
      modify λ s ↦ {s with depth := depth}
      let e1 ← fuzzInt
      modify λ s ↦ {s with depth := depth}
      let e2 ← fuzzInt
      let expr := op e1 e2
      pure $ match expr with
      | LShift x (ConI v) => LShift x (ConI (v % 16))
      | LShift x (ConL v) => LShift x (ConI (v % 64))
      | RShift x (ConI v) => RShift x (ConI (v % 16))
      | RShift x (ConL v) => RShift x (ConI (v % 64))
      | _ => expr

partial def fuzzFloat : FuzzM Expr := do
  let stat ← get
  let maxDepth ← read
  if maxDepth == stat.depth then
    fuzzFloatLeaf
  else
    let rand ← IO.rand 0 4
    if rand == 4 then
      fuzzFloatLeaf
    else
      let op := match rand with
      | 0 => Plus
      | 1 => Sub
      | 2 => Mul
      | _ => Div
      let depth := stat.depth + 1
      modify λ s ↦ {s with depth := depth}
      let e1 ← fuzzFloat
      modify λ s ↦ {s with depth := depth}
      let e2 ← fuzzFloat
      let expr := op e1 e2
      pure $ match expr with
      | LShift x (ConI v) => LShift x (ConI (v % 16))
      | LShift x (ConL v) => LShift x (ConI (v % 64))
      | RShift x (ConI v) => RShift x (ConI (v % 16))
      | RShift x (ConL v) => RShift x (ConI (v % 64))
      | _ => expr

def printParams : Expr -> StateM (Lean.RBTree Nat compare) (List String)
| .Plus e1 e2
| .Sub e1 e2
| .Mul e1 e2
| .Div e1 e2
| .And e1 e2
| .Or e1 e2
| .LShift e1 e2
| .RShift e1 e2 => do
  let p1 ← printParams e1
  let p2 ← printParams e2
  pure $ p1 ++ p2
| .ConI _
| .ConL _
| .ConF _
| .ConD _ => pure $ []
| .VarI n => f "int" n
| .VarL n => f "long" n
| .VarF n => f "float" n
| .VarD n => f "double" n
where f ty n := do
    let nSet ← get
    if nSet.contains n then
      pure []
    else do
      set $ nSet.insert n
      pure [s!"{ty} x{n}"]

partial def printExpr : Expr → StateT (Nat × String) IO String
| .Plus e1 e2 => bin "+" e1 e2
| .Sub e1 e2 => bin "-" e1 e2
| .Mul e1 e2 => bin "*" e1 e2
| .Div e1 e2 => bin "/" e1 e2
| .And e1 e2 => bin "&" e1 e2
| .Or e1 e2 => bin "|" e1 e2
| .LShift e1 e2 => bin "<<" e1 e2
| .RShift e1 e2 => bin ">>" e1 e2
| .ConI v => pure $ s!"{v % (2^31 - 1)}"
| .ConL v => pure $ s!"{v}L"
| .ConF v => pure $ s!"{v}"
| .ConD v => pure $ s!"{v}"
| .VarI n
| .VarL n
| .VarF n
| .VarD n => pure s!"x{n}"
where
  bin op e1 e2 := do
    let s1 ← printExpr e1
    let rand ← IO.rand 0 2
    if rand == 0 then
      let (idx, s) ← get
      set $ (idx + 1, s ++ s!"        var v{idx} = {s1} {op} {s1};\n")
      pure s!"v{idx}"
    else
      let s2 ← printExpr e2
      let (idx, s) ← get
      set $ (idx + 1, s ++ s!"        var v{idx} = {s1} {op} {s2};\n")
      pure s!"v{idx}"

def printProgram (idx : Nat) (expr : Expr): IO (Nat × String) := do
let paramList := (printParams expr).run' Lean.RBTree.empty
let (ret, (_, body)) ← (printExpr expr).run (0, "")
pure $ ((body.split λ c ↦ c == '\n').length, s!"\
public class Test{idx}" ++ " {" ++ s!"
    public static void main(String[] args)" ++ " {" ++s!"
      try" ++ " {" ++s!"
        test{idx}({String.intercalate ", " $ paramList.map λ _ ↦ "0"});
      } catch (Exception e)" ++ " {" ++s!"
      }
    }

    static double test{idx} ({String.intercalate ", " paramList}) "++" {"++s!"
{body}        return {ret};
    }
}\n")

def runFuzzer (fuzzer : FuzzM Expr) (depth : Nat) : IO Expr := do
  (fuzzer.run depth).run' {depth := 0, vars := 0 : FuzzState}
