import C2Validator.SoN
import C2Validator.Z3
import Lean.Data.RBTree

open SoN
open Z3

namespace VC

open Stat
open BoolTerm
open IntTerm

def edgeVC (nodes: Lean.RBMap Nat Node compare) (edge : Edge) (nPostfix : String): Except String Program :=
  let .Edge srcIdx desIdx _ := edge
    let src := Lean.RBMap.findD nodes srcIdx $ Node.Unknown s!"[Error] Missing node {srcIdx}"
    let des := Lean.RBMap.findD nodes desIdx $ Node.Unknown s!"[Error] Missing node {desIdx}"
    match (src, des) with
      | (.ParmInt, .Return) => pure $
        Program.Program
          (Lean.RBTree.ofList [name srcIdx, ret]) #[Assert $ EqI (var srcIdx) (Var ret)]
      | (.Unknown s, _)  | (_, .Unknown s) => throw s!"[Error] Unknown node: {s}"
      | (.ParmInt, .ParmInt) => throw s!"[Error] parm → pram"
      | (.Return, _) => throw s!"[Error] return → ..."
  where
    var (idx: Nat) := IntTerm.Var $ name idx
    @[inline] name (idx: Nat) := s!"v_{idx}_{nPostfix}"
    @[inline] ret := s!"ret_{nPostfix}"

def edgesVC (nodes: Lean.RBMap Nat Node compare) (edges : Array Edge) (nPostfix : String): Except String Program :=
  Array.foldlM gen Program.empty edges
  where gen stats edge := do
    let stat ← edgeVC nodes edge nPostfix
    pure $ stats ∨ stat

def graphVC (nPostfix : String) : Graph → Except String Program
  | .Graph _ edges nodes => edgesVC nodes edges nPostfix

def connectParms : Graph → Program
  | .Graph _ _ nodes =>
  let nodes := Lean.RBMap.toList nodes
  let filter | (idx, .ParmInt) => some idx
              | _ => none
  let nodes := List.filterMap filter nodes
  let decls₁ := Lean.RBTree.fromList (List.map (λ x ↦ s!"v_{x}_pre") nodes) compare
  let decls₂ := Lean.RBTree.fromList (List.map (λ x ↦ s!"v_{x}_post") nodes) compare
  let decls := Lean.RBTree.union decls₁ decls₂
  let asserts := Array.map (λ (s₁, s₂) ↦ Assert $ Eq s₁ s₂) $ Array.zip (Lean.RBTree.toArray decls₁) (Lean.RBTree.toArray decls₂)
  Program.Program decls asserts


def vcGen (g₁ : Graph) (g₂ : Graph) : Except String Program := do
  let p₁ ← graphVC "pre" g₁
  let p₂ ← graphVC "post" g₂
  let p₃ := connectParms g₁
  let p₄ := Program.Program
    Lean.RBTree.empty
    #[ Assert $ Not $ Eq "ret_pre" "ret_post"
     , CheckSAT
     , GetModel
     ]
  pure $ ((p₁ ∨ p₂) ∨ p₃) ∨ p₄
