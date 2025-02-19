import C2Validator.SoN.Build
import C2Validator.ValError
import C2Validator.SoN.Loop
import Lean.Data.Xml

open ValError

namespace SoN


def parse (elem : Lean.Xml.Element) : Error (Graph × Graph) := do
  let (g₁, g₂) ← parseRaw elem
  loopDetect g₁
  loopDetect g₂
  let g₁' ← buildGraph g₁
  let g₂' ← buildGraph g₂
  pure $ (g₁', g₂')
