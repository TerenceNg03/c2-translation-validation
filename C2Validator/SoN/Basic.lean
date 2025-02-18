import C2Validator.SoN.Build
import C2Validator.ValError
import Lean.Data.Xml

open ValError

namespace SoN


def parse (elem : Lean.Xml.Element) : Error (Graph × Graph) := do
  let (g1, g2) ← parseRaw elem
  let g1' ← buildGraph g1
  let g2' ← buildGraph g2
  pure $ (g1', g2')
