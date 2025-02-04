import C2Validator
import Lean.Data.Xml

def main : IO Unit := do
  let file ← IO.FS.readFile "Java/ID.xml"
  let son := SoN.parseSoN =<< Lean.Xml.parse file
  let z3 := son >>= (Function.uncurry VC.vcGen)
  match z3 with
  | .ok s => IO.println s
  | .error s => IO.println s
