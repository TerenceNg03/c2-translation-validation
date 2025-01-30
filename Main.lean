import C2Validator
import Lean.Data.Xml

def main : IO Unit := do
  let fib <- IO.FS.readFile "Resources/fib.xml"
  IO.println $ repr <$> (parseSoN =<< Lean.Xml.parse fib)

#eval main
