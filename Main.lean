import C2Validator
import Lean.Data.Xml

def main : IO Unit := do
  let file <- IO.FS.readFile "Java/ID.xml"
  IO.println $ repr <$> (parseSoN =<< Lean.Xml.parse file)
