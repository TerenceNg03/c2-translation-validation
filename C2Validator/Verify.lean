import C2Validator.VC
import C2Validator.Compile
import C2Validator.Z3
import C2Validator.SoN
import Lean.Data.Xml

namespace Verify

def verify (path : System.FilePath) : IO UInt32 := do
  let xml ← compile.compileIR path
  let graphs := do
    let xml ← xml
    let elem := ValError.fromExcept $ Lean.Xml.parse xml
    SoN.parseSoN =<< elem
  let program := graphs >>= (Function.uncurry VC.vcGen)
  let run ← match program with
  | .ok p => Z3.validate path p
  | .error e => pure $ throw e
  match run with
  | .ok _ => do
    IO.println s!"✅ [Verified] {path}"
    pure 0
  | .error e => do
    IO.eprintln s!"{e}"
    match e with
    | .Timeout | .Unsupported _ | .Undecidable => pure 2
    | _ => pure 1
