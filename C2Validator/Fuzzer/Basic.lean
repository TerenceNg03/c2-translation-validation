import C2Validator.Fuzzer.Fuzzer
namespace fuzzer

def fuzzIntProgram (idx : Nat) (depth : Nat) (path : System.FilePath) : IO System.FilePath := do
  let expr ← runFuzzer fuzzInt depth
  let program := printProgram idx expr
  let path := path.join s!"Test{idx}.java"
  IO.FS.writeFile path program
  pure path
