import C2Validator.Fuzzer.Fuzzer
namespace fuzzer

def fuzzIntProgram (idx : Nat) (depth : Nat) (path : System.FilePath) : IO System.FilePath := do
  let rand ← IO.rand 0 1
  let expr ←
    if rand == 0 then
      runFuzzer fuzzInt depth
    else
      runFuzzer fuzzFloat depth
  let program ← printProgram idx expr
  let path := path.join s!"Test{idx}.java"
  IO.FS.writeFile path program
  pure path
