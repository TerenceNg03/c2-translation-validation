import C2Validator.Fuzzer.Fuzzer
namespace fuzzer

-- | Return (size of program and path)
def fuzzProgram (idx : Nat) (depth : Nat) (path : System.FilePath) : IO (Nat × System.FilePath) := do
  let rand ← IO.rand 0 1
  let expr ←
    if rand == 0 then
      runFuzzer fuzzInt depth
    else
      runFuzzer fuzzFloat depth
  let (size, program) ← printProgram idx expr
  let path := path.join s!"Test{idx}.java"
  IO.FS.writeFile path program
  pure (size ,path)
