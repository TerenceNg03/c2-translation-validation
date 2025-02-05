import C2Validator

def main (args : List String) : IO UInt32 := do
  match List.head? args with
  | some file => Verify.verify file
  | none => do
    IO.eprintln "Require a file"
    pure 1
