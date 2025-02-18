import C2Validator

def main (args : List String) : IO UInt32 := do
  match List.head? args with
  | some file => verify file
  | none => do
    IO.eprintln "[Error] Require a file"
    pure 1
