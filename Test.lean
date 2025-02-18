import C2Validator

def sequence (arr : Array System.FilePath) : IO UInt32 := do
  let failed ← flip Array.filterMapM arr λ name ↦ do
    let code ← verify name
    if code == 1 then
      pure $ some name
    else
      pure none
  match failed with
  | #[] => pure 0
  | _ => do
    IO.println s!"Failed to verify the following files:\n{failed}"
    pure 1

def main : IO UInt32 := do
  sequence
    #[ "Test"/"Resources"/"ID.java"
     , "Test"/"Resources"/"Arithmetic.java"
     ]
