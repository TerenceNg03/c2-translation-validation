import C2Validator

def sequence (arr : Array System.FilePath) : IO String := do
  let failed ← flip Array.filterMapM arr λ name ↦ do
    let code ← compileAndVerify name
    if code == 1 then
      pure $ some name
    else
      pure none
  match failed with
  | #[] => pure "[🟢]All positive cases verified."
  | _ => do
    pure s!"[🔴]Failed to verify the following files:\n{failed}"

def sequenceFail (arr : Array System.FilePath) : IO String := do
  let notFailed ← flip Array.filterMapM arr λ name ↦ do
    let code ← verifyXML name
    if code ≠ 1 then
      pure $ some name
    else
      pure none
  match notFailed with
  | #[] => pure "[🟢]All negative cases verified."
  | _ => pure s!"[🔴]Failed to verify the following files:\n{notFailed}"

def main : IO PUnit := do
  let s1 ← sequence
    #[ "Test"/"Resources"/"ID.java"
     , "Test"/"Resources"/"Arithmetic.java"
     , "Test"/"Resources"/"Loop.java"
     ]
  let s2 ← sequenceFail
    #[ "Test"/"Resources"/"TestArithmetic.xml"
    ]
  IO.println s1
  IO.println s2
