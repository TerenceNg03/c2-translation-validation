import C2Validator.ValError
import C2Validator.VC
import C2Validator.SoN
import C2Validator.Z3

open ValError

def compileIR (path : System.FilePath) : IO (Error String):= do
  let path ← IO.FS.realPath path
  let xml := path.withExtension "xml"
  let jClass := path.fileStem.get!
  let command : IO.Process.SpawnArgs :=
      { cmd := "java"
      , args := #[ "-Xcomp"
                , s!"-XX:CompileCommand=compileonly,{jClass}::{jClass.toLower}"
                , "-XX:PrintIdealGraphLevel=1"
                , s!"-XX:PrintIdealGraphFile={xml}"
                , path.toString
                ]
      , stdout := .null
      }
  IO.println s!"[INFO] Compiling {path.fileName.get!}..."
  let child ← IO.Process.spawn command
  let code ← IO.Process.Child.wait child
  if code ≠ 0 then
    pure $ throw $ ValError.Compile s!"Java returns code {code} while compiling {path}"
    else
    pure <$> IO.FS.readFile xml

def verify (path : System.FilePath) : IO UInt32 := do
  let xml ← compileIR path
  let graphs := do
    let xml ← xml
    let elem := Except.mapError ValError.Parse $ Lean.Xml.parse xml
    SoN.parse =<< elem
  let program := graphs >>= (Function.uncurry VC.vcGen)
  let run ← match program with
  | .ok p => Z3.validate path p
  | .error e => pure $ throw e
  match run with
  | .ok _ => do
    IO.println s!"[🟢Verified] {path}"
    pure 0
  | .error e => do
    IO.eprintln s!"{e}"
    match e with
    | .Timeout | .Undecidable => pure 2
    | _ => pure 1
