import C2Validator.ValError
import C2Validator.VC
import C2Validator.SoN
import C2Validator.Z3

open ValError

def compileIR (path : System.FilePath) : IO (Error System.FilePath):= do
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
    pure $ pure xml

def showResult (path : System.FilePath) (result : Error PUnit) : IO UInt32 :=
  match result with
  | .ok _ => do
    IO.println s!"[🟢][Verified] {path}"
    pure 0
  | .error e => do
    IO.println $ match e with
    | .Unsupported s => s!"[🟡][Unsupported] {s}"
    | .Compile s => s!"[🔴][Compiler Error] Can not compile file: {s}"
    | .Undecidable => s!"[🟡][Undecidable Problem] loop"
    | .CounterExample ce => s!"[🔴][Counter Example] \n{ce}"
    | .Z3 s => s!"[🔴][Z3 Error] {s}"
    | .VC s => s!"[🔴][Verfi Cond Gen Error] {s}"
    | .Parse s => s!"[🔴][Parsing Error] {s}"
    | .Timeout => s!"[🔴][Timeout]"
    match e with
    | .Timeout | .Undecidable => pure 2
    | _ => pure 1

def verifyXML' (path : System.FilePath) : IO (Error PUnit) := do
  let xml ← IO.FS.readFile path
  let graphs := do
    let elem := Except.mapError ValError.Parse $ Lean.Xml.parse xml
    SoN.parse =<< elem
  let program := graphs >>= (Function.uncurry VC.vcGen)
  let run ← match program with
  | .ok p => Z3.validate path p
  | .error e => pure $ throw e

def verifyXML (path : System.FilePath) : IO UInt32 := do
  let result ← verifyXML' path
  showResult path result

def compileAndVerify (path : System.FilePath) : IO UInt32 := do
  let xml ← compileIR path
  let result ← match xml with
    | .ok xml => verifyXML' xml
    | .error e => pure $ throw e
  showResult path result
