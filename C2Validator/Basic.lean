import C2Validator.ValError
import C2Validator.VC
import C2Validator.SoN
import C2Validator.Z3
import C2Validator.Fuzzer.Basic

open ValError

def compileIR (level : Nat) (method : Option String) (path : System.FilePath) (printGraph : Bool): IO (Error System.FilePath):= do
  let path ← IO.FS.realPath path
  let xml := path.withExtension "xml"
  let jClass := path.fileStem.get!
  let method := method.getD s!"{jClass}::{jClass.toLower}"
  let command : IO.Process.SpawnArgs :=
      { cmd := "java"
      , args := let args := #[ "-Xcomp"
                , s!"-XX:CompileCommand=compileonly,{method}"
                , s!"-XX:PrintIdealGraphLevel={level}"
                , s!"-XX:PrintIdealGraphFile={xml}"
                , path.toString
                ]
                have h : args.size = 5 := by
                  constructor
                if printGraph then args else args.eraseIdx 3
      , stdout := if printGraph then .null else .inherit
      }
  IO.println s!"[INFO] Compiling {path.fileName.get!} ..."
  let child ← IO.Process.spawn command
  let code ← IO.Process.Child.wait child
  if code ≠ 0 then
    pure $ throw $ ValError.Compile s!"Java returns code {code} while compiling {path}"
    else
    pure $ pure xml

def showResult (result : Nat × Error PUnit) (path : System.FilePath): IO UInt32 :=
  let path := path.fileName.get!
  let (time, result) := result
  let time := time.toFloat / 1000
  let time := s!"[INFO] Finished in {time} seconds ({path})\n"
  match result with
  | .ok _ => do
    IO.println $ time ++ s!"[INFO] [\x1b[1;32mVerified\x1b[0m] [{path}]"
    pure 0
  | .error e => do
    IO.println $ time ++ match e with
    | .Unsupported s => s!"[WARN] [\x1b[1;33mUnsupported\x1b[0m] [{path}] {s}"
    | .Compile s => s!"[ERROR] [\x1b[1;31mCompiler Error\x1b[0m] [{path}] Can not compile file: {s}\x1b[0m"
    | .Undecidable => s!"[WARN] [\x1b[1;33mUndecidable Problem\x1b[0m] [{path}] loop"
    | .CounterExample ce => s!"[INFO] [\x1b[1;31mCounter Example\x1b[0m] [{path}] Counter example available at {ce}"
    | .Z3 s => s!"[ERROR] [\x1b[1;31mZ3 Error\x1b[0m] [{path}] {s}"
    | .VC s => s!"[ERROR] [\x1b[1;31mVerfi Cond Gen Erro\x1b[0m] [{path}] {s}"
    | .Parse s => s!"[ERROR] [\x1b[1;31mParsing Error\x1b[0m] [{path}] {s}"
    | .Timeout => s!"[WARN] [\x1b[1;31mTimeout\x1b[0m] [{path}]"
    match e with
    | .Timeout | .Undecidable => pure 2
    | _ => pure 1

def verifyXML' (path : System.FilePath) (timeout : Int): IO (Nat × Error PUnit) := do
  let xml ← IO.FS.readFile path
  let graphs := do
    let elem := Except.mapError ValError.Parse $ Lean.Xml.parse xml
    SoN.parse =<< elem
  let program := graphs >>= (Function.uncurry VC.vcGen)
  let run ← match program with
  | .ok p => Z3.validate path p timeout
  | .error e => pure $ (0, throw e)

def verifyXML (path : System.FilePath) (timeout : Int): IO UInt32 := do
  let result ← verifyXML' path timeout
  showResult result path

def compileAndVerify (method : Option String) (path : System.FilePath) (timeout : Int): IO UInt32 := do
  let xml ← compileIR 1 method path true
  let result ← match xml with
    | .ok xml => verifyXML' xml timeout
    | .error e => pure $ (0, throw e)
  showResult result path

def fuzzAndVerify (threaded : Bool) (limit : Nat) (timeout : Nat) (depth : Nat) (path : System.FilePath) : IO PUnit := do
  let date ← IO.Process.run {cmd := "date"}
  let path := path.join $ (date.replace " " "-").dropRight 1
  let shouldremove ← path.isDir
  if shouldremove then IO.FS.removeDirAll path
  IO.FS.createDirAll path
  let path ← IO.FS.realPath path
  let reportFile := path.join "report.csv"
  let handle ← IO.FS.Handle.mk reportFile .append
  handle.putStrLn s!"file,result,msg,size,time"
  let fuzzExample idx := do
    let idx := idx + 1
    IO.println s!"=============== Fuzzing \x1b[1;36m{idx}/{limit}\x1b[0m ==============="
    IO.println s!"[INFO] Generating Test{idx}.java ..."
    let (size, javaFile) ← fuzzer.fuzzProgram idx depth path
    let xml ← compileIR 1 none javaFile true
    let result ← match xml with
      | .ok xml => verifyXML' xml timeout
      | .error e => pure $ (0, throw e)
    let (time, result') := result
    let time := time.toFloat / 1000
    let msg := match result' with
    | .ok _ => s!"Verified,"
    | .error e => match e with
    | .Unsupported s => s!"Unsupported,\"{s.replace "\n" "\\n"}\""
    | .Compile s => s!",Compiler Error,\"{s.replace "\n" "\\n"}\""
    | .Undecidable => s!"Undecidable,loop"
    | .CounterExample ce => s!"Counter Example,Counter example available at {ce}"
    | .Z3 s => s!"Z3 Error,\"{s.replace "\n" "\\n"}\""
    | .VC s => s!"Verfi Cond Gen Error,\"{s.replace "\n" "\\n"}\""
    | .Parse s => s!"Parsing Error,\"{s.replace "\n" "\\n"}\""
    | .Timeout => s!"Timeout,"
    handle.putStrLn s!"{javaFile},{msg},{size},{time}"
    handle.flush
    let _ ← showResult result javaFile
    pure ()
  if threaded then
    forM (List.range limit) $ λ idx ↦ concurrently $ fuzzExample idx
  else
    forM (List.range limit) fuzzExample
where concurrently io := BaseIO.toIO $ (IO.asTask io).map λ _ ↦ ()
