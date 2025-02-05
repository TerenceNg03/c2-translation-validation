import C2Validator.ValError

open ValError

namespace compile

def compileIR (path : System.FilePath) : IO (Error String):= do
  let path ← IO.FS.realPath path
  let xml := path.withExtension "xml"
  let jClass := path.fileStem.get!
  let command : IO.Process.SpawnArgs :=
      { cmd := "java"
      , args := #[ "-Xcomp"
                , s!"-XX:CompileCommand=compileonly,{jClass}::{jClass.toLower}"
                , "-XX:PrintIdealGraphLevel=6"
                , s!"-XX:PrintIdealGraphFile={xml}"
                , path.toString
                ]
      , stdout := .inherit
      }
  IO.println s!"[INFO] Compiling {path.fileName.get!}..."
  let child ← IO.Process.spawn command
  let code ← IO.Process.Child.wait child
  if code ≠ 0 then
    pure $ throw $ ValError.Compile s!"Java returns code {code} while compiling {path}"
    else
    pure <$> IO.FS.readFile xml
