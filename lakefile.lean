import Lake
open Lake DSL

package «C2Validator» where
  version := v!"0.1.0"
  description := "HotSpot C2 compiler translation validation tool."
  license := "MIT"
  licenseFiles := #["LISENSE"]
  readmeFile := "README.md"

@[default_target]
lean_lib «C2Validator»

@[default_target]
lean_exe «c2validator» where

require "leanprover-community" / «mathlib»

script genXML do
  let entries ← System.FilePath.readDir "./Java"
  let files ← liftM $ Array.mapM (IO.FS.realPath ∘ IO.FS.DirEntry.path) entries
  let files := Array.filter (λ x ↦ x.extension == some "java") files
  let indexed := Array.zipWithIndex files
  let len := indexed.size
  flip Array.forM indexed λ (file, i) ↦ do
    let xml := file.withExtension "xml"
    let jClass := file.fileStem.get!
    let command : IO.Process.SpawnArgs :=
        { cmd := "java"
        , args := #[ "-Xcomp"
                  , s!"-XX:CompileCommand=compileonly,{jClass}::{jClass.toLower}"
                  , "-XX:PrintIdealGraphLevel=6"
                  , s!"-XX:PrintIdealGraphFile={xml}"
                  , file.toString
                  ]
        , stdout := .inherit
        }
    IO.println s!"[{i+1}/{len}] Compiling {file.fileName.get!}."
    let child ← IO.Process.spawn command
    let _ ← IO.Process.Child.wait child
    pure ()
  pure 0
