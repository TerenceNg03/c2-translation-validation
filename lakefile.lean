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
lean_exe «Main» where
  exeName := "c2validator"

@[test_driver]
lean_exe «Test» where
  exeName := "c2validator-test"

require "leanprover-community" / «mathlib»
