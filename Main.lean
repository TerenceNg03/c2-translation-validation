import C2Validator
import Cli

open Cli

def validateXML (p: Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  let timeout := λ x ↦ x |>.as! Nat <$> p.flag? "timeout" |>.getD 5
  verifyXML file timeout

def xml : Cmd := `[Cli|
  xml VIA validateXML;
  "Verify a XML file."

  ARGS:
    file : String;      "File to verify."
]

def validate (p : Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  let level := λ x ↦ x |>.as! Nat <$> p.flag? "level" |>.getD 1
  let method := λ x ↦ x |>.as! String <$> p.flag? "method"
  let timeout := λ x ↦ x |>.as! Nat <$> p.flag? "timeout" |>.getD 5
  compileAndVerify level method file timeout

def c2validator : Cmd := `[Cli|
  c2validator VIA validate;
  "Translation validation on HotSpot C2 compiler."

  FLAGS:
    level : Nat;       "Ideal graph level."
    method : String;    "Target method."
    timeout : Nat;      "Timeout"

  ARGS:
    file : String;      "File to verify."

  SUBCOMMANDS:
    xml
]

def main (args : List String) : IO UInt32 := do
  c2validator.validate args
