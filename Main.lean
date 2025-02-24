import C2Validator
import Cli

open Cli

def validateXML (p: Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  verifyXML file

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
  compileAndVerify level method file

def c2validator : Cmd := `[Cli|
  c2validator VIA validate;
  "Translation validation on HotSpot C2 compiler."

  FLAGS:
    level : Nat;       "Ideal graph level."
    method : String;    "Target method."

  ARGS:
    file : String;      "File to verify."

  SUBCOMMANDS:
    xml
]

def main (args : List String) : IO UInt32 := do
  c2validator.validate args
