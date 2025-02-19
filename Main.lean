import C2Validator
import Cli

open Cli


def validate (p : Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  if p.hasFlag "xml"
  then verifyXML file
  else compileAndVerify file

def c2validator : Cmd := `[Cli|
  c2validator VIA validate; ["0.0.1"]
  "Translation validation on HotSpot C2 compiler."

  FLAGS:
    xml;                 "Verify XML file instead of Java file."

  ARGS:
    file : String;      "File to verify."
]

def main (args : List String) : IO UInt32 := do
  c2validator.validate args
