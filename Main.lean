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

def compileFile (p : Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  let level := λ x ↦ x |>.as! Nat <$> p.flag? "level" |>.getD 1
  let method := λ x ↦ x |>.as! String <$> p.flag? "method"
  let _ ← compileIR level method file false
  pure 0

def compile : Cmd := `[Cli|
  compile VIA compileFile;
  "Compile and send ideal graph to IGV"

  FLAGS:
    level : Nat;       "Ideal graph level."
    method : String;    "Target method."

  ARGS:
    file : String;      "File to compile."
]

def runFuzz (p: Parsed) : IO UInt32 := do
  let path : String := p.positionalArg! "output" |>.as! String
  let depth := λ x ↦ x |>.as! Nat <$> p.flag? "depth" |>.getD 4
  let number := λ x ↦ x |>.as! Nat <$> p.flag? "number" |>.getD 20
  let timeout := λ x ↦ x |>.as! Nat <$> p.flag? "timeout" |>.getD 40
  let threaded := p.hasFlag "threaded"
  fuzzAndVerify threaded number timeout depth path
  pure 0

def fuzz : Cmd := `[Cli|
  fuzz VIA runFuzz;
  "Run verifier with fuzzer."

  FLAGS:
    depth : Nat;        "Depth of generated tree, default to 4."
    number : String;    "Number of examples to be generated, default to 20."
    timeout : Nat;      "Timeout in seconds, default to 40."
    threaded;           "Use multithreading."

  ARGS:
    output : String;    "Directory to write output files."
]

def validate (p : Parsed) : IO UInt32 := do
  let file : String := p.positionalArg! "file" |>.as! String
  let method := λ x ↦ x |>.as! String <$> p.flag? "method"
  let timeout := λ x ↦ x |>.as! Nat <$> p.flag? "timeout" |>.getD 60
  compileAndVerify method file timeout

def c2validator : Cmd := `[Cli|
  c2validator VIA validate;
  "Translation validation on HotSpot C2 compiler."

  FLAGS:
    method : String;    "Target method."
    timeout : Nat;      "Timeout"

  ARGS:
    file : String;      "File to verify."

  SUBCOMMANDS:
    xml;
    fuzz;
    compile
]

def main (args : List String) : IO UInt32 := do
  c2validator.validate args
