namespace ValError

inductive ValError where
| Unsupported (reason : String)
| Compile (path : String)
| CounterExample (ce : String)
| Undecidable
| Timeout
| Z3 (reason : String)
| VC (reason : String)
| Parse (reason : String)

abbrev Error := Except ValError

instance : ToString ValError where
  toString
    | .Unsupported s => s!"❓ [Unsupported] {s}"
    | .Compile s => s!"❌ [Compiler Error] Can not compile file: {s}"
    | .Undecidable => s!"❓ [Undecidable Problem] loop"
    | .CounterExample ce => s!"❌ [Counter Example] \n{ce}"
    | .Z3 s => s!"❌ [Z3 Error] {s}"
    | .VC s => s!"❌ [Verfi Cond Gen Error] {s}"
    | .Parse s => s!"❌ [Parsing Error] {s}"
    | .Timeout => s!"❓ [Timeout]"
