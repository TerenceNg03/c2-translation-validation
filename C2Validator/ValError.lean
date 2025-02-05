namespace ValError

inductive ValError where
| Unsupported (reason : String)
| Compile (path : String)
| CounterExample (ce : String)
| Undecidable
| Timeout
| Plain (reason : String)

abbrev Error := Except ValError

instance : ToString ValError where
  toString
    | .Unsupported s => s!"❓ [Unsupported] {s}"
    | .Compile s => s!"❌ [Compiler Error] Can not compile file: {s}"
    | .Undecidable => s!"❓ [Undecidable problem] loop"
    | .CounterExample ce => s!"❌ [Counter Example] \n{ce}"
    | .Plain s => s!"❌ [Error] {s}"
    | .Timeout => s!"❓ [Timeout]"

def fromExcept {α : Type} : Except String α → Error α := Except.mapError ValError.Plain
