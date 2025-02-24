namespace ValError

inductive ValError where
| Unsupported (reason : String)
| Compile (path : String)
| CounterExample (ce : System.FilePath)
| Undecidable
| Timeout
| Z3 (reason : String)
| VC (reason : String)
| Parse (reason : String)

abbrev Error := Except ValError
