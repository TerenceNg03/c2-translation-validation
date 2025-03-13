namespace SoN

abbrev FP32 := String

def toFP32? (s : String) : Option FP32 :=
  if s.all (λ x ↦ x == '1' || x == '0') then
    if s.length == 32 then
      some s
    else
      none
  else
    none
