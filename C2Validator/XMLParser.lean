import Lean.Data.Xml
open Lean.Xml

abbrev Parser : Type → Type := ReaderT Element (Except String)

def eAttr? (attr : String) (p : String → Option a) : Parser a :=
  do
    let elem@(.Element _ attrs _) <- read
    match Lean.RBMap.find? attrs attr >>= p with
      | some x => pure x
      | none => throw $ s!"Element missing attribute: {attr} at {elem}"

def eName : Parser String := do
  do
    let Element.Element name _ _ <- read
    pure name

def natAttr := flip eAttr? String.toNat?
def strAttr := flip eAttr? some

-- Get content if it is a string
def contentString : Parser String := do
  let Element.Element _ _ cont <- read
    let f : (Content → Option String)
          | .Character s => some s
          | _ => none
    match Array.findSome? f cont with
      | some s => pure $ String.stripPrefix s "\n"
      | none => throw s!"Content has no string, got {cont}"

def content (name: String) (p : Parser a): Parser a :=
  do
    let elem0@(.Element _ _ cont) <- read
    let f | .Element elem@(.Element name' _ _) =>
            if name == name' then some elem else none
          | _ => none
    match Array.findSome? f cont with
      | some elem => withReader (λ _ ↦ elem) p
      | none => throw s!"No content element with name: {name} at {elem0}"

def contentFiltered (filter : Parser Bool) (p : Parser a) : Parser (Array a) := do
  let .Element _ _ cont <- read
  let f | .Element elem => some elem
        | _ => none
  let elems : Array Element := Array.filterMap f cont
  -- filter exceptions should be ignored
  let filter' := MonadExcept.orelse' filter (pure false)
  let filtered ← Array.filterM (λ x ↦ withReader (λ _ ↦ x) filter') elems
  Array.mapM (λ x ↦ withReader (λ _ ↦ x) p) filtered

def contentFilteredHead (filter : Parser Bool) (p : Parser a) : Parser a := do
  let arr ← contentFiltered filter p
  match Array.find? (λ _ ↦ true) arr with
    | some elem => pure elem
    | none => throw s!"Content filter has no valid elements."

def contentArray (name: String) : Parser a → Parser (Array a) := contentFiltered ((λ x ↦ x == name) <$> eName)
