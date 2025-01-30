import Lean.Data.Xml
open Lean.Xml

abbrev Parser : Type → Type := ReaderT Element (Except String)

def attr (attr : String) (p : String → Option a) : Parser a :=
  do
    let elem@(Element.Element _ attrs _) <- read
    match Lean.RBMap.find? attrs attr >>= p with
      | some x => pure x
      | none => throw $ s!"Element missing attribute: {attr} at {elem}"

def natAttr := flip attr String.toNat?
def strAttr := flip attr some

def content (name: String) (p : Parser a): Parser a :=
  do
    let Element.Element _ _ cont <- read
    let f | Content.Element elem@(Element.Element name' _ _) =>
            if name == name' then some elem else none
          | _ => none
    match Array.findSome? f cont with
      | some elem => withReader (λ _ ↦ elem) p
      | none => throw s!"No content element with name: {name}"

def contentArrayAttrFilter (name : String) (f : Lean.RBMap String String compare → Bool) (p: Parser a) : Parser (Array a) := do
    let Element.Element _ _ cont <- read
    let f | Content.Element elem@(.Element name' attrs _) => if
            name == name' ∧ f attrs
            then some λ _ ↦ elem
            else none
          | _ => none
    Array.mapM (flip withReader p) (Array.filterMap f cont)

def contentArray (name: String) : Parser a → Parser (Array a) := contentArrayAttrFilter name λ _ ↦ true
