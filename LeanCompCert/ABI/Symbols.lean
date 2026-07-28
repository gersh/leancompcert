namespace LeanCompCert.ABI

private def hex (value : Nat) : String :=
  String.ofList (Nat.toDigits 16 value)

/--
Deterministic, injective encoding into C identifiers.

Dots become single underscores to retain readable Lean module paths;
literal underscores are doubled; every other character is encoded by its
Unicode scalar value.  The `l_` prefix keeps results out of C's keyword set.
-/
def mangle (name : String) : String :=
  "l_" ++ name.toList.foldl (init := "") fun result character =>
    if character.isAlphanum then
      result.push character
    else if character == '.' then
      result ++ "_"
    else if character == '_' then
      result ++ "__"
    else
      result ++ "_x" ++ hex character.toNat ++ "_"

def moduleInitializer (moduleName : String) : String :=
  "initialize_" ++ (mangle moduleName).drop 2

def localName (id : Nat) : String :=
  s!"v_{id}"

def blockLabel (id : Nat) : String :=
  s!"block_{id}"

def isCollisionFreeOn (names : Array String) : Bool := Id.run do
  let mut seen : Array String := #[]
  for name in names do
    let symbol := mangle name
    if seen.contains symbol then return false
    seen := seen.push symbol
  return true

end LeanCompCert.ABI
