import Lean

namespace LeanCompCert.ABI

inductive Endianness where
  | little
  | big
  deriving Repr, BEq, DecidableEq, Inhabited

def Endianness.toString : Endianness → String
  | .little => "little"
  | .big => "big"

structure Manifest where
  leanVersion : String
  pointerBits : Nat
  endianness : Endianness
  objectAlignment : Nat
  scalarTagBits : Nat
  closureLayoutVersion : Nat
  runtimeAbiHash : String
  deriving Repr, BEq, Inhabited

def Manifest.current (runtimeAbiHash : String) : Manifest := {
  leanVersion := Lean.versionString
  pointerBits := System.Platform.numBits
  endianness := .little
  objectAlignment := System.Platform.numBits / 8
  scalarTagBits := 1
  closureLayoutVersion := 1
  runtimeAbiHash
}

def Manifest.toJson (manifest : Manifest) : Lean.Json :=
  Lean.Json.mkObj [
    ("leanVersion", Lean.toJson manifest.leanVersion),
    ("pointerBits", Lean.toJson manifest.pointerBits),
    ("endianness", Lean.toJson manifest.endianness.toString),
    ("objectAlignment", Lean.toJson manifest.objectAlignment),
    ("scalarTagBits", Lean.toJson manifest.scalarTagBits),
    ("closureLayoutVersion", Lean.toJson manifest.closureLayoutVersion),
    ("runtimeAbiHash", Lean.toJson manifest.runtimeAbiHash)
  ]

def Manifest.validateAgainst (expected active : Manifest) : Array String := Id.run do
  let mut errors := #[]
  if expected.leanVersion != active.leanVersion then
    errors := errors.push s!"Lean version mismatch: expected {expected.leanVersion}, got {active.leanVersion}"
  if expected.pointerBits != active.pointerBits then
    errors := errors.push s!"pointer width mismatch: expected {expected.pointerBits}, got {active.pointerBits}"
  if expected.endianness != active.endianness then
    errors := errors.push s!"endianness mismatch: expected {expected.endianness.toString}, got {active.endianness.toString}"
  if expected.objectAlignment != active.objectAlignment then
    errors := errors.push s!"object alignment mismatch: expected {expected.objectAlignment}, got {active.objectAlignment}"
  if expected.scalarTagBits != active.scalarTagBits then
    errors := errors.push s!"scalar tag mismatch: expected {expected.scalarTagBits}, got {active.scalarTagBits}"
  if expected.closureLayoutVersion != active.closureLayoutVersion then
    errors := errors.push
      s!"closure layout mismatch: expected {expected.closureLayoutVersion}, got {active.closureLayoutVersion}"
  if expected.runtimeAbiHash != active.runtimeAbiHash then
    errors := errors.push
      s!"runtime ABI hash mismatch: expected {expected.runtimeAbiHash}, got {active.runtimeAbiHash}"
  return errors

end LeanCompCert.ABI
