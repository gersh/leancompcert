namespace LeanCompCert.ABI

structure ObjectLayout where
  headerBytes : Nat
  alignment : Nat
  tagOffsetBits : Nat
  tagWidthBits : Nat
  scalarTagBits : Nat
  deriving Repr, BEq, Inhabited

def lean64Layout : ObjectLayout := {
  headerBytes := 8
  alignment := 8
  tagOffsetBits := 56
  tagWidthBits := 8
  scalarTagBits := 1
}

def ObjectLayout.validate (layout : ObjectLayout) : Array String := Id.run do
  let mut errors := #[]
  if layout.alignment == 0 || layout.alignment % 2 != 0 then
    errors := errors.push "object alignment must be a nonzero power-of-two multiple"
  if layout.headerBytes % layout.alignment != 0 then
    errors := errors.push "object header size must respect object alignment"
  if layout.tagWidthBits == 0 || layout.tagOffsetBits + layout.tagWidthBits > layout.headerBytes * 8 then
    errors := errors.push "constructor tag lies outside the object header"
  if layout.scalarTagBits >= layout.alignment * 8 then
    errors := errors.push "scalar tag consumes all aligned pointer bits"
  return errors

end LeanCompCert.ABI
