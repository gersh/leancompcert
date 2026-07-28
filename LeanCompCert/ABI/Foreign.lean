import LeanCompCert.CCIR.Type

namespace LeanCompCert.ABI

inductive ForeignType where
  | void
  | scalar (type : CCIR.CCType)
  | pointer
  | object
  deriving Repr, BEq, Inhabited

inductive Ownership where
  | borrowed
  | consumed
  | returned
  | unmanaged
  deriving Repr, BEq, DecidableEq, Inhabited

structure OwnershipSpec where
  arguments : Array Ownership
  result : Ownership
  deriving Repr, BEq, Inhabited

structure EffectSpec where
  mayAllocate : Bool := false
  mayBlock : Bool := false
  mayThrow : Bool := false
  entersLeanFromThread : Bool := false
  deriving Repr, BEq, Inhabited

structure ForeignSpec where
  symbol : String
  args : Array ForeignType
  result : ForeignType
  ownership : OwnershipSpec
  effects : EffectSpec
  trusted : Bool
  deriving Repr, BEq, Inhabited

def ForeignSpec.validate (spec : ForeignSpec) : Array String := Id.run do
  let mut errors := #[]
  if spec.args.size != spec.ownership.arguments.size then
    errors := errors.push
      s!"ownership descriptor has {spec.ownership.arguments.size} entries for {spec.args.size} arguments"
  if spec.effects.mayThrow then
    errors := errors.push "C++/foreign exceptions cannot cross the Lean CompCert boundary"
  if spec.effects.entersLeanFromThread then
    errors := errors.push "thread entry into Lean requires an approved runtime adapter"
  return errors

end LeanCompCert.ABI
