namespace LeanCompCert.Runtime

inductive Status where
  | compatible
  | adapted
  | externalTrusted
  | unsupported
  deriving Repr, BEq, DecidableEq, Inhabited

def Status.toString : Status → String
  | .compatible => "COMPATIBLE"
  | .adapted => "ADAPTED"
  | .externalTrusted => "EXTERNAL_TRUSTED"
  | .unsupported => "UNSUPPORTED"

structure Entry where
  symbol : String
  status : Status
  source : Option String := none
  reason : Option String := none
  features : Array String := #[]
  deriving Repr, BEq, Inhabited

structure Inventory where
  entries : Array Entry
  deriving Repr, BEq, Inhabited

def Inventory.find? (inventory : Inventory) (symbol : String) : Option Entry :=
  inventory.entries.toList.find? (fun entry => entry.symbol == symbol)

def Inventory.validateSymbols
    (inventory : Inventory)
    (symbols : Array String)
    (allowExternal : Bool) : Array String := Id.run do
  let mut errors := #[]
  for symbol in symbols do
    match inventory.find? symbol with
    | none => errors := errors.push s!"unknown runtime symbol `{symbol}`"
    | some entry =>
        if entry.status == .unsupported then
          errors := errors.push s!"runtime symbol `{symbol}` is unsupported: {entry.reason.getD "no reason recorded"}"
        if entry.status == .externalTrusted && !allowExternal then
          errors := errors.push s!"runtime symbol `{symbol}` is external but the active profile forbids it"
  return errors

def defaultInventory : Inventory := {
  entries := #[
    {
      symbol := "lean_compcert_unreachable"
      status := .compatible
      source := some "runtime/portable/unreachable.c"
      features := #["fatal error"]
    },
    {
      symbol := "lean_compcert_atomic_fetch_sub_int"
      status := .adapted
      source := some "runtime/adapters/atomics.c"
      reason := some "CompCert 3.17 does not accept C11 atomic types"
      features := #["thread-safe reference counting"]
    },
    {
      symbol := "lean_alloc_ctor"
      status := .externalTrusted
      source := some "Lean runtime"
      features := #["allocation"]
    },
    {
      symbol := "lean_dec_ref"
      status := .externalTrusted
      source := some "Lean runtime"
      features := #["reference counting"]
    },
    {
      symbol := "lean_spawn_task"
      status := .unsupported
      reason := some "requires threads and synchronization"
      features := #["thread"]
    }
  ]
}

end LeanCompCert.Runtime
