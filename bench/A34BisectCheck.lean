import LeanCompCert.Ports.A34Bisect

/-! Native exploration only: find a passing uniform depth.  This executable
does not produce a theorem and is outside the trust path. -/

open LeanCompCert.Ports.A34Bisect

def main (args : List String) : IO UInt32 := do
  let d := (args.head?.bind String.toNat?).getD depth
  let ok := sweepOKAt d
  IO.println s!"depth={d} leaves={2 ^ d} ok={ok}"
  pure (if ok then 0 else 1)
