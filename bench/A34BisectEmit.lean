import LeanCompCert.Ports.A34BisectProgram

open LeanCompCert.Ports.A34BisectProgram

private def driver (d expected : Nat) : String :=
  "\nint main(void)\n{\n    return l_A34Bisect" ++ toString d ++
    "() == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  let d := (args[0]?).bind String.toNat? |>.getD
    LeanCompCert.Ports.A34Bisect.depth
  let expected := (args[1]?).bind String.toNat? |>.getD 0
  let out := (args[2]?).getD "a34_bisect.c"
  match LeanCompCert.Verified.Reflect.emitRolled (programAt d) s!"A34Bisect{d}" with
  | .error es =>
      for e in es do IO.eprintln e
      pure 2
  | .ok c =>
      IO.FS.writeFile out (c ++ driver d expected)
      IO.println s!"depth={d} loops={2 ^ d} expected={expected} out={out}"
      pure 0
