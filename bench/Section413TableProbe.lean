import LeanCompCert.Ports.Section413G2Generated10000

namespace LeanCompCert.Bench.Section413TableProbe

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G2Generated

def g1FromG2 (T : Array Cell) (X : Nat) : Cell :=
  cadd T[X]!
    (cadd (cratSMul (-2) 3 T[X / 2]!)
      (cratSMul 1 9 T[X / 4]!))

def hmFromTable (T : Array Cell) (N : Nat) : Int × Int :=
  (List.range N).foldl (fun s i =>
    let X := i + 1
    let I := T[X]!
    (s.1 + cabsUB I * ((5 * X * X + 2 * X + 1 : Nat) : Int),
      s.2 + mainTermUB X I)) (0, 0)

def hmV1FromG2OK (T : Array Cell) (N : Nat) : Bool :=
  let s := hmFromTable ((List.range (N + 1)).toArray.map (g1FromG2 T)) N
  decide (s.1 ≤ 37224400 * (SCALE : Int)) &&
    decide (10000000 * s.2 ≤ 2 * 3624829 * (SCALE : Int))

def hmV2FromTableOK (T : Array Cell) (N : Nat) : Bool :=
  let s := hmFromTable T N
  decide (s.1 ≤ 47734021 * (SCALE : Int)) &&
    decide (10000000 * s.2 ≤ 4 * 3605763 * (SCALE : Int))

#eval hmFromTable expected10000 10000
#eval hmV2FromTableOK expected10000 10000
#eval hmFromTable ((List.range 10001).toArray.map (g1FromG2 expected10000)) 10000
#eval hmV1FromG2OK expected10000 10000

end LeanCompCert.Bench.Section413TableProbe
