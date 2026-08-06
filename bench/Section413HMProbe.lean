import LeanCompCert.Ports.Section413Sweep

open LeanCompCert.Ports.Section413Sweep

def main : IO Unit := do
  IO.println s!"g2-all={g2SweepOK 999 1 10000}"
  IO.println s!"v1={hmV1OK 999 10000}"
  IO.println s!"v2={hmV2OK 999 10000}"
  let s1 := hmRun 1 999 10000
  let s2 := hmRun 2 999 10000
  IO.println s!"v1-head={s1.headAcc} v1-main={s1.mainAcc}"
  IO.println s!"v2-head={s2.headAcc} v2-main={s2.mainAcc}"
