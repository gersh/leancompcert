def sum : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sum xs

def buildList (size : Nat) (seed : UInt64) : List UInt64 :=
  (List.range size).map fun n => UInt64.ofNat n * 3 + seed

def churn : Nat → UInt64 → UInt64
  | 0, checksum => checksum
  | rounds + 1, checksum =>
      let values := buildList 128 (UInt64.ofNat rounds)
      churn rounds (checksum + sum values)

def main : IO Unit := do
  IO.println (churn 100 0)
