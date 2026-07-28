def sum : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sum xs

def transform (k : UInt64) : List UInt64 → List UInt64 :=
  List.map fun x => x * k + 1

def main : IO Unit := do
  let xs := transform 3 [1, 2, 3, 4, 5]
  IO.println (sum xs)
