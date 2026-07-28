import LeanCompCert.CompilerAdapter.Pass

def captureAdd (x y : UInt64) : UInt64 :=
  x + y

def captureSelect (condition : Bool) (x y : UInt64) : UInt64 :=
  if condition then x else y
