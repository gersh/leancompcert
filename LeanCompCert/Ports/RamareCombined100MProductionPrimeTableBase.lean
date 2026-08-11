import LeanCompCert.Ports.RamareCombined100MCellBounds

/-!
# Shardable production prime-table certificate

Each closed block recomputes the paper's `trialPrime` predicate only on its
own numeric interval.  The aggregate later proves that concatenating those
blocks is exactly `trialPrimesBelow 10001`.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def trialPrimeRange (start len : Nat) : List Nat :=
  (List.range' start len).filter trialPrime

theorem trialPrimeRange_split (start a b : Nat) :
    trialPrimeRange start (a + b) =
      trialPrimeRange start a ++ trialPrimeRange (start + a) b := by
  simp only [trialPrimeRange, ← List.filter_append,
    List.range'_append_1]

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
