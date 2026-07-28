import Lake.Build.Trace
import LeanCompCert.Verified.Decide

open LeanCompCert.Verified

/--
Direct replacement for the closed `List.range` example in `Init.Tactics`.
The larger recursion allowance is contained inside `verified_decide`.
-/
theorem listRange1000 : (List.range 1000).length = 1000 := by
  verified_decide

/--
Direct replacement for Lake's concrete hexadecimal parser sanity check.
Raising the kernel recursion allowance is sufficient; no native evaluator is
needed.
-/
theorem lakeHashOfHex :
    Lake.Hash.ofHex "0123456789" = ⟨0x0123456789⟩ ∧
      Lake.Hash.ofHex "abcdeF" = ⟨0xabcdef⟩ ∧
      Lake.Hash.ofHex "ABCDEF" = ⟨0xABCDEF⟩ := by
  verified_decide

#print axioms listRange1000
#print axioms lakeHashOfHex
