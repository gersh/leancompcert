/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.AbsDiffBlock
import LeanCompCert.Ports.Section413G1Denote

/-!
# Hurst's test, as an instruction block

The reduction on the `claude_math` side leaves

```text
1000² · M(n)²  ≤  571² · n
```

and a scan has to decide that at every `n`.  Three things stop it being a
comparison of two registers.

* `M(n)` is **signed** and the machine is not.  The scan carries it as a pair
  of non-negative counts, and `absDiffG` recovers `|M(n)|` branchlessly.
* Squaring leaves the word: at `n = 10^16`, `|M(n)| ≈ 10^8`, so the left side
  is about `10^22` against `2^64 ≈ 1.8·10^19`.
* Once both sides are 128-bit, the comparison itself is `le128G`.

The one arrangement that matters: `1000² · D²` is computed as `(1000·D)²`,
not as `1000² · D²`.  Folding the constant in *before* the widening multiply
keeps the only single-word product at `1000·D ≈ 10^11`, comfortably inside a
word, and leaves exactly one widening step per side.  The other grouping
overflows before the widening can help.

Registers are concrete so every disjointness condition is `decide`-able:

```
 30 31   the two accumulator counts (in)
 32      n (in)
 33      |M(n)|
 34      1000·|M(n)|
 35 36   left  limbs
 37 38   right limbs
 39      the constant 571² = 326041
 40      verdict (out)
 41 42   comparison scratch
 50..57  multiplier scratch
```
-/

namespace LeanCompCert.Ports.HurstTestBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.AbsDiffBlock
open LeanCompCert.Ports.Section413G1Denote

/-- The scaled difference: `34 ← 1000 · |30 − 31|`. -/
def scaledAbsG : List Instr :=
  absDiffG 30 31 33 41 42 ++ [Instr.binop 34 .mul (.reg 33) (.lit 1000)]

/-- The whole test.  `40` ends as `1` exactly when the inequality holds. -/
def hurstTestG : List Instr :=
  scaledAbsG
  ++ mulWideG 4294967295 4294967296 34 34 35 36 50 51 52 53 54 55 56 57
  ++ [Instr.mov 39 (.lit 326041)]
  ++ mulWideG 4294967295 4294967296 39 32 37 38 50 51 52 53 54 55 56 57
  ++ le128G 35 36 37 38 40 41 42

theorem scaledAbsG_noDiv : scaledAbsG.all NoDivI = true := rfl

theorem hurstTestG_noDiv : hurstTestG.all NoDivI = true := rfl

/-- `34` holds `1000 · |M(n)|`, provided that fits a word. -/
theorem scaledAbsG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : 1000 * ((s 30 : Int) - (s 31 : Int)).natAbs < M) :
    srun k s scaledAbsG 34 = 1000 * ((s 30 : Int) - (s 31 : Int)).natAbs := by
  have hD := absDiffG_spec k s 30 31 33 41 42 hs (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hw : ∀ j, srun k s (absDiffG 30 31 33 41 42) j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp (absDiffG_noDiv 30 31 33 41 42) i hi) s hs
  rw [scaledAbsG, srun_append]
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, if_true]
  rw [hD]
  have hlit : (1000 : Nat) % M = 1000 := by decide
  rw [hlit]
  have hfit' : ((s 30 : Int) - (s 31 : Int)).natAbs * 1000 < M := by omega
  rw [Nat.mod_eq_of_lt hfit']
  omega

#print axioms scaledAbsG_spec

end LeanCompCert.Ports.HurstTestBlock
