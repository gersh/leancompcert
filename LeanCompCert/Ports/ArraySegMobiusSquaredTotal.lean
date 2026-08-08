import LeanCompCert.Ports.ArraySegMobiusSquaredSound
import LeanCompCert.Ports.MobiusResidueRealisation

/-!
# Total semantics of the production root-free test section

The expensive three-product trace is already opaque in
`ArraySegMobiusSquaredSound`.  This small layer composes it with the five
input-preparation instructions and the two-instruction gated counter update,
keeping elaboration below the repository's memory-safe build threshold.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredSound

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.MobiusResidueRealisation

/-- The new production residue is exactly the already-proved arithmetic and
ceiling prefix followed by the exact root-free test. -/
theorem mobiusLiveSquaredResidue_split (k : Nat) :
    mobiusLiveSquaredResidue k =
      blkA k ++ (blkB ++ (blkC k ++ (blkD ++ (blkE ++ mobiusSquaredTestBody k)))) := by
  rfl

/-- Total word semantics of the complete production section (F), including
the main-phase gate and the running violation counter. -/
theorem testG_spec (idx k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun idx s (testG k) rMViol =
      (s rMViol +
        (if nWord (s 65) * uWord k (s 65) (s 159) ^ 2 ≤ 2 ^ 122 then 0 else 1) *
          s 133) % M := by
  let p := srun idx s (prepG k)
  let c := srun idx p checkerG
  have hp := prepG_spec idx k s
  change p 166 = uWord k (s 65) (s 159) ∧ p 167 = nWord (s 65) at hp
  have hpword : ∀ j, p j < M := srun_lt_of_lt idx _ _ hs
  have hchecker : c 191 =
      if p 167 * p 166 ^ 2 ≤ 2 ^ 122 then 0 else 1 := checkerG_nat_spec idx p hpword
  have hc104 : c rMViol = p rMViol := checkerG_frame_viol idx p
  have hc133 : c 133 = p 133 := checkerG_frame_gate idx p
  have hp104 : p rMViol = s rMViol := prepG_frame_viol idx k s
  have hp133 : p 133 = s 133 := prepG_frame_gate idx k s
  simp only [testG, srun_append]
  change srun idx c gateG rMViol = _
  rw [gateG_spec, hchecker, hc104, hp104, hc133, hp133, hp.1, hp.2]

/-! ## No-wrap identification with the paper predicate -/

theorem ceilWord_eq (k n : Nat) (hk : k ≤ 15)
    (hn : n + 2 ^ (k + 2) < M) :
    ceilWord k n = (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) := by
  have hq1 : 1 ≤ (2 : Nat) ^ (k + 2) := Nat.one_le_two_pow
  have hassoc : n + 2 ^ (k + 2) - 1 = n + (2 ^ (k + 2) - 1) :=
    Nat.add_sub_assoc hq1 n
  have hpow : (2 : Nat) ^ (k + 2) < M := by
    rw [show M = 18446744073709551616 by rfl]
    have hk' : k + 2 ≤ 17 := by omega
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hk') (by decide)
  have hmod1 : ((2 : Nat) ^ (k + 2) - 1) % M = 2 ^ (k + 2) - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hsum : n + (2 ^ (k + 2) - 1) < M := by omega
  have hmod2 : (n + ((2 : Nat) ^ (k + 2) - 1)) % M =
      n + (2 ^ (k + 2) - 1) := Nat.mod_eq_of_lt hsum
  have hmod3 : (k + 2) % M = k + 2 := Nat.mod_eq_of_lt (by
    rw [show M = 18446744073709551616 by rfl]
    omega)
  have hdivlt : (n + (2 ^ (k + 2) - 1)) / 2 ^ (k + 2) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsum
  have hmod4 : ((n + (2 ^ (k + 2) - 1)) / 2 ^ (k + 2)) % M =
      (n + (2 ^ (k + 2) - 1)) / 2 ^ (k + 2) := Nat.mod_eq_of_lt hdivlt
  simp only [ceilWord, hmod1, hmod2, hmod3, Nat.shiftRight_eq_div_pow, hmod4]
  rw [hassoc]

theorem uWord_eq (k n absV : Nat) (hk : k ≤ 15)
    (hn : n + 2 ^ (k + 2) < M)
    (hu : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) :
    uWord k n absV =
      absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 := by
  rw [uWord, ceilWord_eq k n hk hn]
  have hsum : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) < M := by omega
  rw [Nat.mod_eq_of_lt hsum]
  have h1 : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by
    rw [show M = 18446744073709551616 by rfl]
    omega)
  rw [h1, Nat.mod_eq_of_lt hu]

theorem nWord_eq (n : Nat) (hn : n + 1 < M) : nWord n = n + 1 := by
  unfold nWord
  have h1 : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by
    rw [show M = 18446744073709551616 by rfl]
    omega)
  rw [h1, Nat.mod_eq_of_lt hn]

/-- Exact source-level semantics of section (F) under the explicit production
word guards. -/
theorem testG_source_spec (idx k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hk : k ≤ 15)
    (hn : s 65 + 2 ^ (k + 2) < M)
    (hu : s 159 + (s 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) :
    srun idx s (testG k) rMViol =
      (s rMViol +
        (if (s 65 + 1) *
            (s 159 + (s 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) ^ 2 ≤
              2 ^ 122 then 0 else 1) * s 133) % M := by
  have hn1 : s 65 + 1 < M := by
    have hp : 1 ≤ (2 : Nat) ^ (k + 2) := Nat.one_le_two_pow
    omega
  simpa only [uWord_eq k (s 65) (s 159) hk hn hu,
    nWord_eq (s 65) hn1] using testG_spec idx k s hs

/-- The actual array-machine instruction block has the same exact source
semantics; it touches no array cells. -/
theorem testBody_arun_source_spec (idx k : Nat) (s : AState)
    (hs : ∀ j, s.regs j < M)
    (hk : k ≤ 15)
    (hn : s.regs 65 + 2 ^ (k + 2) < M)
    (hu : s.regs 159 + (s.regs 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) :
    (arun idx s (mobiusSquaredTestBody k)).regs rMViol =
      (s.regs rMViol +
        (if (s.regs 65 + 1) *
            (s.regs 159 + (s.regs 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) ^ 2 ≤
              2 ^ 122 then 0 else 1) * s.regs 133) % M := by
  rw [test_lift, LeanCompCert.Verified.ArrayScalarBlock.arun_lift_regs]
  exact testG_source_spec idx k s.regs hs hk hn hu

end LeanCompCert.Ports.ArraySegMobiusSquaredSound
