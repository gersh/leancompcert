import LeanCompCert.Ports.Prop1224Cell
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Source semantics of the Proposition 12.2.4 coprimality subprogram

This is the first source-facing component of the cell phase.  It proves that
the emitted straight-line remainder chain computes the conjunction
`∀ p ∈ qPrimes, p ∤ r`; the result is not inferred from an oracle run.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- The value accumulated by the emitted coprimality chain from an arbitrary
zero/one seed. -/
def coprimeAccum : Nat → List Nat → Nat → Nat
  | a, [], _ => a
  | a, p :: ps, r =>
      coprimeAccum (a * if r % p = 0 then 0 else 1) ps r

/-- The zero/one value accumulated from the production seed `1`. -/
def coprimeIndicator (ps : List Nat) (r : Nat) : Nat :=
  coprimeAccum 1 ps r

@[simp] theorem coprimeIndicator_nil (r : Nat) :
    coprimeIndicator [] r = 1 := rfl

theorem coprimeAccum_le_one (a : Nat) (ps : List Nat) (r : Nat)
    (ha : a ≤ 1) : coprimeAccum a ps r ≤ 1 := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
      apply ih
      split <;> omega

theorem coprimeIndicator_le_one (ps : List Nat) (r : Nat) :
    coprimeIndicator ps r ≤ 1 :=
  coprimeAccum_le_one 1 ps r (by omega)

theorem coprimeAccum_eq_one_iff (a : Nat) (ps : List Nat) (r : Nat)
    (ha : a ≤ 1) :
    coprimeAccum a ps r = 1 ↔
      a = 1 ∧ ∀ p ∈ ps, r % p ≠ 0 := by
  induction ps generalizing a with
  | nil => simp [coprimeAccum]
  | cons p ps ih =>
      rw [coprimeAccum]
      have hnext : a * (if r % p = 0 then 0 else 1) ≤ 1 := by
        split <;> omega
      rw [ih _ hnext]
      by_cases hp : r % p = 0 <;> simp [hp]

/-- Logical meaning of the machine's coprimality word. -/
theorem coprimeIndicator_eq_one_iff (ps : List Nat) (r : Nat) :
    coprimeIndicator ps r = 1 ↔ ∀ p ∈ ps, r % p ≠ 0 := by
  simpa [coprimeIndicator] using
    coprimeAccum_eq_one_iff 1 ps r (by omega)

/-- General accumulator form used by the list induction. -/
theorem coprimeBody_run_from (ps : List Nat) (k r a : Nat) (s : AState)
    (hr : s.regs 85 = r) (ha : s.regs 81 = a) (ha1 : a ≤ 1)
    (hps : ∀ p ∈ ps, 0 < p ∧ p < M) :
    let out := arun k s (coprimeBody ps)
    out.regs 81 = coprimeAccum a ps r ∧ out.regs 85 = r ∧ out.arr = s.arr := by
  induction ps generalizing s a with
  | nil =>
      exact ⟨ha, hr, rfl⟩
  | cons p ps ih =>
      let head : List AInstr :=
        [ .scalar (.binop 82 .urem (.reg 85) (.lit p))
        , .scalar (.binop 83 .ne (.reg 82) (.lit 0))
        , .scalar (.binop 81 .mul (.reg 81) (.reg 83)) ]
      let mid := arun k s head
      have hp : 0 < p := (hps p (by simp)).1
      have hpM : p < M := (hps p (by simp)).2
      have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
      have hrpM : r % p < M := Nat.lt_trans (Nat.mod_lt r hp) hpM
      have hrpMod : r % p % M = r % p := Nat.mod_eq_of_lt hrpM
      have hps' : ∀ q ∈ ps, 0 < q ∧ q < M := by
        intro q hq
        exact hps q (by simp [hq])
      let a' := a * if r % p = 0 then 0 else 1
      have ha' : a' ≤ 1 := by
        dsimp [a']
        split <;> omega
      have ha'M : a' < M := Nat.lt_of_le_of_lt ha' (by decide)
      have hprodMod :
          (a * if r % p = 0 then 0 else 1) % M =
            a * if r % p = 0 then 0 else 1 := by
        exact Nat.mod_eq_of_lt (by simpa [a'] using ha'M)
      have hmid81 : mid.regs 81 = a' := by
        change mid.regs 81 = a * if r % p = 0 then 0 else 1
        simp [mid, head, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
          AState.writeReg, Option.getD_some, hr, ha]
        rw [hpMod, if_neg (Nat.ne_of_gt hp), hrpMod, Option.getD_some,
          hprodMod]
      have hmid85 : mid.regs 85 = r := by
        simp [mid, head, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
          AState.writeReg, Option.getD_some, hr, ha]
      have hmidArr : mid.arr = s.arr := by
        rfl
      have tail := ih (a := a') (s := mid) hmid85 hmid81 ha' hps'
      dsimp only at tail
      rw [show coprimeBody (p :: ps) = head ++ coprimeBody ps by rfl,
        arun_append]
      rcases tail with ⟨hout, h85, harr⟩
      refine ⟨?_, h85, harr.trans hmidArr⟩
      exact hout

/-- The literal `urem/ne/mul` chain computes `coprimeIndicator`.  Register 85
is framed, which makes the induction feed the same candidate to every prime.
The only partial operations are the remainders, so positivity and word bounds
of every listed prime are explicit. -/
theorem coprimeBody_run (ps : List Nat) (k r : Nat) (s : AState)
    (hr : s.regs 85 = r) (hone : s.regs 81 = 1)
    (hps : ∀ p ∈ ps, 0 < p ∧ p < M) :
    let out := arun k s (coprimeBody ps)
    out.regs 81 = coprimeIndicator ps r ∧ out.regs 85 = r ∧ out.arr = s.arr := by
  simpa [coprimeIndicator] using
    coprimeBody_run_from ps k r 1 s hr hone (by omega) hps

#print axioms coprimeBody_run_from
#print axioms coprimeBody_run
#print axioms coprimeIndicator_eq_one_iff

end LeanCompCert.Ports.Prop1224Cell
