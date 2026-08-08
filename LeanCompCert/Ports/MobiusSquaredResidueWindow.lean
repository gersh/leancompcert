import LeanCompCert.Ports.MobiusSquaredResidueRealisation
import LeanCompCert.Ports.MobiusResidueWindow

/-!
# Window soundness for the squared Möbius residue

Only the violation recurrence differs from `MobiusResidueWindow`.  The exact
accumulator and ceiling invariant is transported across the shared prefix;
acceptance is then proved directly from `sound_of_squared_test`.
-/

namespace LeanCompCert.Ports.MobiusSquaredResidueRealisation

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Transparent squared-residue run over the consecutive signals `1..N`. -/
def squaredResRun (k : Nat) (mu : Nat → Int) (r0 : Res) : Nat → Res
  | 0 => r0
  | n + 1 => squaredResStep k (muSig mu (n + 1))
      (squaredResRun k mu r0 n)

/-- The accumulator/ceiling invariant is insensitive to the choice of
violation predicate. -/
theorem resInv_squaredStep (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hnlt : n + 1 < 2 ^ (64 - k))
    (hnext : (accTrue k mu (n + 1)).natAbs ≤ 2 ^ (62 + k))
    (hcelNext :
      (celStep (n + 1) r.celSq r.cel 1).1 + 1 < 2 ^ 32)
    (h : ResInv k mu n r) :
    ResInv k mu (n + 1) (squaredResStep k (muSig mu (n + 1)) r) := by
  have hold := h.step k mu n r hmu hk hk15 hnlt hnext hcelNext
  exact
    { loLt := hold.loLt
      hiLt := hold.hiLt
      acc := hold.acc
      bnd := hold.bnd
      cel := hold.cel
      celSq := hold.celSq
      celLt := hold.celLt }

/-- Prefixwise invariant for the squared transparent run. -/
theorem squaredResRun_inv (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcel : ∀ m, m < N →
      (celStep (m + 1) (squaredResRun k mu r0 m).celSq
        (squaredResRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0) :
    ResInv k mu N (squaredResRun k mu r0 N) := by
  induction N with
  | zero => simpa only [squaredResRun] using h0
  | succ n ih =>
      have hprev := ih
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (fun m hm => hbnd m (by omega))
        (fun m hm => hcel m (by omega))
      simpa only [squaredResRun] using resInv_squaredStep k mu n
        (squaredResRun k mu r0 n) hmu hk hk15
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (hbnd (n + 1) (Nat.le_refl _)) (hcel n (by omega)) hprev

/-- One gated squared step increments the counter exactly on failure. -/
theorem squaredResStep_viol_eq (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hviol : r.viol + 1 < M) :
    (squaredResStep k (muSig mu n) r).viol =
      r.viol + if SquaredPass k n (stepAbs k mu n r) then 0 else 1 := by
  unfold squaredResStep squaredViolStep muSig stepAbs stepAcc
  dsimp only
  by_cases hp : SquaredPass k n
      (absBias
        (vBias k
          (accStep (if mu n = 1 then 1 else 0)
            (if mu n = -1 then 1 else 0) (wPair k n).1 (wPair k n).2
            r.tLo r.tHi).1
          (accStep (if mu n = 1 then 1 else 0)
            (if mu n = -1 then 1 else 0) (wPair k n).1 (wPair k n).2
            r.tLo r.tHi).2))
  · simp only [hp, if_true, Nat.zero_mul, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hp, if_false, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by omega)

/-- A zero next counter exposes both the zero carry-in and the passing
paper-faithful predicate. -/
theorem squaredPass_of_next_viol_zero (k : Nat) (mu : Nat → Int) (n : Nat)
    (r : Res) (hviol : r.viol + 1 < M)
    (hz : (squaredResStep k (muSig mu n) r).viol = 0) :
    r.viol = 0 ∧ SquaredPass k n (stepAbs k mu n r) := by
  rw [squaredResStep_viol_eq k mu n r hviol] at hz
  by_cases hp : SquaredPass k n (stepAbs k mu n r)
  · simp only [hp, if_true, Nat.add_zero] at hz
    exact ⟨hz, hp⟩
  · simp only [hp, if_false] at hz
    omega

/-- A zero final counter means every squared endpoint in the run passed. -/
theorem squaredResRun_zero_all_pass (k : Nat) (mu : Nat → Int) (r0 : Res)
    (N : Nat)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hz : (squaredResRun k mu r0 N).viol = 0) :
    ∀ m, m < N →
      SquaredPass k (m + 1) (stepAbs k mu (m + 1)
        (squaredResRun k mu r0 m)) := by
  induction N with
  | zero => intro m hm; omega
  | succ n ih =>
      have hzStep :
          (squaredResStep k (muSig mu (n + 1))
            (squaredResRun k mu r0 n)).viol = 0 := by
        simpa only [squaredResRun] using hz
      obtain ⟨hzPrev, hpass⟩ := squaredPass_of_next_viol_zero k mu (n + 1)
        (squaredResRun k mu r0 n) (hviol n (by omega)) hzStep
      have hprev := ih (fun m hm => hviol m (by omega)) hzPrev
      intro m hm
      by_cases hmn : m = n
      · subst m
        exact hpass
      · exact hprev m (by omega)

/-- A passing squared step proves the exact cross-multiplied source bound. -/
theorem SquaredPass.sound (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk15 : k ≤ 15) (hn : 1 ≤ n) (D : Nat) (hD : 0 < D)
    (hdvd : ∀ m, 1 ≤ m → m ≤ n → m ∣ D)
    (hnext : ResInv k mu n (squaredResStep k (muSig mu n) r))
    (hpass : SquaredPass k n (stepAbs k mu n r)) :
    4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hold : ResInv k mu n (resStep k (muSig mu n) r) := by
    exact
      { loLt := hnext.loLt
        hiLt := hnext.hiLt
        acc := hnext.acc
        bnd := hnext.bnd
        cel := hnext.cel
        celSq := hnext.celSq
        celLt := hnext.celLt }
  have hV := stepAbs_exact_bound k mu n r hk15 hold
  have happ := accTrue_close k mu hmu D n hdvd
  exact sound_of_squared_test k n (stepAbs k mu n r)
    (accTrue k mu n) (numTrue mu D n) D hn hD hV happ hpass

/-- Whole-run soundness of the paper-faithful squared transparent model. -/
theorem squaredResRun_zero_sound (k : Nat) (mu : Nat → Int) (r0 : Res)
    (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcelInv : ∀ m, m < N →
      (celStep (m + 1) (squaredResRun k mu r0 m).celSq
        (squaredResRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hz : (squaredResRun k mu r0 N).viol = 0) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ D, 0 < D →
      (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hpasses := squaredResRun_zero_all_pass k mu r0 N hviol hz
  intro n hn1 hnN D hD hdvd
  cases n with
  | zero => omega
  | succ m =>
      have hmN : m < N := by omega
      have hpass := hpasses m hmN
      have hinv := squaredResRun_inv k mu r0 (m + 1) hmu hk hk15
        (Nat.lt_of_le_of_lt hnN hN)
        (fun j hj => hbnd j (Nat.le_trans hj hnN))
        (fun j hj => hcelInv j (by omega)) h0
      have hnext : ResInv k mu (m + 1)
          (squaredResStep k (muSig mu (m + 1))
            (squaredResRun k mu r0 m)) := by
        simpa only [squaredResRun] using hinv
      exact hpass.sound k mu (m + 1) (squaredResRun k mu r0 m)
        hmu hk15 (by omega) D hD hdvd hnext

end LeanCompCert.Ports.MobiusSquaredResidueRealisation
