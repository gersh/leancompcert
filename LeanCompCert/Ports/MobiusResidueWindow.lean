import LeanCompCert.Ports.MobiusResidueRealisation
import LeanCompCert.Ports.MobiusResidueAcc
import LeanCompCert.Ports.MobiusResidueTest

/-!
# One window of the per-integer `Σ μ(m)/m` residue

`MobiusResidueRealisation` shows the `mobiusLiveResidue` block denotes
`resStep`.  `MobiusResidueWeight`, `MobiusResidueAcc` and `MobiusResidueTest`
show that each section of `resStep` is the arithmetic it claims to be.  This
file supplies the two things the window-level statement needs on top of those:

* `accTrue_close` — the **accumulated** round-to-nearest error over `[1, n]`.
  The fixed-point accumulator tracks `2^(63+k)` times the exact rational
  partial sum to within `n/2` ulps, cleared of denominators.  This is the
  hypothesis `happ` of `MobiusResidueTest.sound_of_test`, and it is what makes
  a passing integer test a bound on the *real* sum rather than on its
  fixed-point image.
* `coreBody_regDests_disjoint` / `coreInit_regDests_disjoint` — **the two
  halves of the loop body do not interact.**  Every register the sieve core
  writes lies outside `{100,…,104} ∪ {150,…,171}`, and (by
  `mobiusLiveResidue_denote`) the residue writes nothing else.  So the
  residue's five accumulators are a function of the four signals in registers
  `65`, `79`, `80`, `133` alone, and bolting a residue onto the core cannot
  perturb the sieve.

Together with `sound_of_test` these give, at a single gated integer `n` whose
carry-in really is the accumulator at `n − 1`,

```
4 · (n+1) · (Σ_{m ≤ n} μ(m)·(D/m))² ≤ D²   for every common denominator D,
```

which is `|Σ_{m ≤ n} μ(m)/m| ≤ 1/(2·√(n+1))` with the denominators cleared,
i.e. `MathExtras.Reductions.PlattStrongerRangeNatFamily` at `n`.

Nothing here assumes anything about the sieve: `mu` is an arbitrary function
into `{−1, 0, 1}` and the signals are the ones a correct sieve would present.
Supplying that the sieve *does* present them remains the principal
whole-program denotation premise.

`accStep_mu` and `ResInv.step` now assemble the per-section arithmetic into one
exact model step, including machine overflow/underflow safety.  `resRun_inv`
chains that invariant over every integer, and `resFold_range_eq_resRun` makes
the indexed run definitionally available to a future denotation trace.

`resStep_viol_eq` and `resRun_zero_all_pass` also prove the reverse acceptance
direction: a zero final counter forces every transparent per-step comparison
to pass.

`stepAbs_exact_bound`, `StepPass.sound`, and `resRun_zero_sound` complete the
final arithmetic assembly from those passing comparisons to the exact
cross-multiplied source family.

This leaf does not itself identify the segmented sieve signal with a library
Möbius function.  The consuming project proves that identification and the
complete production schedule in
`TGNativeCertificates.ArraySegMobiusMoebius`; live Hurst/CDEM residues reuse
that schedule through `ArraySegMertensLiveFold`.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-! ## The window model -/

/-- Iterating the model over a list of signals. -/
def resFold (k : Nat) : List Sig → Res → Res
  | [], r => r
  | g :: gs, r => resFold k gs (resStep k g r)

/-- The signal a gated integer `n` presents: `n` in register `65`, the two
`μ` indicators in `79`/`80`, the main-accumulation gate set. -/
def muSig (mu : Nat → Int) (n : Nat) : Sig :=
  ⟨n, if mu n = 1 then 1 else 0, if mu n = -1 then 1 else 0, 1⟩

/-- The exact fixed-point accumulator `Σ_{m ≤ n} μ(m)·round(2^(63+k)/m)`. -/
def accTrue (k : Nat) (mu : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => accTrue k mu n + mu (n + 1) * (wgt k (n + 1) : Int)

/-- `Σ_{m ≤ n} μ(m)·(D/m)`: the exact partial sum over a common denominator
`D`.  For `D` divisible by every `m ≤ n` this is `D · Σ_{m ≤ n} μ(m)/m`. -/
def numTrue (mu : Nat → Int) (D : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => numTrue mu D n + mu (n + 1) * ((D / (n + 1) : Nat) : Int)

/-- The invariant the residue's five registers carry from one gated integer to
the next. -/
structure ResInv (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res) : Prop where
  loLt : r.tLo < M
  hiLt : r.tHi < M
  acc : (r.tLo : Int) + (M : Int) * r.tHi = 2 ^ (64 + k) + accTrue k mu n
  bnd : (accTrue k mu n).natAbs ≤ 2 ^ (62 + k)
  cel : CeilInv r.cel (n + 1)
  celSq : r.celSq = r.cel * r.cel
  celLt : r.cel + 1 < 2 ^ 32

/-- `accTrue` depends only on the values at the positive integers in its
finite prefix. -/
theorem accTrue_congr_prefix (k n : Nat) (mu nu : Nat → Int)
    (h : ∀ m, 1 ≤ m → m ≤ n → mu m = nu m) :
    accTrue k mu n = accTrue k nu n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [accTrue]
      rw [ih (fun m hm1 hmn => h m hm1 (by omega)),
        h (n + 1) (by omega) (Nat.le_refl _)]

/-- Change the arithmetic function named by a residue invariant when the two
functions agree on the invariant's finite positive prefix. -/
theorem ResInv.changeFunction {k n : Nat} {mu nu : Nat → Int} {r : Res}
    (hfun : ∀ m, 1 ≤ m → m ≤ n → mu m = nu m)
    (h : ResInv k mu n r) : ResInv k nu n r := by
  have heq := accTrue_congr_prefix k n mu nu hfun
  exact
    { loLt := h.loLt
      hiLt := h.hiLt
      acc := by simpa only [heq] using h.acc
      bnd := by simpa only [heq] using h.bnd
      cel := h.cel
      celSq := h.celSq
      celLt := h.celLt }

/-! ## One exact accumulator step -/

/-- The two indicator bits produced for a value of `μ(n)` advance the
two-limb accumulator by exactly `μ(n) * wgt k n`.  The two range hypotheses
are the ordinary unsigned add/subtract preconditions; a window invariant will
derive the relevant one from its bound on the next exact partial sum. -/
theorem accStep_mu (k n tLo tHi : Nat) (mu : Int)
    (hmu : mu = 1 ∨ mu = -1 ∨ mu = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hn : 1 ≤ n)
    (hnlt : n < 2 ^ (64 - k)) (hlo : tLo < M) (hhi : tHi < M)
    (hadd : (tLo + M * tHi) + wgt k n < M * M)
    (hsub : wgt k n ≤ tLo + M * tHi) :
    let w := wPair k n
    ((accStep (if mu = 1 then 1 else 0) (if mu = -1 then 1 else 0)
        w.1 w.2 tLo tHi).1 : Int) +
      (M : Int) * (accStep (if mu = 1 then 1 else 0)
        (if mu = -1 then 1 else 0) w.1 w.2 tLo tHi).2 =
      (tLo : Int) + (M : Int) * tHi + mu * (wgt k n : Nat) := by
  dsimp only
  have hw := wPair_spec k n hk hk15 hn hnlt
  have hwl := wPair_fst_lt k n
  have hwh := wPair_snd_lt k n
  rcases hmu with hmu | hmu | hmu
  · rw [hmu]
    have hone : (1 : Int) ≠ -1 := by omega
    simp [hone]
    rw [← hw] at hadd ⊢
    exact_mod_cast accStep_add (wPair k n).1 (wPair k n).2 tLo tHi
      hwl hwh hlo hhi hadd
  · rw [hmu]
    have hneg : (-1 : Int) ≠ 1 := by omega
    simp [hneg]
    rw [← hw] at hsub ⊢
    have ha := accStep_sub (wPair k n).1 (wPair k n).2 tLo tHi
      hwl hwh hlo hhi hsub
    have ha' := congrArg (fun x : Nat => (x : Int)) ha
    push_cast at ha'
    rw [Int.natCast_sub hsub] at ha'
    omega
  · rw [hmu]
    have hzero1 : (0 : Int) ≠ 1 := by omega
    have hzeroNeg : (0 : Int) ≠ -1 := by omega
    simp [hzero1, hzeroNeg,
      accStep_zero (wPair k n).1 (wPair k n).2 tLo tHi hlo hhi]

/-- The invariant leaves enough headroom for the next positive weight. -/
theorem ResInv.addRange {k : Nat} {mu : Nat → Int} {n : Nat} {r : Res}
    (hk15 : k ≤ 15) (h : ResInv k mu n r) :
    r.tLo + M * r.tHi + wgt k (n + 1) < M * M := by
  have hw := wgt_le k (n + 1) (by omega)
  have h64 : (2 : Nat) ^ (64 + k) ≤ 2 ^ 79 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h63 : (2 : Nat) ^ (63 + k) ≤ 2 ^ 78 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h62 : (2 : Nat) ^ (62 + k) ≤ 2 ^ 77 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hcap : (2 : Nat) ^ 79 + 2 ^ 77 + 2 ^ 78 < M * M := by decide
  have hAupper : accTrue k mu n ≤ ((2 ^ (62 + k) : Nat) : Int) := by
    by_cases hA : 0 ≤ accTrue k mu n
    · have hb : (((accTrue k mu n).natAbs : Nat) : Int) ≤
          ((2 ^ (62 + k) : Nat) : Int) := by exact_mod_cast h.bnd
      rw [Int.natAbs_of_nonneg hA] at hb
      exact hb
    · have hp0 : (0 : Int) ≤ ((2 ^ (62 + k) : Nat) : Int) :=
        Int.natCast_nonneg _
      omega
  have hencI : ((r.tLo + M * r.tHi : Nat) : Int) ≤
      ((2 ^ (64 + k) + 2 ^ (62 + k) : Nat) : Int) := by
    push_cast
    rw [h.acc]
    exact Int.add_le_add_left hAupper _
  have henc : r.tLo + M * r.tHi ≤ 2 ^ (64 + k) + 2 ^ (62 + k) := by
    exact_mod_cast hencI
  omega

/-- The invariant's positive bias is larger than any one weight, so the next
unsigned subtraction cannot underflow. -/
theorem ResInv.subRange {k : Nat} {mu : Nat → Int} {n : Nat} {r : Res}
    (h : ResInv k mu n r) : wgt k (n + 1) ≤ r.tLo + M * r.tHi := by
  have hw := wgt_le k (n + 1) (by omega)
  have hp64 : (2 : Nat) ^ (64 + k) = 4 * 2 ^ (62 + k) := by
    rw [show 64 + k = (62 + k) + 2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hp63 : (2 : Nat) ^ (63 + k) = 2 * 2 ^ (62 + k) := by
    rw [show 63 + k = (62 + k) + 1 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hp64I : (2 : Int) ^ (64 + k) = 4 * 2 ^ (62 + k) := by
    exact_mod_cast hp64
  have hp63I : (2 : Int) ^ (63 + k) = 2 * 2 ^ (62 + k) := by
    exact_mod_cast hp63
  have hAlower : -(((2 ^ (62 + k) : Nat) : Int)) ≤ accTrue k mu n := by
    by_cases hA : accTrue k mu n ≤ 0
    · have hb : (((accTrue k mu n).natAbs : Nat) : Int) ≤
          ((2 ^ (62 + k) : Nat) : Int) := by exact_mod_cast h.bnd
      rw [Int.ofNat_natAbs_of_nonpos hA] at hb
      omega
    · have hp0 : (0 : Int) ≤ ((2 ^ (62 + k) : Nat) : Int) :=
        Int.natCast_nonneg _
      omega
  have hcast62 : (((2 : Nat) ^ (62 + k) : Nat) : Int) =
      (2 : Int) ^ (62 + k) := Int.natCast_pow 2 (62 + k)
  rw [hcast62] at hAlower
  have hencI : ((2 ^ (63 + k) : Nat) : Int) ≤
      ((r.tLo + M * r.tHi : Nat) : Int) := by
    push_cast
    rw [h.acc]
    rw [hp64I, hp63I]
    omega
  have henc : 2 ^ (63 + k) ≤ r.tLo + M * r.tHi := by exact_mod_cast hencI
  omega

/-- The biased accumulator occupies at most `k+1` high-limb bits, exactly the
range required by `vBias_spec`. -/
theorem ResInv.hiSmall {k : Nat} {mu : Nat → Int} {n : Nat} {r : Res}
    (h : ResInv k mu n r) : r.tHi < 2 ^ (k + 1) := by
  have hAupper : accTrue k mu n ≤ ((2 ^ (62 + k) : Nat) : Int) := by
    by_cases hA : 0 ≤ accTrue k mu n
    · have hb : (((accTrue k mu n).natAbs : Nat) : Int) ≤
          ((2 ^ (62 + k) : Nat) : Int) := by exact_mod_cast h.bnd
      rw [Int.natAbs_of_nonneg hA] at hb
      exact hb
    · exact Int.le_trans (by omega) (Int.natCast_nonneg _)
  have hencI : ((r.tLo + M * r.tHi : Nat) : Int) ≤
      ((2 ^ (64 + k) + 2 ^ (62 + k) : Nat) : Int) := by
    push_cast
    rw [h.acc]
    exact Int.add_le_add_left hAupper _
  have henc : r.tLo + M * r.tHi ≤ 2 ^ (64 + k) + 2 ^ (62 + k) := by
    exact_mod_cast hencI
  have hp64 : (2 : Nat) ^ (64 + k) = 4 * 2 ^ (62 + k) := by
    rw [show 64 + k = (62 + k) + 2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hp65 : (2 : Nat) ^ (65 + k) = 8 * 2 ^ (62 + k) := by
    rw [show 65 + k = (62 + k) + 3 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hMshift : M * 2 ^ (k + 1) = 2 ^ (65 + k) := by
    rw [M_eq']
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcap : 2 ^ (64 + k) + 2 ^ (62 + k) < M * 2 ^ (k + 1) := by
    rw [hMshift, hp64, hp65]
    have hp : 0 < (2 : Nat) ^ (62 + k) := Nat.two_pow_pos _
    omega
  apply Nat.lt_of_not_ge
  intro hhi
  have hmul : M * 2 ^ (k + 1) ≤ M * r.tHi :=
    Nat.mul_le_mul_left M hhi
  omega

/-- One gated `μ` signal preserves the exact accumulator and ceiling
invariant.  This theorem assembles the independently proved weight,
two-limb-arithmetic, and ceiling-recurrence components into the transparent
`resStep` model used by the compiled block. -/
theorem ResInv.step (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hnlt : n + 1 < 2 ^ (64 - k))
    (hnext : (accTrue k mu (n + 1)).natAbs ≤ 2 ^ (62 + k))
    (hcelNext :
      (celStep (n + 1) r.celSq r.cel 1).1 + 1 < 2 ^ 32)
    (h : ResInv k mu n r) :
    ResInv k mu (n + 1) (resStep k (muSig mu (n + 1)) r) := by
  have hadd := h.addRange hk15
  have hsub := h.subRange
  have hacc := accStep_mu k (n + 1) r.tLo r.tHi (mu (n + 1))
    (hmu (n + 1)) hk hk15 (by omega) hnlt h.loLt h.hiLt hadd hsub
  have hceil0 := celStep_invariant (n + 1) r.cel h.cel h.celLt
  have hceil :
      CeilInv (celStep (n + 1) r.celSq r.cel 1).1 (n + 2) ∧
        (celStep (n + 1) r.celSq r.cel 1).2 =
          (celStep (n + 1) r.celSq r.cel 1).1 *
            (celStep (n + 1) r.celSq r.cel 1).1 := by
    simpa only [h.celSq] using hceil0
  unfold resStep muSig
  dsimp only
  refine
    { loLt := accStep_fst_lt
        (if mu (n + 1) = 1 then 1 else 0)
        (if mu (n + 1) = -1 then 1 else 0)
        (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi
      hiLt := accStep_snd_lt
        (if mu (n + 1) = 1 then 1 else 0)
        (if mu (n + 1) = -1 then 1 else 0)
        (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi
      acc := ?_
      bnd := hnext
      cel := hceil.1
      celSq := hceil.2
      celLt := hcelNext }
  calc
    ((accStep (if mu (n + 1) = 1 then 1 else 0)
          (if mu (n + 1) = -1 then 1 else 0)
          (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi).1 : Int) +
        (M : Int) *
          (accStep (if mu (n + 1) = 1 then 1 else 0)
            (if mu (n + 1) = -1 then 1 else 0)
            (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi).2 =
      (r.tLo : Int) + (M : Int) * r.tHi +
        mu (n + 1) * (wgt k (n + 1) : Nat) := hacc
    _ = 2 ^ (64 + k) + accTrue k mu (n + 1) := by
      rw [h.acc]
      simp only [accTrue]
      grind

/-- The transparent residue model run from `1` through `N`. -/
def resRun (k : Nat) (mu : Nat → Int) (r0 : Res) : Nat → Res
  | 0 => r0
  | n + 1 => resStep k (muSig mu (n + 1)) (resRun k mu r0 n)

theorem resFold_append (k : Nat) (xs ys : List Sig) (r : Res) :
    resFold k (xs ++ ys) r = resFold k ys (resFold k xs r) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append, resFold] using ih (resStep k x r)

/-- The list fold over the consecutive signals `1, …, N` is the indexed
`resRun`.  This is the seam used to transfer the induction to a denotation
trace once the sieve's signal theorem is available. -/
theorem resFold_range_eq_resRun (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat) :
    resFold k ((List.range N).map (fun i => muSig mu (i + 1))) r0 =
      resRun k mu r0 N := by
  induction N with
  | zero => rfl
  | succ n =>
      rw [List.range_succ, List.map_append, resFold_append]
      simpa only [List.map_cons, List.map_nil, resFold, resRun] using congrArg
        (fun r => resStep k (muSig mu (n + 1)) r) (by assumption)

/-- The updated accumulator pair used by one transparent Möbius step. -/
def stepAcc (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res) : Nat × Nat :=
  accStep (if mu n = 1 then 1 else 0) (if mu n = -1 then 1 else 0)
    (wPair k n).1 (wPair k n).2 r.tLo r.tHi

def stepAbs (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res) : Nat :=
  absBias (vBias k (stepAcc k mu n r).1 (stepAcc k mu n r).2)

def stepCel (n : Nat) (r : Res) : Nat :=
  (celStep n r.celSq r.cel 1).1

private theorem centeredDiv_pos (q B E a : Nat) (hq : 0 < q)
    (hE : E = B * q + a) :
    B ≤ E / q ∧ a < (E / q - B + 1) * q := by
  have hB : B ≤ E / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    omega
  have hd := Nat.div_add_mod E q
  rw [Nat.mul_comm q (E / q)] at hd
  have hr := Nat.mod_lt E hq
  have hu : E < (E / q + 1) * q := by
    rw [Nat.add_mul]
    omega
  constructor
  · exact hB
  · rw [Nat.add_mul, Nat.sub_mul]
    omega

private theorem centeredDiv_neg (q B E a : Nat) (hq : 0 < q) (ha : 0 < a)
    (hE : E + a = B * q) :
    E / q < B ∧ a < (B - E / q + 1) * q := by
  have hd := Nat.div_add_mod E q
  rw [Nat.mul_comm q (E / q)] at hd
  have hr := Nat.mod_lt E hq
  have hl : E / q * q ≤ E := by omega
  have hv : E / q < B := by
    apply Nat.lt_of_not_ge
    intro h
    have hm := Nat.mul_le_mul_right q h
    omega
  constructor
  · exact hv
  · rw [Nat.add_mul, Nat.sub_mul]
    have hq1 : 1 ≤ q := hq
    omega

/-- The absolute word formed after the biased right shift encloses the exact
signed accumulator to strictly less than one shifted unit.  This is the
direction-critical hypothesis `sound_of_test` needs. -/
theorem stepAbs_exact_bound (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hk15 : k ≤ 15)
    (hnext : ResInv k mu n (resStep k (muSig mu n) r)) :
    (accTrue k mu n).natAbs <
      (stepAbs k mu n r + 1) * 2 ^ (k + 1) := by
  let t := stepAcc k mu n r
  let E := t.1 + M * t.2
  let q := 2 ^ (k + 1)
  let B := 2 ^ 63
  have hlo : t.1 < M := by
    simpa only [t, stepAcc, resStep, muSig] using hnext.loLt
  have hhi : t.2 < q := by
    have hs := hnext.hiSmall
    simpa only [t, q, stepAcc, resStep, muSig] using hs
  have hv := vBias_spec k t.1 t.2 hk15 hlo hhi
  have hq : 0 < q := Nat.two_pow_pos _
  have hEcap : E < M * q := by
    have hs : t.2 + 1 ≤ q := Nat.succ_le_of_lt hhi
    dsimp only [E]
    have hm := Nat.mul_le_mul_left M hs
    have hfirst : t.1 + M * t.2 < M * (t.2 + 1) := by
      rw [Nat.mul_succ]
      omega
    exact Nat.lt_of_lt_of_le hfirst hm
  have hvM : vBias k t.1 t.2 < M := by
    rw [hv]
    exact (Nat.div_lt_iff_lt_mul hq).2 hEcap
  have habs := absBias_spec (vBias k t.1 t.2) hvM
  have henc : ((E : Nat) : Int) =
      2 ^ (64 + k) + accTrue k mu n := by
    dsimp only [E]
    rw [Int.natCast_add, Int.natCast_mul]
    simpa only [t, stepAcc, resStep, muSig] using hnext.acc
  have hbias : B * q = 2 ^ (64 + k) := by
    dsimp only [B, q]
    rw [← Nat.pow_add]
    congr 1
    omega
  by_cases hA : 0 ≤ accTrue k mu n
  · have hAnat : (((accTrue k mu n).natAbs : Nat) : Int) =
        accTrue k mu n := Int.natAbs_of_nonneg hA
    have hEI : ((E : Nat) : Int) =
        ((B * q + (accTrue k mu n).natAbs : Nat) : Int) := by
      have hbI := congrArg (fun x : Nat => (x : Int)) hbias
      push_cast at hbI
      push_cast
      rw [hAnat, hbI]
      exact henc
    have hE : E = B * q + (accTrue k mu n).natAbs := by exact_mod_cast hEI
    obtain ⟨hB, ha⟩ := centeredDiv_pos q B E (accTrue k mu n).natAbs hq hE
    have habsEq : stepAbs k mu n r = E / q - B := by
      unfold stepAbs
      change absBias (vBias k t.1 t.2) = _
      rw [habs, hv, if_pos hB]
    rw [habsEq]
    exact ha
  · have hAle : accTrue k mu n ≤ 0 := by omega
    have haPos : 0 < (accTrue k mu n).natAbs := by
      have hneg : accTrue k mu n < 0 := by omega
      exact Int.natAbs_pos.mpr (by omega)
    have hAnat : (((accTrue k mu n).natAbs : Nat) : Int) =
        -accTrue k mu n := Int.ofNat_natAbs_of_nonpos hAle
    have hEI : ((E + (accTrue k mu n).natAbs : Nat) : Int) =
        ((B * q : Nat) : Int) := by
      push_cast
      rw [henc, hAnat]
      have hbI := congrArg (fun x : Nat => (x : Int)) hbias
      push_cast at hbI
      omega
    have hE : E + (accTrue k mu n).natAbs = B * q := by exact_mod_cast hEI
    obtain ⟨hvB, ha⟩ := centeredDiv_neg q B E (accTrue k mu n).natAbs
      hq haPos hE
    have habsEq : stepAbs k mu n r = B - E / q := by
      unfold stepAbs
      change absBias (vBias k t.1 t.2) = _
      rw [habs, hv, if_neg (Nat.not_le_of_lt hvB)]
    rw [habsEq]
    exact ha

/-- Field-level form of `stepAbs_exact_bound`.  This separates the exact
two-limb encoding needed by the absolute-value argument from the stronger
`ResInv.bnd` conclusion.  The squared checker uses it to recover that bound
from its own passing predicate, avoiding a circular a-priori accumulator
bound. -/
theorem stepAbs_exact_bound_of_fields
    (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hk15 : k ≤ 15)
    (hlo : (stepAcc k mu n r).1 < M)
    (hhi : (stepAcc k mu n r).2 < 2 ^ (k + 1))
    (hacc : ((stepAcc k mu n r).1 : Int) +
      (M : Int) * (stepAcc k mu n r).2 =
        2 ^ (64 + k) + accTrue k mu n) :
    (accTrue k mu n).natAbs <
      (stepAbs k mu n r + 1) * 2 ^ (k + 1) := by
  let t := stepAcc k mu n r
  let E := t.1 + M * t.2
  let q := 2 ^ (k + 1)
  let B := 2 ^ 63
  have hlo' : t.1 < M := by simpa only [t] using hlo
  have hhi' : t.2 < q := by simpa only [t, q] using hhi
  have hv := vBias_spec k t.1 t.2 hk15 hlo' hhi'
  have hq : 0 < q := Nat.two_pow_pos _
  have hEcap : E < M * q := by
    have hs : t.2 + 1 ≤ q := Nat.succ_le_of_lt hhi'
    dsimp only [E]
    have hm := Nat.mul_le_mul_left M hs
    have hfirst : t.1 + M * t.2 < M * (t.2 + 1) := by
      rw [Nat.mul_succ]
      omega
    exact Nat.lt_of_lt_of_le hfirst hm
  have hvM : vBias k t.1 t.2 < M := by
    rw [hv]
    exact (Nat.div_lt_iff_lt_mul hq).2 hEcap
  have habs := absBias_spec (vBias k t.1 t.2) hvM
  have henc : ((E : Nat) : Int) =
      2 ^ (64 + k) + accTrue k mu n := by
    dsimp only [E]
    rw [Int.natCast_add, Int.natCast_mul]
    simpa only [t] using hacc
  have hbias : B * q = 2 ^ (64 + k) := by
    dsimp only [B, q]
    rw [← Nat.pow_add]
    congr 1
    omega
  by_cases hA : 0 ≤ accTrue k mu n
  · have hAnat : (((accTrue k mu n).natAbs : Nat) : Int) =
        accTrue k mu n := Int.natAbs_of_nonneg hA
    have hEI : ((E : Nat) : Int) =
        ((B * q + (accTrue k mu n).natAbs : Nat) : Int) := by
      have hbI := congrArg (fun x : Nat => (x : Int)) hbias
      push_cast at hbI
      push_cast
      rw [hAnat, hbI]
      exact henc
    have hE : E = B * q + (accTrue k mu n).natAbs := by
      exact_mod_cast hEI
    obtain ⟨hB, ha⟩ := centeredDiv_pos q B E
      (accTrue k mu n).natAbs hq hE
    have habsEq : stepAbs k mu n r = E / q - B := by
      unfold stepAbs
      change absBias (vBias k t.1 t.2) = _
      rw [habs, hv, if_pos hB]
    rw [habsEq]
    exact ha
  · have hAle : accTrue k mu n ≤ 0 := by omega
    have haPos : 0 < (accTrue k mu n).natAbs := by
      have hneg : accTrue k mu n < 0 := by omega
      exact Int.natAbs_pos.mpr (by omega)
    have hAnat : (((accTrue k mu n).natAbs : Nat) : Int) =
        -accTrue k mu n := Int.ofNat_natAbs_of_nonpos hAle
    have hEI : ((E + (accTrue k mu n).natAbs : Nat) : Int) =
        ((B * q : Nat) : Int) := by
      push_cast
      rw [henc, hAnat]
      have hbI := congrArg (fun x : Nat => (x : Int)) hbias
      push_cast at hbI
      omega
    have hE : E + (accTrue k mu n).natAbs = B * q := by
      exact_mod_cast hEI
    obtain ⟨hvB, ha⟩ := centeredDiv_neg q B E
      (accTrue k mu n).natAbs hq haPos hE
    have habsEq : stepAbs k mu n r = B - E / q := by
      unfold stepAbs
      change absBias (vBias k t.1 t.2) = _
      rw [habs, hv, if_neg (Nat.not_le_of_lt hvB)]
    rw [habsEq]
    exact ha

/-- The literal comparison made at one gated integer. -/
abbrev StepPass (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res) : Prop :=
  stepAbs k mu n r + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 ≤
    2 ^ 61 / stepCel n r

/-- On its machine range, one transparent step increments the violation
counter exactly when its literal comparison fails. -/
theorem resStep_viol_eq (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hk15 : k ≤ 15) (hcel : 1 ≤ stepCel n r) (hcelM : stepCel n r < M)
    (hn : n + 2 ^ (k + 2) < M) (habs : stepAbs k mu n r < 2 ^ 62)
    (hviol : r.viol + 1 < M) :
    (resStep k (muSig mu n) r).viol =
      r.viol + if StepPass k mu n r then 0 else 1 := by
  have hv := violStep_spec_of_lt k n (stepAbs k mu n r) (stepCel n r)
    1 r.viol hk15 hcel hcelM hn habs (by omega) hviol
  unfold resStep muSig
  dsimp only
  change violStep k n (stepAbs k mu n r) (stepCel n r) 1 r.viol = _
  rw [hv]
  simp only [Nat.mul_one]
  by_cases hp : StepPass k mu n r
  · rw [if_pos hp]
    have hnot : ¬(2 ^ 61 / stepCel n r < stepAbs k mu n r +
        (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) := by
      unfold StepPass at hp
      omega
    rw [if_neg hnot]
  · rw [if_neg hp]
    have hlt : 2 ^ 61 / stepCel n r < stepAbs k mu n r +
        (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 := by
      unfold StepPass at hp
      omega
    rw [if_pos hlt]

/-- Therefore a zero next counter forces a zero carry-in counter and a
passing current comparison. -/
theorem stepPass_of_next_viol_zero (k : Nat) (mu : Nat → Int) (n : Nat)
    (r : Res) (hk15 : k ≤ 15) (hcel : 1 ≤ stepCel n r)
    (hcelM : stepCel n r < M) (hn : n + 2 ^ (k + 2) < M)
    (habs : stepAbs k mu n r < 2 ^ 62) (hviol : r.viol + 1 < M)
    (hz : (resStep k (muSig mu n) r).viol = 0) :
    r.viol = 0 ∧ StepPass k mu n r := by
  rw [resStep_viol_eq k mu n r hk15 hcel hcelM hn habs hviol] at hz
  by_cases hp : StepPass k mu n r
  · simp [hp] at hz
    exact ⟨hz, hp⟩
  · simp [hp] at hz

/-- **Acceptance induction.**  A zero final counter means that every literal
comparison in the transparent run passed.  The hypotheses are exactly the
non-wrapping preconditions of `violStep_spec_of_lt`, stated prefixwise so they
can later be discharged from `resRun_inv` and the campaign endpoint. -/
theorem resRun_zero_all_pass (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat)
    (hk15 : k ≤ 15)
    (hcelLo : ∀ m, m < N → 1 ≤ stepCel (m + 1) (resRun k mu r0 m))
    (hcelHi : ∀ m, m < N → stepCel (m + 1) (resRun k mu r0 m) < M)
    (hn : ∀ m, m < N → m + 1 + 2 ^ (k + 2) < M)
    (habs : ∀ m, m < N → stepAbs k mu (m + 1) (resRun k mu r0 m) < 2 ^ 62)
    (hviol : ∀ m, m < N → (resRun k mu r0 m).viol + 1 < M)
    (hz : (resRun k mu r0 N).viol = 0) :
    ∀ m, m < N → StepPass k mu (m + 1) (resRun k mu r0 m) := by
  induction N with
  | zero => intro m hm; omega
  | succ n ih =>
      have hzStep :
          (resStep k (muSig mu (n + 1)) (resRun k mu r0 n)).viol = 0 := by
        simpa only [resRun] using hz
      obtain ⟨hzPrev, hpass⟩ := stepPass_of_next_viol_zero k mu (n + 1)
        (resRun k mu r0 n) hk15 (hcelLo n (by omega)) (hcelHi n (by omega))
        (hn n (by omega)) (habs n (by omega)) (hviol n (by omega)) hzStep
      have hprev := ih
        (fun m hm => hcelLo m (by omega))
        (fun m hm => hcelHi m (by omega))
        (fun m hm => hn m (by omega))
        (fun m hm => habs m (by omega))
        (fun m hm => hviol m (by omega)) hzPrev
      intro m hm
      by_cases hmn : m = n
      · subst m
        exact hpass
      · exact hprev m (by omega)

/-- **Window induction.**  Exact bounds on the mathematical partial sum at
each prefix propagate the register invariant through the whole transparent
run.  `hcel` is only the machine-width side condition for the next ceiling
register; source-scale campaigns discharge it from their endpoint. -/
theorem resRun_inv (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcel : ∀ m, m < N →
      (celStep (m + 1) (resRun k mu r0 m).celSq
        (resRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0) :
    ResInv k mu N (resRun k mu r0 N) := by
  induction N with
  | zero => simpa only [resRun] using h0
  | succ n ih =>
      have hprev := ih
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (fun m hm => hbnd m (by omega))
        (fun m hm => hcel m (by omega))
      simpa only [resRun] using ResInv.step k mu n (resRun k mu r0 n)
        hmu hk hk15
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (hbnd (n + 1) (Nat.le_refl _)) (hcel n (by omega)) hprev


/-! ## The rounding budget, summed over the window -/

private theorem mu_natAbs_le_one {mu : Nat → Int}
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0) (m : Nat) :
    (mu m).natAbs ≤ 1 := by
  rcases hmu m with h | h | h <;> rw [h] <;> decide

/-- **The accumulated round-to-nearest error.**  The fixed-point accumulator
tracks `2^(63+k)` times the exact partial sum to within half an ulp per term.
Everything is cleared of denominators: `D` is any common multiple of
`1, …, n`.  This is what makes a passing integer test a bound on the *real*
sum rather than on its fixed-point image. -/
theorem accTrue_close (k : Nat) (mu : Nat → Int)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0) (D : Nat) :
    ∀ n : Nat, (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      2 * (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n).natAbs
        ≤ n * D := by
  intro n
  induction n with
  | zero => intro _; simp [accTrue, numTrue]
  | succ n ih =>
      intro hdvd
      have hIH := ih (fun m h1 h2 => hdvd m h1 (Nat.le_succ_of_le h2))
      obtain ⟨e, he⟩ := hdvd (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Nat.le_refl _)
      have hDe : (D : Int) = ((n : Int) + 1) * (e : Int) := by
        rw [he]; push_cast; grind
      have hDdiv : ((D / (n + 1) : Nat) : Int) = (e : Int) := by
        rw [he, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]
      obtain ⟨hup, hdown⟩ :=
        wgt_close k (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      have hpush : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by push_cast; grind
      rw [hpush] at hup hdown
      -- the per-term error, cleared of denominators
      have hbase :
          2 * ((wgt k (n + 1) : Int) * ((n : Int) + 1) - 2 ^ (63 + k)).natAbs
            ≤ n + 1 := by omega
      have hterm :
          2 * (mu (n + 1) * ((wgt k (n + 1) : Int) * D
                - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int))).natAbs ≤ D := by
        have hfac : (wgt k (n + 1) : Int) * D
            - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)
            = (e : Int) * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)) := by
          rw [hDe, hDdiv]; grind
        rw [hfac, Int.natAbs_mul, Int.natAbs_mul]
        have hmul := mu_natAbs_le_one hmu (n + 1)
        have hee : (e : Int).natAbs = e := Int.natAbs_natCast e
        rw [hee]
        have hD' : D = (n + 1) * e := he
        calc 2 * ((mu (n + 1)).natAbs *
              (e * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs))
            ≤ 2 * (1 *
              (e * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmul)
          _ = e * (2 * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs) := by grind
          _ ≤ e * (n + 1) := Nat.mul_le_mul_left e hbase
          _ = D := by rw [hD']; exact Nat.mul_comm _ _
      have hsplit :
          accTrue k mu (n + 1) * D - 2 ^ (63 + k) * numTrue mu D (n + 1)
            = (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n)
              + mu (n + 1) * ((wgt k (n + 1) : Int) * D
                  - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)) := by
        simp only [accTrue, numTrue]; grind
      rw [hsplit]
      have htri := Int.natAbs_add_le
        (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n)
        (mu (n + 1) * ((wgt k (n + 1) : Int) * D
          - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)))
      have hexp : (n + 1) * D = n * D + D := by grind
      omega

/-- A passing transparent step is the exact cross-multiplied source-family
bound at that integer. -/
theorem StepPass.sound (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk15 : k ≤ 15) (hn : 1 ≤ n) (D : Nat) (hD : 0 < D)
    (hdvd : ∀ m, 1 ≤ m → m ≤ n → m ∣ D)
    (hnext : ResInv k mu n (resStep k (muSig mu n) r))
    (hpass : StepPass k mu n r) :
    4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hceil : CeilInv (stepCel n r) (n + 1) := by
    simpa only [stepCel, resStep, muSig] using hnext.cel
  have hV := stepAbs_exact_bound k mu n r hk15 hnext
  have happ := accTrue_close k mu hmu D n hdvd
  exact sound_of_test k n (stepCel n r) (stepAbs k mu n r)
    (accTrue k mu n) (numTrue mu D n) D hn hD hceil.1 hceil.2.1 hV happ hpass

/-- **Whole transparent-run soundness.**  A zero final counter proves the
cross-multiplied family at every integer in the run.  The remaining hypotheses
are machine-width facts and the broad exact-accumulator bound; the production
endpoint discharges them independently of the target inequality. -/
theorem resRun_zero_sound (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcelInv : ∀ m, m < N →
      (celStep (m + 1) (resRun k mu r0 m).celSq
        (resRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0)
    (hcelLo : ∀ m, m < N → 1 ≤ stepCel (m + 1) (resRun k mu r0 m))
    (hcelHi : ∀ m, m < N → stepCel (m + 1) (resRun k mu r0 m) < M)
    (hnM : ∀ m, m < N → m + 1 + 2 ^ (k + 2) < M)
    (habs : ∀ m, m < N → stepAbs k mu (m + 1) (resRun k mu r0 m) < 2 ^ 62)
    (hviol : ∀ m, m < N → (resRun k mu r0 m).viol + 1 < M)
    (hz : (resRun k mu r0 N).viol = 0) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ D, 0 < D →
      (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hpasses := resRun_zero_all_pass k mu r0 N hk15 hcelLo hcelHi hnM
    habs hviol hz
  intro n hn1 hnN D hD hdvd
  cases n with
  | zero => omega
  | succ m =>
      have hmN : m < N := by omega
      have hpass := hpasses m hmN
      have hinv := resRun_inv k mu r0 (m + 1) hmu hk hk15
        (Nat.lt_of_le_of_lt hnN hN)
        (fun j hj => hbnd j (Nat.le_trans hj hnN))
        (fun j hj => hcelInv j (by omega)) h0
      have hnext : ResInv k mu (m + 1)
          (resStep k (muSig mu (m + 1)) (resRun k mu r0 m)) := by
        simpa only [resRun] using hinv
      exact StepPass.sound k mu (m + 1) (resRun k mu r0 m) hmu hk15
        (by omega) D hD hdvd hnext hpass


/-! ## Non-interference: the sieve core never touches the residue's registers -/

/-- The register an instruction writes, if any.  A `store` writes only the
array. -/
def ainstrRegDest? : AInstr → Option Nat
  | .scalar (.mov d _) => some d
  | .scalar (.binop d _ _ _) => some d
  | .load d _ => some d
  | .store _ _ => none

/-- `S` covers every register destination of a block. -/
def RegDestsIn (S : Nat → Bool) (l : List AInstr) : Prop :=
  l.all (fun a => match ainstrRegDest? a with
    | some d => S d
    | none => true) = true

private theorem denoteAInstr_reg_frame {len idx : Nat} {s s' : AState}
    {a : AInstr} (h : denoteAInstr len idx s a = some s') {j : Nat}
    (hj : ainstrRegDest? a ≠ some j) : s'.regs j = s.regs j := by
  cases a with
  | scalar i =>
      cases i with
      | mov d src =>
          simp only [denoteAInstr, denoteInstr, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at h
          subst h
          simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
          simp only [RegState.set]
          exact if_neg (fun h => hj h.symm)
      | binop d op l r =>
          simp only [denoteAInstr, denoteInstr, Option.bind_eq_bind] at h
          cases hv : denoteOp op (denoteOperand idx s.regs l)
              (denoteOperand idx s.regs r) with
          | none => rw [hv] at h; exact absurd h (by simp)
          | some v =>
              rw [hv] at h
              simp only [Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
              simp only [RegState.set]
              exact if_neg (fun h => hj h.symm)
  | load d i =>
      obtain ⟨_, _, _, hframe⟩ := denoteAInstr_load_some h
      simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
      exact hframe j (fun h => hj h.symm)
  | store i sr =>
      obtain ⟨_, hregs, _, _⟩ := denoteAInstr_store_some h
      rw [hregs]

/-- **Register frame.**  A block leaves every register outside its destination
set untouched — `load` and `store` included. -/
theorem denoteAInstrs_reg_frame (len idx : Nat) (S : Nat → Bool) :
    ∀ (l : List AInstr), RegDestsIn S l → ∀ (s s' : AState),
      denoteAInstrs len idx s l = some s' →
      ∀ j, S j = false → s'.regs j = s.regs j := by
  intro l
  induction l with
  | nil =>
      intro _ s s' h j _
      simp only [denoteAInstrs, Option.some.injEq] at h
      exact h ▸ rfl
  | cons a l ih =>
      intro hall s s' h j hj
      have hd : (match ainstrRegDest? a with
          | some d => S d | none => true) = true :=
        (List.all_eq_true.mp hall) a (by simp)
      have hrest : RegDestsIn S l := by
        refine List.all_eq_true.mpr ?_
        intro x hx
        exact (List.all_eq_true.mp hall) x (List.mem_cons_of_mem _ hx)
      simp only [denoteAInstrs, Option.bind_eq_bind] at h
      cases hstep : denoteAInstr len idx s a with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hstep] at h
          simp only [Option.bind_some] at h
          have hne : ainstrRegDest? a ≠ some j := by
            intro hEq
            rw [hEq] at hd
            simp only at hd
            rw [hj] at hd
            exact absurd hd (by simp)
          rw [ih hrest s1 s' h j hj]
          exact denoteAInstr_reg_frame hstep hne

/-- The residue's own register file. -/
def ResidueRegs (j : Nat) : Bool :=
  decide ((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171))

/-- **Non-interference.**  Every register the sieve core writes lies outside
the residue's register file.  Together with `mobiusLiveResidue_denote` — which
says the residue writes nothing else — the two halves of the loop body are
independent: the residue's five accumulators are a function of the four
signals `65`, `79`, `80`, `133` alone, and the sieve's state is unaffected by
which residue is bolted on. -/
theorem coreBody_regDests_disjoint (c : Cfg) :
    RegDestsIn (fun j => !ResidueRegs j) c.coreBody := rfl

/-- The same for the core's initialization block. -/
theorem coreInit_regDests_disjoint (c : Cfg) :
    RegDestsIn (fun j => !ResidueRegs j) c.coreInit := by
  refine List.all_eq_true.mpr ?_
  intro x hx
  simp only [Cfg.coreInit, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨y, _, hy⟩ | h
  · rcases hy with h | h | h <;> subst h <;> rfl
  · rcases h with h | h | h | h | h <;> subst h <;> rfl

end LeanCompCert.Ports.MobiusResidueRealisation
