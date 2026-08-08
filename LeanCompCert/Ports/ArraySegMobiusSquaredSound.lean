import LeanCompCert.Ports.ArraySegMobiusSquared
import LeanCompCert.Ports.MobiusSquaredBlockSound

/-!
# Denotation of the production root-free Möbius test suffix

This module connects the literal register allocation in
`ArraySegSieve.mobiusSquaredTestBody` to `Verified.MulThree.squareMul` and the
exact source predicate.  It is kept separate from `ArraySegSieve` so changing
the production endpoint does not force Lean to re-elaborate the monolithic
segmented-sieve definition file.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredSound

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.Section413G1Denote

def wide (ra rb lo hi : Nat) : List Instr :=
  mulWideG 4294967295 4294967296 ra rb lo hi 177 178 179 180 181 182 183 184

def prefixG : List Instr :=
  wide 166 166 168 169 ++
  wide 168 167 170 171 ++
  wide 169 167 172 173

def compareG : List Instr :=
  [ .binop 174 .add (.reg 171) (.reg 172)
  , .binop 175 .lt (.reg 174) (.reg 172)
  , .binop 176 .add (.reg 173) (.reg 175)
  , .binop 185 .ne (.reg 176) (.lit 0)
  , .binop 186 .gt (.reg 174) (.lit (2 ^ 58))
  , .binop 187 .eq (.reg 174) (.lit (2 ^ 58))
  , .binop 188 .ne (.reg 170) (.lit 0)
  , .binop 189 .mul (.reg 187) (.reg 188)
  , .binop 190 .bor (.reg 185) (.reg 186)
  , .binop 191 .bor (.reg 190) (.reg 189) ]

def checkerG : List Instr := prefixG ++ compareG

def prepG (k : Nat) : List Instr :=
  [ .binop 165 .add (.reg 65) (.lit (2 ^ (k + 2) - 1))
  , .binop 165 .lshr (.reg 165) (.lit (k + 2))
  , .binop 166 .add (.reg 159) (.reg 165)
  , .binop 166 .add (.reg 166) (.lit 1)
  , .binop 167 .add (.reg 65) (.lit 1) ]

def gateG : List Instr :=
  [ .binop 177 .mul (.reg 191) (.reg 133)
  , .binop rMViol .add (.reg rMViol) (.reg 177) ]

def testG (k : Nat) : List Instr := prepG k ++ checkerG ++ gateG

theorem test_lift (k : Nat) : mobiusSquaredTestBody k = lift (testG k) := by
  rfl

private theorem wide_hl (idx : Nat) (s : RegState) (ra rb lo hi : Nat)
    (hra : ra < 177) (hrb : rb < 177) (hlo : lo < 177) (hhi : hi < 177)
    (hlohi : lo ≠ hi) (hs : ∀ j, s j < M) :
    srun idx s (wide ra rb lo hi) lo = (MulWide.hl (s ra) (s rb)).1 ∧
    srun idx s (wide ra rb lo hi) hi = (MulWide.hl (s ra) (s rb)).2 := by
  apply mulWideG_hl
  all_goals simp_all [Distinct8, NotIn8] <;> omega

private theorem wide_frame (idx : Nat) (s : RegState) (ra rb lo hi j : Nat)
    (hjlo : j ≠ lo) (hjhi : j ≠ hi) (hj : j < 177) :
    srun idx s (wide ra rb lo hi) j = s j := by
  apply mulWideG_frame
  all_goals simp_all [NotIn8] <;> omega

/-- The three production multiplier traces compute the exact three limbs of
`(s 167) * (s 166)^2`. -/
theorem prefixG_spec (idx : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    let out := srun idx s prefixG
    out 170 = (MulThree.squareMul (s 166) (s 167)).lo ∧
    out 171 = (MulWide.hl (MulWide.hl (s 166) (s 166)).1 (s 167)).2 ∧
    out 172 = (MulWide.hl (MulWide.hl (s 166) (s 166)).2 (s 167)).1 ∧
    out 173 = (MulWide.hl (MulWide.hl (s 166) (s 166)).2 (s 167)).2 := by
  let t1 := srun idx s (wide 166 166 168 169)
  let t2 := srun idx t1 (wide 168 167 170 171)
  let t3 := srun idx t2 (wide 169 167 172 173)
  have h1 := wide_hl idx s 166 166 168 169 (by decide) (by decide)
    (by decide) (by decide) (by decide) hs
  have ht1N : t1 167 = s 167 := wide_frame idx s 166 166 168 169 167
    (by decide) (by decide) (by decide)
  have ht1word : ∀ j, t1 j < M := srun_lt_of_lt idx _ _ hs
  have h2 := wide_hl idx t1 168 167 170 171 (by decide) (by decide)
    (by decide) (by decide) (by decide) ht1word
  have ht2SqHi : t2 169 = t1 169 := wide_frame idx t1 168 167 170 171 169
    (by decide) (by decide) (by decide)
  have ht2N : t2 167 = t1 167 := wide_frame idx t1 168 167 170 171 167
    (by decide) (by decide) (by decide)
  have ht2word : ∀ j, t2 j < M := srun_lt_of_lt idx _ _ ht1word
  have h3 := wide_hl idx t2 169 167 172 173 (by decide) (by decide)
    (by decide) (by decide) (by decide) ht2word
  have ht3Lo : t3 170 = t2 170 := wide_frame idx t2 169 167 172 173 170
    (by decide) (by decide) (by decide)
  have ht3Mid0 : t3 171 = t2 171 := wide_frame idx t2 169 167 172 173 171
    (by decide) (by decide) (by decide)
  simp only [prefixG, srun_append]
  change t3 170 = _ ∧ t3 171 = _ ∧ t3 172 = _ ∧ t3 173 = _
  change t1 168 = _ ∧ t1 169 = _ at h1
  change t2 170 = _ ∧ t2 171 = _ at h2
  change t3 172 = _ ∧ t3 173 = _ at h3
  simp only [MulThree.squareMul, MulThree.mul128x64]
  exact ⟨ht3Lo.trans (h2.1.trans (by rw [h1.1, ht1N])),
    ht3Mid0.trans (h2.2.trans (by rw [h1.1, ht1N])),
    h3.1.trans (by rw [ht2SqHi, h1.2, ht2N, ht1N]),
    h3.2.trans (by rw [ht2SqHi, h1.2, ht2N, ht1N])⟩

/-- The production comparison suffix returns zero exactly for `lePow122`. -/
theorem compareG_spec (idx : Nat) (s : RegState) (x : MulThree.Limbs3)
    (hlo : s 170 = x.lo)
    (hmid : (s 171 + s 172) % M = x.mid)
    (hhi : s 173 + (s 171 + s 172) / M = x.hi)
    (hm0 : s 171 < M) (hm1 : s 172 < M)
    (hwords : x.lo < M ∧ x.mid < M ∧ x.hi < M) :
    srun idx s compareG 191 = if MulThree.lePow122 x then 0 else 1 := by
  classical
  have hc := AddWide.carry_bit (s 171) (s 172) hm0 hm1
  change (if (s 171 + s 172) % M < s 172 then 1 else 0) =
    (s 171 + s 172) / M at hc
  have htop : (s 173 + (if (s 171 + s 172) % M < s 172 then 1 else 0)) % M =
      x.hi := by
    rw [hc, hhi]
    exact Nat.mod_eq_of_lt hwords.2.2
  simp only [compareG, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, Nat.reduceEqDiff, M, if_true, if_false] at htop ⊢
  change s 170 = x.lo at hlo
  change (s 171 + s 172) % (2 ^ 64) = x.mid at hmid
  simp only [hmid] at htop
  simp only [hlo, hmid, htop]
  have hzero : 0 % (2 ^ 64) = 0 := by decide
  have h58 : (2 ^ 58) % (2 ^ 64) = 2 ^ 58 := by decide
  rw [hzero, h58]
  simp only [MulThree.lePow122]
  by_cases ht : x.hi = 0 <;> by_cases hg : x.mid > 2 ^ 58 <;>
    by_cases he : x.mid = 2 ^ 58 <;> by_cases hl : x.lo = 0 <;>
    simp [ht, hg, he, hl] <;> omega

/-- End-to-end total semantics of the production three-word checker. -/
theorem checkerG_spec (idx : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun idx s checkerG 191 =
      if MulThree.lePow122 (MulThree.squareMul (s 166) (s 167)) then 0 else 1 := by
  let t := srun idx s prefixG
  let x := MulThree.squareMul (s 166) (s 167)
  have hp := prefixG_spec idx s hs
  change t 170 = x.lo ∧ t 171 = _ ∧ t 172 = _ ∧ t 173 = _ at hp
  have htword : ∀ j, t j < M := srun_lt_of_lt idx _ _ hs
  have hwords : x.lo < M ∧ x.mid < M ∧ x.hi < M :=
    MulThree.squareMul_words (s 166) (s 167) (hs 166) (hs 167)
  have hmid : (t 171 + t 172) % M = x.mid := by
    rw [hp.2.1, hp.2.2.1]
    rfl
  have hc := AddWide.carry_bit (t 171) (t 172) (htword 171) (htword 172)
  change (if (t 171 + t 172) % M < t 172 then 1 else 0) =
    (t 171 + t 172) / M at hc
  have hhi : t 173 + (t 171 + t 172) / M = x.hi := by
    rw [← hc, hp.2.2.2, hp.2.1, hp.2.2.1]
    rfl
  rw [checkerG, srun_append]
  exact compareG_spec idx t x hp.1 hmid hhi (htword 171) (htword 172) hwords

/-! ## Input preparation and gated counter update -/

/-- Machine-word form of `ceil(n / 2^(k+2))`. -/
def ceilWord (k n : Nat) : Nat :=
  (((n + (2 ^ (k + 2) - 1) % M) % M) >>> ((k + 2) % M)) % M

/-- Machine-word rounding majorant prepared for the squared checker. -/
def uWord (k n absV : Nat) : Nat :=
  (((absV + ceilWord k n) % M) + 1 % M) % M

def nWord (n : Nat) : Nat := (n + 1 % M) % M

theorem prepG_spec (idx k : Nat) (s : RegState) :
    let out := srun idx s (prepG k)
    out 166 = uWord k (s 65) (s 159) ∧ out 167 = nWord (s 65) := by
  simp only [prepG, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, Nat.reduceEqDiff, if_true, if_false, ceilWord, uWord, nWord]
  exact ⟨trivial, trivial⟩

/-- Source-predicate form of the checker theorem. -/
theorem checkerG_nat_spec (idx : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun idx s checkerG 191 =
      if s 167 * s 166 ^ 2 ≤ 2 ^ 122 then 0 else 1 := by
  have hchecker := checkerG_spec idx s hs
  have hiff := MulThree.squareMul_lePow122_iff (s 166) (s 167)
    (hs 166) (hs 167)
  by_cases htest : s 167 * s 166 ^ 2 ≤ 2 ^ 122
  · have hle := hiff.mpr htest
    simpa only [htest, hle, if_true] using hchecker
  · have hnle : ¬MulThree.lePow122 (MulThree.squareMul (s 166) (s 167)) :=
      fun hle => htest (hiff.mp hle)
    simpa only [htest, hnle, if_false] using hchecker

theorem checkerG_frame_viol (idx : Nat) (s : RegState) :
    srun idx s checkerG rMViol = s rMViol :=
  srun_frame idx rMViol checkerG (by rfl) s

theorem checkerG_frame_gate (idx : Nat) (s : RegState) :
    srun idx s checkerG 133 = s 133 :=
  srun_frame idx 133 checkerG (by rfl) s

theorem prepG_frame_viol (idx k : Nat) (s : RegState) :
    srun idx s (prepG k) rMViol = s rMViol :=
  srun_frame idx rMViol (prepG k) (by rfl) s

theorem prepG_frame_gate (idx k : Nat) (s : RegState) :
    srun idx s (prepG k) 133 = s 133 :=
  srun_frame idx 133 (prepG k) (by rfl) s

theorem gateG_spec (idx : Nat) (s : RegState) :
    srun idx s gateG rMViol = (s rMViol + s 191 * s 133) % M := by
  simp only [gateG, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, rMViol, Nat.reduceEqDiff, if_true, if_false]
  simp [Nat.add_mod]

end LeanCompCert.Ports.ArraySegMobiusSquaredSound
