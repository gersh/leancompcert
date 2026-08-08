import LeanCompCert.Ports.MobiusSquaredBlock
import LeanCompCert.Ports.Section413G1Denote

/-! # Denotation of the literal root-free Möbius checker -/

namespace LeanCompCert.Ports.MobiusSquaredBlockSound

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.MobiusSquaredBlock
open LeanCompCert.Ports.Section413G1Denote

def wide (ra rb lo hi : Nat) : List Instr :=
  mulWideG 4294967295 4294967296 ra rb lo hi s0 s1 s2 s3 s4 s5 s6 s7

def mulPrefix : List Instr :=
  wide rU rU rSqLo rSqHi ++
  wide rSqLo rN rPLo rMid0 ++
  wide rSqHi rN rMid1 rTop0

def compareG : List Instr :=
  [ .binop rMid .add (.reg rMid0) (.reg rMid1)
  , .binop rCarry .lt (.reg rMid) (.reg rMid1)
  , .binop rTop .add (.reg rTop0) (.reg rCarry)
  , .binop rTopNZ .ne (.reg rTop) (.lit 0)
  , .binop rMidGT .gt (.reg rMid) (.lit (2 ^ 58))
  , .binop rMidEQ .eq (.reg rMid) (.lit (2 ^ 58))
  , .binop rLoNZ .ne (.reg rPLo) (.lit 0)
  , .binop rEqLoBad .mul (.reg rMidEQ) (.reg rLoNZ)
  , .binop rBad0 .bor (.reg rTopNZ) (.reg rMidGT)
  , .binop rBad .bor (.reg rBad0) (.reg rEqLoBad) ]

def bodyG : List Instr := mulPrefix ++ compareG

theorem body_lift : MobiusSquaredBlock.body = lift bodyG := by rfl

private theorem wide_hl (k : Nat) (s : RegState) (ra rb lo hi : Nat)
    (hra : ra < 11) (hrb : rb < 11) (hlo : lo < 11) (hhi : hi < 11)
    (hlohi : lo ≠ hi) (hs : ∀ j, s j < M) :
    srun k s (wide ra rb lo hi) lo = (MulWide.hl (s ra) (s rb)).1 ∧
    srun k s (wide ra rb lo hi) hi = (MulWide.hl (s ra) (s rb)).2 := by
  apply mulWideG_hl
  all_goals simp_all [Distinct8, NotIn8, s0, s1, s2, s3, s4, s5, s6, s7] <;> omega

private theorem wide_frame (k : Nat) (s : RegState) (ra rb lo hi j : Nat)
    (hjlo : j ≠ lo) (hjhi : j ≠ hi) (hj : j < 11) :
    srun k s (wide ra rb lo hi) j = s j := by
  apply mulWideG_frame
  all_goals simp_all [NotIn8, s0, s1, s2, s3, s4, s5, s6, s7] <;> omega

/-- The three literal multiplier traces are exactly `MulThree.squareMul`. -/
theorem prefix_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    let out := srun k s mulPrefix
    out rPLo = (MulThree.squareMul (s rU) (s rN)).lo ∧
    out rMid0 = (MulWide.hl (MulWide.hl (s rU) (s rU)).1 (s rN)).2 ∧
    out rMid1 = (MulWide.hl (MulWide.hl (s rU) (s rU)).2 (s rN)).1 ∧
    out rTop0 = (MulWide.hl (MulWide.hl (s rU) (s rU)).2 (s rN)).2 := by
  let t1 := srun k s (wide rU rU rSqLo rSqHi)
  let t2 := srun k t1 (wide rSqLo rN rPLo rMid0)
  let t3 := srun k t2 (wide rSqHi rN rMid1 rTop0)
  have h1 := wide_hl k s rU rU rSqLo rSqHi (by decide) (by decide)
    (by decide) (by decide) (by decide) hs
  have ht1N : t1 rN = s rN := wide_frame k s rU rU rSqLo rSqHi rN
    (by decide) (by decide) (by decide)
  have ht1word : ∀ j, t1 j < M := srun_lt_of_lt k _ _ hs
  have h2 := wide_hl k t1 rSqLo rN rPLo rMid0 (by decide) (by decide)
    (by decide) (by decide) (by decide) ht1word
  have ht2SqHi : t2 rSqHi = t1 rSqHi := wide_frame k t1 rSqLo rN rPLo rMid0 rSqHi
    (by decide) (by decide) (by decide)
  have ht2N : t2 rN = t1 rN := wide_frame k t1 rSqLo rN rPLo rMid0 rN
    (by decide) (by decide) (by decide)
  have ht2word : ∀ j, t2 j < M := srun_lt_of_lt k _ _ ht1word
  have h3 := wide_hl k t2 rSqHi rN rMid1 rTop0 (by decide) (by decide)
    (by decide) (by decide) (by decide) ht2word
  have ht3PLo : t3 rPLo = t2 rPLo := wide_frame k t2 rSqHi rN rMid1 rTop0 rPLo
    (by decide) (by decide) (by decide)
  have ht3Mid0 : t3 rMid0 = t2 rMid0 := wide_frame k t2 rSqHi rN rMid1 rTop0 rMid0
    (by decide) (by decide) (by decide)
  simp only [mulPrefix, srun_append]
  change t3 rPLo = _ ∧ t3 rMid0 = _ ∧ t3 rMid1 = _ ∧ t3 rTop0 = _
  change t1 rSqLo = _ ∧ t1 rSqHi = _ at h1
  change t2 rPLo = _ ∧ t2 rMid0 = _ at h2
  change t3 rMid1 = _ ∧ t3 rTop0 = _ at h3
  simp only [MulThree.squareMul, MulThree.mul128x64]
  exact ⟨ht3PLo.trans (h2.1.trans (by rw [h1.1, ht1N])),
    ht3Mid0.trans (h2.2.trans (by rw [h1.1, ht1N])),
    h3.1.trans (by rw [ht2SqHi, h1.2, ht2N, ht1N]),
    h3.2.trans (by rw [ht2SqHi, h1.2, ht2N, ht1N])⟩

/-- The literal comparison suffix returns zero exactly for `lePow122`. -/
theorem compareG_spec (k : Nat) (s : RegState) (x : MulThree.Limbs3)
    (hlo : s rPLo = x.lo)
    (hmid : (s rMid0 + s rMid1) % M = x.mid)
    (hhi : s rTop0 + (s rMid0 + s rMid1) / M = x.hi)
    (hm0 : s rMid0 < M) (hm1 : s rMid1 < M)
    (hwords : x.lo < M ∧ x.mid < M ∧ x.hi < M) :
    srun k s compareG rBad = if MulThree.lePow122 x then 0 else 1 := by
  classical
  have hc := AddWide.carry_bit (s rMid0) (s rMid1) hm0 hm1
  change (if (s rMid0 + s rMid1) % M < s rMid1 then 1 else 0) =
    (s rMid0 + s rMid1) / M at hc
  have htop : (s rTop0 + (if (s rMid0 + s rMid1) % M < s rMid1 then 1 else 0)) % M =
      x.hi := by
    rw [hc, hhi]
    exact Nat.mod_eq_of_lt hwords.2.2
  simp only [compareG, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, Nat.reduceEqDiff,
    rMid, rMid0, rMid1, rCarry, rTop,
    rTop0, rTopNZ, rMidGT, rMidEQ, rLoNZ, rPLo, rEqLoBad, rBad0, rBad,
    M, if_true, if_false] at htop ⊢
  change s 4 = x.lo at hlo
  change (s 5 + s 6) % (2 ^ 64) = x.mid at hmid
  simp only [hmid] at htop
  simp only [hlo, hmid, htop]
  have hzero : 0 % (2 ^ 64) = 0 := by decide
  have h58 : (2 ^ 58) % (2 ^ 64) = 2 ^ 58 := by decide
  rw [hzero, h58]
  simp only [MulThree.lePow122]
  by_cases ht : x.hi = 0 <;> by_cases hg : x.mid > 2 ^ 58 <;>
    by_cases he : x.mid = 2 ^ 58 <;> by_cases hl : x.lo = 0 <;>
    simp [ht, hg, he, hl] <;> omega

/-- End-to-end total semantics of the literal block. -/
theorem bodyG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    srun k s bodyG rBad =
      if MulThree.lePow122 (MulThree.squareMul (s rU) (s rN)) then 0 else 1 := by
  let t := srun k s mulPrefix
  let x := MulThree.squareMul (s rU) (s rN)
  have hp := prefix_spec k s hs
  change t rPLo = x.lo ∧ t rMid0 = _ ∧ t rMid1 = _ ∧ t rTop0 = _ at hp
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ _ hs
  have hwords : x.lo < M ∧ x.mid < M ∧ x.hi < M := by
    exact MulThree.squareMul_words (s rU) (s rN) (hs rU) (hs rN)
  have hmid : (t rMid0 + t rMid1) % M = x.mid := by
    rw [hp.2.1, hp.2.2.1]
    rfl
  have hc := AddWide.carry_bit (t rMid0) (t rMid1)
    (htword rMid0) (htword rMid1)
  change (if (t rMid0 + t rMid1) % M < t rMid1 then 1 else 0) =
    (t rMid0 + t rMid1) / M at hc
  have hhi : t rTop0 + (t rMid0 + t rMid1) / M = x.hi := by
    rw [← hc, hp.2.2.2, hp.2.1, hp.2.2.1]
    rfl
  rw [bodyG, srun_append]
  exact compareG_spec k t x hp.1 hmid hhi (htword rMid0) (htword rMid1) hwords

def initG (u n : Nat) : List Instr :=
  [.mov rU (.lit u), .mov rN (.lit n)] ++ bodyG

theorem init_lift (u n : Nat) : (MobiusSquaredBlock.program u n).init = lift (initG u n) := by
  rfl

/-- The standalone program returns zero exactly when the source squared
predicate holds.  This closes the denotation premise of `program_compiled`. -/
theorem program_denote (u n : Nat) (hu : u < M) (hn : n < M) :
    (MobiusSquaredBlock.program u n).denote =
      some (if n * u ^ 2 ≤ 2 ^ 122 then 0 else 1) := by
  let seed := srun 0 initialState [.mov rU (.lit u), .mov rN (.lit n)]
  have hseedU : seed rU = u := by
    simp [seed, srun, sdest, sval, denoteOperand, RegState.set, rU, rN,
      Nat.mod_eq_of_lt hu]
  have hseedN : seed rN = n := by
    simp [seed, srun, sdest, sval, denoteOperand, RegState.set, rU, rN,
      Nat.mod_eq_of_lt hn]
  have hseedWord : ∀ j, seed j < M := srun_lt_of_lt 0 _ _ (fun _ => M_pos)
  have hbody := bodyG_spec 0 seed hseedWord
  simp only [hseedU, hseedN] at hbody
  have hiff := MulThree.squareMul_lePow122_iff u n hu hn
  have hbody' : srun 0 seed bodyG rBad =
      if n * u ^ 2 ≤ 2 ^ 122 then 0 else 1 := by
    by_cases htest : n * u ^ 2 ≤ 2 ^ 122
    · have hle := hiff.mpr htest
      simpa only [htest, hle, if_true] using hbody
    · have hnle : ¬MulThree.lePow122 (MulThree.squareMul u n) :=
        fun hle => htest (hiff.mp hle)
      simpa only [htest, hnle, if_false] using hbody
  unfold AProgram.denote
  rw [init_lift]
  simp only [MobiusSquaredBlock.program]
  have hdef := ArrayScalarBlock.allDefined_lift_of_noDiv 1 0 (initG u n)
    initialAState (by rfl)
  rw [denoteAInstrs_eq_arun 1 0 _ _ hdef]
  simp only [List.range_zero, List.foldlM_nil, denoteAInstrs]
  change some ((arun 0 initialAState (lift (initG u n))).regs rBad) = _
  rw [ArrayScalarBlock.arun_lift_regs, initG, srun_append]
  change some (srun 0 seed bodyG rBad) = _
  rw [hbody']

/-- End-to-end compiled theorem with no denotation premise: the lowered CCIR
and emitted C return the decision bit for the exact source predicate. -/
theorem program_compiled_source (u n : Nat) (hu : u < M) (hn : n < M)
    (base : Int) (hBase : BaseOk (MobiusSquaredBlock.program u n).arrayLen base) :
    Option.bind
        (MemFragment.evalMCCSequence
          ((MobiusSquaredBlock.program u n).initialMCC base)
          (MobiusSquaredBlock.program u n).compile)
        (fun m : MemFragment.MCCState =>
          m.env ⟨(MobiusSquaredBlock.program u n).output + 1⟩) =
      some (((if n * u ^ 2 ≤ 2 ^ 122 then 0 else 1 : Nat) : Int)) := by
  apply MobiusSquaredBlock.program_compiled u n base hBase
  exact program_denote u n hu hn

end LeanCompCert.Ports.MobiusSquaredBlockSound
