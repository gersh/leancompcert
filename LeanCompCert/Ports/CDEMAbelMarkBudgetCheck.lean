import LeanCompCert.Ports.MertensCDEM
import LeanCompCert.Ports.BlockedFold

/-!
# Rolled scalar checker for the CDEM Abel marking budget

This program reuses the verified trial-division stages of `MertensCDEM`.
For each divisor `d = 2, ..., 199330`, 445 scalar rounds determine whether
`d` is squarefree.  The final round adds `floor(1000000 / d) + 1` for a
squarefree divisor and one divisor-advance step except on the last row.

The result is the compact marking budget minus its fixed `segLen + 2` seed.
The program is rolled: the emitted C contains one loop body, not 88 million
unrolled instructions.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.BlockedFold

def kBound : Nat := 199330
def segLen : Nat := 1000000
def rounds : Nat := 445
def len : Nat := kBound - 1
def seed : Nat := segLen + 2

/-- A `MertensCDEM.Cfg` carrying exactly the index-decoding parameters used
by this checker.  Its other fields are harmless witnesses for the already
proved stage-A arithmetic bounds. -/
def trialCfg : MertensCDEM.Cfg where
  lo := 2
  len := len
  rounds := rounds
  bias := 200000
  m0 := 200000
  lower := 0
  den := 1
  slack := 0
  cap := 200000
  anchorX := 0
  anchorM := 0

theorem trialCfg_admissible : MertensCDEM.Admissible trialCfg := by
  refine
    { roundsPos := by decide
      loopLt := by decide
      divLt := by decide
      candLt := by decide
      biasLt := by decide
      m0Lt := by decide
      m0Pos := by decide
      m0Hi := by decide
      capLt := by decide
      capSound := by decide
      capLtM := by decide
      denLtM := by decide
      slackLtM := by decide
      lowerLt := by decide
      anchorXLt := by decide
      anchorMLt := by decide }

def bodyC1 : List Instr :=
  [ .binop 22 .eq (.reg 6) (.lit (rounds - 1))
  , .binop 23 .sub (.lit 1) (.reg 3)
  , .binop 24 .udiv (.lit segLen) (.reg 9)
  , .binop 25 .add (.reg 24) (.lit 1) ]

def bodyC2 : List Instr :=
  [ .binop 25 .mul (.reg 25) (.reg 23)
  , .binop 26 .lt (.reg 9) (.lit kBound)
  , .binop 25 .add (.reg 25) (.reg 26) ]

def bodyC3 : List Instr :=
  [ .binop 25 .mul (.reg 25) (.reg 22)
  , .binop 0 .add (.reg 0) (.reg 25) ]

def bodyC : List Instr := bodyC1 ++ (bodyC2 ++ bodyC3)

def body : List Instr :=
  MertensCDEM.bodyA trialCfg ++ (MertensCDEM.bodyB ++ bodyC)

def initBlock : List Instr := [ .mov 0 (.lit seed) ]

def program : Program :=
  { regCount := MertensCDEM.regCount
  , loopCount := len * rounds
  , init := initBlock
  , body := body
  , epilogue := []
  , output := 0 }

structure Abs where
  acc : Nat
  t : MertensCDEM.Trial
  deriving Repr, DecidableEq

def obs (s : RegState) : Abs := ⟨s 0, ⟨s 2, s 3, s 4⟩⟩

theorem Abs.eq_of {x y : Abs} (hacc : x.acc = y.acc) (ht : x.t = y.t) :
    x = y := by
  cases x; cases y; simp_all

def reset (idx : Nat) (a : Abs) : Abs :=
  let q := idx % rounds
  ⟨a.acc,
    ⟨if q = 0 then 2 + idx / rounds else a.t.res,
     if q = 0 then 0 else a.t.sq,
     if q = 0 then 0 else a.t.par⟩⟩

def divided (idx : Nat) (a : Abs) : Abs :=
  ⟨a.acc, MertensCDEM.trialStep (idx % rounds + 2) a.t⟩

def allowanceOf (d : Nat) (t : MertensCDEM.Trial) : Nat :=
  (1 - t.sq) * (segLen / d + 1) + (if d < kBound then 1 else 0)

def accumulated (idx : Nat) (a : Abs) : Abs :=
  let last := if idx % rounds = rounds - 1 then 1 else 0
  let d := 2 + idx / rounds
  ⟨(a.acc + last * allowanceOf d a.t) % M, a.t⟩

def gstep (idx : Nat) (a : Abs) : Abs :=
  accumulated idx (divided idx (reset idx a))

def step (idx : Nat) (s : RegState) : RegState := srun idx s body

def Inv (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 3 ≤ 1 ∧ s 4 ≤ 1

private theorem msub_bit (x : Nat) (hx : x ≤ 1) :
    (1 + (M - x)) % M = 1 - x := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
  · rw [show 1 + (M - 0) = 1 + M by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by decide)
  · rw [show 1 + (M - 1) = M by decide, Nat.mod_self]

theorem bodyC1_spec (idx : Nat) (s : RegState) (h3 : s 3 ≤ 1)
    (h9pos : 0 < s 9) :
    let s' := srun idx s bodyC1
    s' 0 = s 0 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 6 = s 6 ∧ s' 9 = s 9 ∧
      s' 22 = (if s 6 = rounds - 1 then 1 else 0) ∧
      s' 23 = 1 - s 3 ∧ s' 25 = segLen / s 9 + 1 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hrM : (rounds - 1) % M = rounds - 1 := by
    exact Nat.mod_eq_of_lt (by decide)
  have hsegM : segLen % M = segLen := by
    exact Nat.mod_eq_of_lt (by decide)
  have hdivM : (segLen / s 9) % M = segLen / s 9 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide))
  have h9ne : s 9 ≠ 0 := by omega
  have htermLt : segLen / s 9 + 1 < M := by
    have := Nat.div_le_self segLen (s 9)
    have : segLen + 1 < M := by decide
    omega
  have htermM : (segLen / s 9 + 1) % M = segLen / s 9 + 1 :=
    Nat.mod_eq_of_lt htermLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [bodyC1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      h1M, hrM, hsegM, hdivM, htermM, h9ne, msub_bit _ h3]

theorem bodyC2_spec (idx : Nat) (s : RegState) (h3 : s 3 ≤ 1)
    (h25 : s 25 = segLen / s 9 + 1) (h23 : s 23 = 1 - s 3) :
    let s' := srun idx s bodyC2
    s' 0 = s 0 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 6 = s 6 ∧ s' 9 = s 9 ∧ s' 22 = s 22 ∧
      s' 25 = allowanceOf (s 9) ⟨s 2, s 3, s 4⟩ := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hkM : kBound % M = kBound := Nat.mod_eq_of_lt (by decide)
  have htermLt : segLen / s 9 + 1 < M := by
    have := Nat.div_le_self segLen (s 9)
    have : segLen + 1 < M := by decide
    omega
  have htermSuccLt : segLen / s 9 + 1 + 1 < M := by
    have := Nat.div_le_self segLen (s 9)
    have : segLen + 2 < M := by decide
    omega
  rcases (show s 3 = 0 ∨ s 3 = 1 by omega) with hs3 | hs3 <;>
    by_cases hk : s 9 < kBound <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [bodyC2, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      h25, h23, hs3, hk, hkM, allowanceOf, Nat.mod_eq_of_lt htermLt,
      Nat.mod_eq_of_lt htermSuccLt, h1M]

theorem bodyC3_spec (idx : Nat) (s : RegState)
    (h22 : s 22 = (if s 6 = rounds - 1 then 1 else 0))
    (h25 : s 25 = allowanceOf (s 9) ⟨s 2, s 3, s 4⟩)
    (hallow : allowanceOf (s 9) ⟨s 2, s 3, s 4⟩ < M) :
    let s' := srun idx s bodyC3
    s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 0 = (s 0 +
        (if s 6 = rounds - 1 then 1 else 0) *
          allowanceOf (s 9) ⟨s 2, s 3, s 4⟩) % M := by
  by_cases hlast : s 6 = rounds - 1 <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [bodyC3, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      h22, h25, hlast, Nat.mod_eq_of_lt hallow, Nat.add_mod]

theorem allowanceOf_lt_M (d : Nat) (t : MertensCDEM.Trial)
    (hsq : t.sq ≤ 1) : allowanceOf d t < M := by
  have hterm : segLen / d + 1 ≤ segLen + 1 := by
    have := Nat.div_le_self segLen d
    omega
  have hcap : segLen + 2 < M := by decide
  rcases (show t.sq = 0 ∨ t.sq = 1 by omega) with h | h <;>
    simp [allowanceOf, h] <;> split <;> omega

theorem bodyC_spec (idx : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (h3 : s 3 ≤ 1) (h9pos : 0 < s 9) :
    let s' := srun idx s bodyC
    s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 0 = (s 0 +
        (if s 6 = rounds - 1 then 1 else 0) *
          allowanceOf (s 9) ⟨s 2, s 3, s 4⟩) % M := by
  let s1 := srun idx s bodyC1
  let s2 := srun idx s1 bodyC2
  have hC1 := bodyC1_spec idx s h3 h9pos
  simp only [s1] at hC1
  have hC2 := bodyC2_spec idx s1 (by
      change (srun idx s bodyC1) 3 ≤ 1
      rw [hC1.2.2.1]
      exact h3)
    (by dsimp only [s1]; rw [hC1.2.2.2.2.2.1]; exact hC1.2.2.2.2.2.2.2.2)
    (by dsimp only [s1]; rw [hC1.2.2.1]; exact hC1.2.2.2.2.2.2.2.1)
  simp only [s1, s2] at hC2
  have hallow : allowanceOf (s1 9) ⟨s1 2, s1 3, s1 4⟩ < M :=
    allowanceOf_lt_M _ _ (by
      change (srun idx s bodyC1) 3 ≤ 1
      rw [hC1.2.2.1]
      exact h3)
  have h22 : s2 22 = (if s2 6 = rounds - 1 then 1 else 0) := by
    dsimp only [s2, s1]
    rw [hC2.2.2.2.2.2.2.1]
    simp only [hC2.2.2.2.2.1, hC1.2.2.2.2.1,
      hC1.2.2.2.2.2.2.1]
  have h25 : s2 25 = allowanceOf (s2 9) ⟨s2 2, s2 3, s2 4⟩ := by
    dsimp only [s2, s1]
    rw [hC2.2.2.2.2.2.2.2, hC2.2.2.2.2.2.1, hC2.2.1,
      hC2.2.2.1, hC2.2.2.2.1]
  have hallow2 : allowanceOf (s2 9) ⟨s2 2, s2 3, s2 4⟩ < M := by
    apply allowanceOf_lt_M
    dsimp only [s2, s1]
    rw [hC2.2.2.1, hC1.2.2.1]
    exact h3
  have hC3 := bodyC3_spec idx s2 h22 h25 hallow2
  simp only [s1, s2] at hC3
  rw [bodyC, srun_append, srun_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hC3.1, hC2.2.1, hC1.2.1]
  · rw [hC3.2.1, hC2.2.2.1, hC1.2.2.1]
  · rw [hC3.2.2.1, hC2.2.2.2.1, hC1.2.2.2.1]
  · rw [hC3.2.2.2, hC2.1, hC1.1]
    simp only [hC2.2.2.2.2.1, hC1.2.2.2.2.1,
      hC2.2.2.2.2.2.1, hC1.2.2.2.2.2.1,
      hC2.2.1, hC1.2.1, hC2.2.2.1, hC1.2.2.1,
      hC2.2.2.2.1, hC1.2.2.2.1]

theorem bodyC1_defined (idx : Nat) (s : RegState) (h9 : s 9 ≠ 0) :
    SAllDefined idx s bodyC1 := by
  simp [bodyC1, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, h9]

theorem bodyC2_defined (idx : Nat) (s : RegState) :
    SAllDefined idx s bodyC2 := by
  simp [bodyC2, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set]

theorem bodyC3_defined (idx : Nat) (s : RegState) :
    SAllDefined idx s bodyC3 := by
  simp [bodyC3, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set]

theorem bodyC_defined (idx : Nat) (s : RegState) (h9 : s 9 ≠ 0) :
    SAllDefined idx s bodyC := by
  rw [bodyC, SAllDefined_append, SAllDefined_append]
  exact ⟨bodyC1_defined idx s h9,
    bodyC2_defined idx (srun idx s bodyC1),
    bodyC3_defined idx (srun idx (srun idx s bodyC1) bodyC2)⟩

theorem body_denote (idx : Nat) (s : RegState) (hidx : idx < len * rounds)
    (hI : Inv s) : denoteInstrs idx s body = some (step idx s) := by
  have hs3 := hI.2.1
  have hs4 := hI.2.2
  have hA := MertensCDEM.bodyA_spec trialCfg idx s trialCfg_admissible
    hI.1 hidx
  let sA := srun idx s (MertensCDEM.bodyA trialCfg)
  have hq : idx % rounds < rounds := Nat.mod_lt _ (by decide)
  have hBdef : SAllDefined idx sA MertensCDEM.bodyB :=
    MertensCDEM.bodyB_defined idx sA (by
      dsimp only [sA]
      rw [hA.2.2.2.1]
      simp only [trialCfg]
      omega)
  let sB := srun idx sA MertensCDEM.bodyB
  have hB := MertensCDEM.bodyB_spec idx (idx % rounds + 2) sA
    (srun_lt_of_lt idx _ s hI.1) hA.2.2.2.1 (by omega)
    (Nat.lt_trans (by omega) (by decide : rounds + 2 < M))
    (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.1]; split <;> omega)
    (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.2]; split <;> omega)
  have h9pos : 0 < sB 9 := by
    have hB9 : sB 9 = sA 9 := by simpa only [sB] using hB.2.2.2.2.1
    have hA9 : sA 9 = trialCfg.lo + idx / trialCfg.rounds := by
      simpa only [sA] using hA.2.2.2.2.1
    rw [hB9, hA9]
    simp only [trialCfg]
    show 0 < 2 + idx / rounds
    exact Nat.add_pos_left (by decide) _
  apply denoteInstrs_eq_srun
  rw [body, SAllDefined_append, SAllDefined_append]
  exact ⟨MertensCDEM.bodyA_defined trialCfg idx s (by decide), hBdef,
    bodyC_defined idx sB (by exact Nat.ne_of_gt h9pos)⟩

theorem body_obs (idx : Nat) (s : RegState) (hidx : idx < len * rounds)
    (hI : Inv s) : obs (step idx s) = gstep idx (obs s) := by
  have hs3 := hI.2.1
  have hs4 := hI.2.2
  have hA := MertensCDEM.bodyA_spec trialCfg idx s trialCfg_admissible
    hI.1 hidx
  let sA := srun idx s (MertensCDEM.bodyA trialCfg)
  have hAlt : ∀ j, sA j < M := srun_lt_of_lt idx _ s hI.1
  have hq : idx % rounds < rounds := Nat.mod_lt _ (by decide)
  have hB := MertensCDEM.bodyB_spec idx (idx % rounds + 2) sA hAlt
    hA.2.2.2.1 (by omega)
    (Nat.lt_trans (by omega) (by decide : rounds + 2 < M))
    (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.1]; split <;> omega)
    (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.2]; split <;> omega)
  let sB := srun idx sA MertensCDEM.bodyB
  have hBlt : ∀ j, sB j < M := srun_lt_of_lt idx _ sA hAlt
  have hB3 : sB 3 ≤ 1 := by
    dsimp only [sB]
    rw [hB.2.2.2.2.2.2.1]
    exact (MertensCDEM.trialStep_bits _ _
      (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.1];
          by_cases h : idx % trialCfg.rounds = 0 <;> simp [h, hs3])
      (by dsimp only [sA]; rw [hA.2.2.2.2.2.2.2];
          by_cases h : idx % trialCfg.rounds = 0 <;> simp [h, hs4])).1
  have hB9pos : 0 < sB 9 := by
    have hB9 : sB 9 = sA 9 := by simpa only [sB] using hB.2.2.2.2.1
    have hA9 : sA 9 = trialCfg.lo + idx / trialCfg.rounds := by
      simpa only [sA] using hA.2.2.2.2.1
    rw [hB9, hA9]
    simp only [trialCfg]
    show 0 < 2 + idx / rounds
    exact Nat.add_pos_left (by decide) _
  have hC := bodyC_spec idx sB hBlt hB3 hB9pos
  have hA0 : sA 0 = s 0 := by simpa only [sA] using hA.1
  have hA6 : sA 6 = idx % rounds := by
    simpa only [sA, trialCfg] using hA.2.2.1
  have hA9 : sA 9 = 2 + idx / rounds := by
    simpa only [sA, trialCfg] using hA.2.2.2.2.1
  have hA2 : sA 2 = if idx % rounds = 0 then 2 + idx / rounds else s 2 := by
    simpa only [sA, trialCfg] using hA.2.2.2.2.2.1
  have hA3 : sA 3 = if idx % rounds = 0 then 0 else s 3 := by
    dsimp only [sA]
    rw [hA.2.2.2.2.2.2.1]
    simp only [trialCfg]
    rfl
  have hA4 : sA 4 = if idx % rounds = 0 then 0 else s 4 := by
    dsimp only [sA]
    rw [hA.2.2.2.2.2.2.2]
    simp only [trialCfg]
    rfl
  have hB0 : sB 0 = sA 0 := by simpa only [sB] using hB.1
  have hB6 : sB 6 = sA 6 := by simpa only [sB] using hB.2.2.1
  have hB9 : sB 9 = sA 9 := by simpa only [sB] using hB.2.2.2.2.1
  have hB2 : sB 2 = (MertensCDEM.trialStep (idx % rounds + 2)
      ⟨sA 2, sA 3, sA 4⟩).res := by simpa only [sB] using hB.2.2.2.2.2.1
  have hB3eq : sB 3 = (MertensCDEM.trialStep (idx % rounds + 2)
      ⟨sA 2, sA 3, sA 4⟩).sq := by simpa only [sB] using hB.2.2.2.2.2.2.1
  have hB4 : sB 4 = (MertensCDEM.trialStep (idx % rounds + 2)
      ⟨sA 2, sA 3, sA 4⟩).par := by simpa only [sB] using hB.2.2.2.2.2.2.2
  have hsplit : step idx s = srun idx sB bodyC := by
    simp [step, body, sA, sB, srun_append]
  rw [hsplit]
  apply Abs.eq_of
  · show (srun idx sB bodyC) 0 = _
    rw [hC.2.2.2]
    simp only [gstep, accumulated, divided, reset, obs, trialCfg]
    rw [hB0, hA0, hB6, hA6, hB9, hA9, hB2, hB3eq, hB4,
      hA2, hA3, hA4]
  · apply MertensCDEM.Trial.eq_of
    · simp only [obs, gstep, accumulated, divided, reset, trialCfg]
      rw [hC.1, hB2, hA2, hA3, hA4]
    · simp only [obs, gstep, accumulated, divided, reset, trialCfg]
      rw [hC.2.1, hB3eq, hA2, hA3, hA4]
    · simp only [obs, gstep, accumulated, divided, reset, trialCfg]
      rw [hC.2.2.1, hB4, hA2, hA3, hA4]

theorem step_inv (idx : Nat) (s : RegState) (hidx : idx < len * rounds)
    (hI : Inv s) : Inv (step idx s) := by
  have hs3 := hI.2.1
  have hs4 := hI.2.2
  have hobs := body_obs idx s hidx hI
  refine ⟨srun_lt_of_lt idx body s hI.1, ?_, ?_⟩
  · show (obs (step idx s)).t.sq ≤ 1
    rw [hobs]
    exact (MertensCDEM.trialStep_bits _ _
      (by show (if idx % rounds = 0 then 0 else s 3) ≤ 1;
          by_cases h : idx % rounds = 0 <;> simp [h, hs3])
      (by show (if idx % rounds = 0 then 0 else s 4) ≤ 1;
          by_cases h : idx % rounds = 0 <;> simp [h, hs4])).1
  · show (obs (step idx s)).t.par ≤ 1
    rw [hobs]
    exact (MertensCDEM.trialStep_bits _ _
      (by show (if idx % rounds = 0 then 0 else s 3) ≤ 1;
          by_cases h : idx % rounds = 0 <;> simp [h, hs3])
      (by show (if idx % rounds = 0 then 0 else s 4) ≤ 1;
          by_cases h : idx % rounds = 0 <;> simp [h, hs4])).2

end LeanCompCert.Ports.CDEMAbelMarkBudgetCheck
