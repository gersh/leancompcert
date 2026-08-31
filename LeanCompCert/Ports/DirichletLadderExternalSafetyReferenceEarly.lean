import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLoad

/-! Historical body instructions 26--50: the first eight reference flags.

The block is split at every update of `rViol`.  This avoids asking the
elaborator to normalize the exponential cross product of eight comparisons.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalEarly (c : Cfg) : List AInstr := (c.bodyBlock.drop 26).take 25

def early1 : List AInstr :=
  [ .scalar (.binop 33 .eq (.reg 21) (.reg rPrevTag))
  , .scalar (.binop 34 .sub (.lit 1) (.reg 33))
  , .scalar (.binop 35 .ge (.reg 21) (.reg rPrevTag))
  , .scalar (.binop 36 .sub (.lit 1) (.reg 35))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 36)) ]

def early2 : List AInstr :=
  [ .scalar (.binop 37 .sub (.lit 1) (.reg rPrevLast))
  , .scalar (.binop 38 .mul (.reg 34) (.reg 37))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 38)) ]

def early3 : List AInstr :=
  [ .scalar (.binop 39 .mul (.reg 33) (.reg rPrevLast))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 39)) ]

def early4 : List AInstr :=
  [ .scalar (.binop 40 .add (.reg rPrevBlk) (.lit 1))
  , .scalar (.binop 41 .mul (.reg 33) (.reg 40))
  , .scalar (.binop 42 .ne (.reg 22) (.reg 41))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 42)) ]

def early5 : List AInstr :=
  [ .scalar (.binop 43 .mul (.reg 33) (.reg rPrevUpper))
  , .scalar (.binop 44 .ne (.reg 23) (.reg 43))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 44)) ]

def early6 : List AInstr :=
  [ .scalar (.binop 45 .add (.reg 23) (.reg 24))
  , .scalar (.binop 46 .ne (.reg 25) (.reg 45))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 46)) ]

def early7 : List AInstr :=
  [ .scalar (.binop 47 .gt (.reg 28) (.lit 1))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 47)) ]

def early8 : List AInstr :=
  [ .scalar (.binop 48 .eq (.reg 28) (.lit 1))
  , .scalar (.binop 49 .gt (.reg 27) (.lit maxStat))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 49)) ]

theorem historicalEarly_eq_parts (c : Cfg) :
    historicalEarly c =
      early1 ++ early2 ++ early3 ++ early4 ++ early5 ++ early6 ++ early7 ++ early8 := by
  rfl

def earlyConditions (words : List Nat) (st : RefState) (idx : Nat) :
    List Bool :=
  let W : Nat → Nat := fun i => words.getD i 0
  let b := recW * idx
  let tag := W b
  let blk := W (b + 1)
  let lower := W (b + 2)
  let slots := W (b + 3)
  let upper := W (b + 4)
  let stat := W (b + 6)
  let isL := W (b + 7)
  let same := tag == st.prevTag
  [ tag < st.prevTag
  , !same && st.prevLast != 1
  , same && st.prevLast == 1
  , blk != (if same then st.prevBlk + 1 else 0)
  , lower != (if same then st.prevUpper else 0)
  , upper != lower + slots
  , isL > 1
  , stat > maxStat ]

set_option maxRecDepth 12000
set_option maxHeartbeats 500000

private theorem one_add_M_sub_one : 1 + (M - 1) = M := by
  have := one_lt_M
  omega

private theorem one_add_M_sub_zero : 1 + (M - 0) = M + 1 := by omega

private theorem four_lt_M : 4 < M := by decide

private theorem zero_eq_iff_eq_zero (n : Nat) : 0 = n ↔ n = 0 :=
  ⟨Eq.symm, Eq.symm⟩

theorem early1_result
    (idx n tag prevTag : Nat) (s : AState)
    (hv : s.regs rViol = n) (htag : s.regs 21 = tag)
    (hprev : s.regs rPrevTag = prevTag) (hn : n + 1 < M) :
    let out := arun idx s early1
    out.regs rViol = bump (tag < prevTag) n ∧
    out.regs 33 = (if tag = prevTag then 1 else 0) ∧
    out.regs 34 = (if tag = prevTag then 0 else 1) := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hp1 : s.regs 1 = prevTag := by simpa [rPrevTag] using hprev
  have hn0 : n < M := by omega
  by_cases heq : tag = prevTag <;> by_cases hlt : tag < prevTag
  <;> by_cases hge : prevTag ≤ tag
  <;> dsimp [early1, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol, rPrevTag]
  <;> rw [hv0, htag, hp1]
  <;> simp [heq, hlt, hge, bump, one_add_M_sub_one,
    one_add_M_sub_zero, Nat.add_mod_right, Nat.add_mod_left,
    Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt one_lt_M]
  <;> omega

theorem early2_result
    (idx n prevLast : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n)
    (hnew : s.regs 34 = if same then 0 else 1)
    (hlast : s.regs rPrevLast = prevLast)
    (hlast01 : prevLast ≤ 1) (hn : n + 1 < M) :
    (arun idx s early2).regs rViol =
      bump (!same && prevLast != 1) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hl10 : s.regs 10 = prevLast := by simpa [rPrevLast] using hlast
  have hn0 : n < M := by omega
  cases same <;> by_cases hp0 : prevLast = 0 <;> by_cases hp1 : prevLast = 1
  <;> dsimp [early2, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol, rPrevLast]
  <;> rw [hv0, hnew, hl10]
  <;> simp [hp0, hp1, bump, one_add_M_sub_one, one_add_M_sub_zero,
    Nat.add_mod_right, Nat.add_mod_left, Nat.mod_eq_of_lt hn0,
    Nat.mod_eq_of_lt hn]
  <;> omega

theorem early3_result
    (idx n prevLast : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hlast : s.regs rPrevLast = prevLast)
    (hlast01 : prevLast ≤ 1) (hn : n + 1 < M) :
    (arun idx s early3).regs rViol =
      bump (same && prevLast == 1) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hl10 : s.regs 10 = prevLast := by simpa [rPrevLast] using hlast
  have hn0 : n < M := by omega
  cases same <;> by_cases hp0 : prevLast = 0 <;> by_cases hp1 : prevLast = 1
  <;> dsimp [early3, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol, rPrevLast]
  <;> rw [hv0, hsame, hl10]
  <;> simp [hp0, hp1, bump, Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn]
  <;> omega

theorem early4_result
    (idx n prevBlk blk : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hprev : s.regs rPrevBlk = prevBlk) (hblk : s.regs 22 = blk)
    (hprevWord : prevBlk + 1 < M) (hn : n + 1 < M) :
    (arun idx s early4).regs rViol =
      bump (blk != (if same then prevBlk + 1 else 0)) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hp2 : s.regs 2 = prevBlk := by simpa [rPrevBlk] using hprev
  have hn0 : n < M := by omega
  cases same <;> by_cases hzero : blk = 0
  <;> by_cases hnext : blk = prevBlk + 1
  <;> dsimp [early4, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol, rPrevBlk]
  <;> rw [hv0, hsame, hp2, hblk]
  <;> simp [hzero, hnext, bump, Nat.mod_eq_of_lt hprevWord,
    Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn]

theorem early5_result
    (idx n prevUpper lower : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hprev : s.regs rPrevUpper = prevUpper) (hlower : s.regs 23 = lower)
    (hprevWord : prevUpper < M) (hn : n + 1 < M) :
    (arun idx s early5).regs rViol =
      bump (lower != (if same then prevUpper else 0)) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hp3 : s.regs 3 = prevUpper := by simpa [rPrevUpper] using hprev
  have hn0 : n < M := by omega
  cases same
  all_goals simp at hsame
  all_goals by_cases hzero : lower = 0
  all_goals by_cases hprevEq : lower = prevUpper
  all_goals by_cases hpzero : prevUpper = 0
  all_goals
    dsimp [early5, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, rPrevUpper]
    rw [hv0, hsame, hp3, hlower]
    simp [hzero, hprevEq, hpzero, zero_eq_iff_eq_zero, bump,
      Nat.mod_eq_of_lt hprevWord,
      Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn]

theorem early6_result
    (idx n lower slots upper : Nat) (s : AState)
    (hv : s.regs rViol = n) (hlower : s.regs 23 = lower)
    (hslots : s.regs 24 = slots) (hupper : s.regs 25 = upper)
    (hslotWord : lower + slots < M) (hn : n + 1 < M) :
    (arun idx s early6).regs rViol = bump (upper != lower + slots) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hn0 : n < M := by omega
  by_cases hflag : upper = lower + slots
  <;> dsimp [early6, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol]
  <;> rw [hv0, hlower, hslots, hupper]
  <;> simp [hflag, bump, Nat.mod_eq_of_lt hslotWord,
    Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn]

theorem early7_result
    (idx n isLast : Nat) (s : AState)
    (hv : s.regs rViol = n) (hlast : s.regs 28 = isLast)
    (hn : n + 1 < M) :
    (arun idx s early7).regs rViol = bump (isLast > 1) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hn0 : n < M := by omega
  by_cases hflag : isLast > 1
  <;> dsimp [early7, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rViol]
  <;> rw [hv0, hlast]
  <;> simp [hflag, bump, Nat.mod_eq_of_lt one_lt_M,
    Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn]

theorem early8_result
    (idx n isLast stat : Nat) (s : AState)
    (hv : s.regs rViol = n) (hlast : s.regs 28 = isLast)
    (hstat : s.regs 27 = stat) (hn : n + 1 < M) :
    let out := arun idx s early8
    out.regs rViol = bump (stat > maxStat) n ∧
      out.regs 48 = (if isLast = 1 then 1 else 0) := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hn0 : n < M := by omega
  by_cases hlast1 : isLast = 1 <;> by_cases hflag : 4 < stat
  all_goals
    dsimp [early8, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, maxStat]
    rw [hv0, hlast, hstat]
    simp [hlast1, hflag, maxStat, bump, Nat.mod_eq_of_lt one_lt_M,
      Nat.mod_eq_of_lt four_lt_M, Nat.mod_eq_of_lt hn0,
      Nat.mod_eq_of_lt hn]

end LeanCompCert.Ports.DirichletLadderExternalSafety
