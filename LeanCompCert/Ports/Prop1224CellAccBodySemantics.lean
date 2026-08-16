import LeanCompCert.Ports.Prop1224CellAccSemantics
import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Source semantics of the Proposition 12.2.4 accumulation phase

This module identifies the literal loads and arithmetic surrounding the
already-refined coprimality chain.  Its hypotheses are the source invariant
that the marking phase must establish for one cell: the three planes contain
the radical of the small-prime part, its totient contribution, and the
squarefull flag.  No production loop is evaluated in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

set_option maxRecDepth 1000000
set_option profiler true
set_option profiler.threshold 1000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.Prop1224Margin (C cdiv gqTerm)
open LeanCompCert.Ports.ArraySegMobiusSignal (avoidsStore arun_arr_frame)

/-- Position arithmetic at the start of one accumulation cell. -/
def accPositionPrefix (c : CellCfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  [ .scalar (.binop 84 .sub (.reg rR) (.lit T))
  , .scalar (.binop 86 .mul (.reg 12) (.reg 84))
  , .scalar (.binop 85 .add (.reg 86) (.reg rW))
  , .scalar (.binop 87 .add (.reg 86) (.lit L))
  , .scalar (.binop 88 .add (.reg 86) (.lit (2 * L)))
  , .scalar (.binop 89 .add (.reg 86) (.lit (3 * L))) ]

/-- The three source sieve-plane loads. -/
def accLoadPrefix : List AInstr :=
  [ .load 90 86
  , .load 91 87
  , .load 92 88 ]

/-- Compare the marked radical with the candidate and divide by it. -/
def accLargeComparePrefix : List AInstr :=
  [ .scalar (.binop 93 .ne (.reg 90) (.reg 85))
  , .scalar (.binop 94 .udiv (.reg 85) (.reg 90)) ]

/-- Convert the optional large prime to its `p-1` totient factor. -/
def accLargeFinishPrefix : List AInstr :=
  [ .scalar (.binop 95 .sub (.reg 94) (.lit 2))
  , .scalar (.binop 96 .mul (.reg 93) (.reg 95))
  , .scalar (.binop 97 .add (.reg 96) (.lit 1)) ]

/-- Recover the possible large-prime totient factor. -/
def accLargeFactorPrefix : List AInstr :=
  accLargeComparePrefix ++ accLargeFinishPrefix

/-- Finish `φ(r)`, the squarefree bit, and the coprimality seed. -/
def accFinishClassifyPrefix : List AInstr :=
  [ .scalar (.binop 98 .mul (.reg 91) (.reg 97))
  , .scalar (.binop 99 .eq (.reg 92) (.lit 0))
  , .scalar (.mov 81 (.lit 1)) ]

/-- Recover `φ(r)` and the squarefree bit from the source sieve planes. -/
def accClassifyPrefix : List AInstr :=
  accLargeFactorPrefix ++ accFinishClassifyPrefix

/-- The fixed prefix of `CellCfg.accBody`, before the row-specific literal
coprimality chain. -/
def accPrefix (c : CellCfg) : List AInstr :=
  accPositionPrefix c ++ accLoadPrefix ++ accClassifyPrefix

/-- Staged execution identity for the accumulation prefix.  Keeping this as
an opaque theorem prevents downstream source contracts from re-normalizing
the complete literal instruction list. -/
theorem accPrefix_run_eq (c : CellCfg) (k : Nat) (s : AState) :
    arun k s (accPrefix c) =
      arun k (arun k (arun k s (accPositionPrefix c)) accLoadPrefix)
        accClassifyPrefix := by
  rw [accPrefix, arun_append, arun_append]

/-- The fixed suffix of `CellCfg.accBody`, after the row-specific literal
coprimality chain. -/
def accGateSuffix : List AInstr :=
  [ .scalar (.binop 100 .mul (.reg 99) (.reg 81))
  ]

def accCeilSuffix : List AInstr :=
  [ .scalar (.binop 101 .add (.lit (2 ^ C)) (.reg 98))
  , .scalar (.binop 102 .sub (.reg 101) (.lit 1))
  , .scalar (.binop 103 .udiv (.reg 102) (.reg 98)) ]

def accAddSuffix : List AInstr :=
  [ .scalar (.binop 104 .mul (.reg 103) (.reg 100))
  , .scalar (.binop 105 .mul (.reg 104) (.reg 12))
  , .scalar (.binop rG .add (.reg rG) (.reg 105)) ]

def accComputeSuffix : List AInstr :=
  accGateSuffix ++ accCeilSuffix ++ accAddSuffix

def accResetAddressSuffix (c : CellCfg) : List AInstr :=
  let L := c.segLen
  let SNK := c.sink
  [ .scalar (.binop 106 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 107 .mul (.reg 106) (.lit SNK))
  , .scalar (.binop 108 .add (.reg 86) (.reg 107))
  , .scalar (.binop 109 .add (.reg 108) (.lit L))
  , .scalar (.binop 110 .add (.reg 108) (.lit (2 * L)))
  , .scalar (.binop 111 .add (.reg 108) (.lit (3 * L))) ]

def accResetStoreSuffix : List AInstr :=
  [ .store 111 rG
  , .store 108 rOne
  , .store 109 rOne
  , .store 110 rZero ]

def accResetSuffix (c : CellCfg) : List AInstr :=
  accResetAddressSuffix c ++ accResetStoreSuffix

def accSuffix (c : CellCfg) : List AInstr :=
  accComputeSuffix ++ accResetSuffix c

theorem accBody_eq (c : CellCfg) :
    c.accBody = accPrefix c ++ coprimeBody c.qPrimes ++ accSuffix c := by
  rfl

theorem accPositionPrefix_run (c : CellCfg) (k i w : Nat) (s : AState)
    (hR : s.regs rR = c.markSteps + i) (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w) (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M) (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M) :
    let out := arun k s (accPositionPrefix c)
    out.regs 86 = i ∧ out.regs 85 = w + i ∧
      out.regs 87 = i + c.segLen ∧
      out.regs 88 = i + 2 * c.segLen := by
  have hiM : i < M := by omega
  have hiL : i + c.segLen < M := by omega
  have hi2L : i + 2 * c.segLen < M := by omega
  have hR5 : s.regs 5 = c.markSteps + i := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hT
  have hiMod : i % M = i := Nat.mod_eq_of_lt hiM
  have hSub : (c.markSteps + i + (M - c.markSteps)) % M = i := by
    simp [show c.markSteps + i + (M - c.markSteps) = M + i by omega, hiMod]
  have hiwMod : (i + w) % M = w + i := by
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt hr
  simp [accPositionPrefix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, rR, rW, hR5, hW6, hAcc, hTmod, hSub,
    hiMod, hiwMod, Nat.mod_eq_of_lt hiL, Nat.mod_eq_of_lt hi2L]

theorem accLoadPrefix_run (k i radical phiSmall sqf : Nat) (s : AState)
    (hI : s.regs 86 = i)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (s.regs 87) = phiSmall)
    (hSqf : s.arr (s.regs 88) = sqf) :
    let out := arun k s accLoadPrefix
    out.regs 90 = radical ∧ out.regs 91 = phiSmall ∧ out.regs 92 = sqf := by
  simp [accLoadPrefix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, hI, hProd, hPhi, hSqf]

#eval IO.println "checkpoint: load"

theorem accLargeComparePrefix_run (k r radical : Nat) (s : AState)
    (hR : s.regs 85 = r) (hRad : s.regs 90 = radical)
    (hrM : r < M) (hRadPos : 0 < radical) :
    let out := arun k s accLargeComparePrefix
    out.regs 93 = (if radical = r then 0 else 1) ∧
      out.regs 94 = r / radical := by
  have hqM : r / radical < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrM
  by_cases heq : radical = r
  · have hrPos : 0 < r := by simpa [← heq] using hRadPos
    have hqq : r / r = 1 := Nat.div_self hrPos
    have hOneMod : 1 % M = 1 := by decide
    simp [accLargeComparePrefix, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, hR, hRad, heq, Nat.ne_of_gt hrPos, hqq,
      hOneMod]
  · simp [accLargeComparePrefix, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, hR, hRad, heq, Nat.ne_of_gt hRadPos,
      Nat.mod_eq_of_lt hqM]

#eval IO.println "checkpoint: compare"

theorem accLargeFinishPrefix_run_zero (k q : Nat) (s : AState)
    (hFlag : s.regs 93 = 0) :
    (arun k s accLargeFinishPrefix).regs 97 = 1 := by
  have hOneMod : 1 % M = 1 := by decide
  let s1 := astep k s (.scalar (.binop 95 .sub (.reg 94) (.lit 2)))
  let s2 := astep k s1 (.scalar (.binop 96 .mul (.reg 93) (.reg 95)))
  let s3 := astep k s2 (.scalar (.binop 97 .add (.reg 96) (.lit 1)))
  have hFlag1 : s1.regs 93 = 0 := by
    simpa [s1, astep, AState.writeReg, sdest, sval] using hFlag
  have hZero : s2.regs 96 = 0 := by
    simp [s2, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hFlag1]
  have hOne : s3.regs 97 = 1 := by
    simp [s3, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hZero, hOneMod]
  exact hOne

#eval IO.println "checkpoint: finish-zero"

theorem accLargeFinishPrefix_run_one (k q : Nat) (s : AState)
    (hFlag : s.regs 93 = 1) (hQ : s.regs 94 = q)
    (hqTwo : 2 ≤ q) (hqM : q < M) :
    (arun k s accLargeFinishPrefix).regs 97 = q - 1 := by
  have hTwoMod : 2 % M = 2 := by decide
  have hqm2M : q - 2 < M := by omega
  have hfactorM : q - 1 < M := by omega
  have hFactor : (q + (M - 2) + 1) % M = q - 1 := by
    rw [show q + (M - 2) + 1 = M + (q - 1) by omega]
    simp [Nat.mod_eq_of_lt hfactorM]
  have hSubMod : (q + (M - 2)) % M = q - 2 := by
    rw [show q + (M - 2) = M + (q - 2) by omega]
    simp [Nat.mod_eq_of_lt hqm2M]
  have hAddMod : (q - 2 + 1) % M = q - 1 := by
    rw [show q - 2 + 1 = q - 1 by omega]
    exact Nat.mod_eq_of_lt hfactorM
  let s1 := astep k s (.scalar (.binop 95 .sub (.reg 94) (.lit 2)))
  let s2 := astep k s1 (.scalar (.binop 96 .mul (.reg 93) (.reg 95)))
  let s3 := astep k s2 (.scalar (.binop 97 .add (.reg 96) (.lit 1)))
  have hSub : s1.regs 95 = q - 2 := by
    simp [s1, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hQ, hTwoMod, hSubMod]
  have hFlag1 : s1.regs 93 = 1 := by
    simpa [s1, astep, AState.writeReg, sdest, sval] using hFlag
  have hMul : s2.regs 96 = q - 2 := by
    simp [s2, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hFlag1, hSub, Nat.mod_eq_of_lt hqm2M]
  have hOut : s3.regs 97 = q - 1 := by
    simp [s3, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hMul, hAddMod]
  exact hOut

#eval IO.println "checkpoint: finish-one"

theorem accLargeFactorPrefix_run (k r radical : Nat) (s : AState)
    (hR : s.regs 85 = r) (hRad : s.regs 90 = radical)
    (hrM : r < M) (hRadPos : 0 < radical) (hRadDvd : radical ∣ r)
    (hRadLe : radical ≤ r) :
    let out := arun k s accLargeFactorPrefix
    out.regs 97 = (if radical = r then 1 else r / radical - 1) := by
  let compared := arun k s accLargeComparePrefix
  have hc := accLargeComparePrefix_run k r radical s hR hRad hrM hRadPos
  dsimp only at hc
  by_cases heq : radical = r
  · rw [accLargeFactorPrefix, arun_append]
    simpa [heq] using accLargeFinishPrefix_run_zero k (r / radical) compared
      (by simpa [heq] using hc.1)
  · have hrPos : 0 < r := Nat.lt_of_lt_of_le hRadPos hRadLe
    have hqM : r / radical < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrM
    have hqne : r / radical ≠ 1 := by
      intro hq
      have heq' := (Nat.div_eq_iff_eq_mul_left hRadPos hRadDvd).mp hq
      exact heq (by simpa using heq'.symm)
    have hqPos : 0 < r / radical := Nat.div_pos
      (Nat.le_of_dvd hrPos hRadDvd) hRadPos
    have hqTwo : 2 ≤ r / radical := by omega
    rw [accLargeFactorPrefix, arun_append]
    simpa [heq] using accLargeFinishPrefix_run_one k (r / radical) compared
      (by simpa [heq] using hc.1) hc.2 hqTwo hqM

#eval IO.println "checkpoint: factor"

theorem accFinishClassifyPrefix_run (k phiSmall sqf factor phi : Nat)
    (s : AState) (hPhi : s.regs 91 = phiSmall)
    (hSqf : s.regs 92 = sqf) (hFactor : s.regs 97 = factor)
    (hPhiEq : phi = phiSmall * factor) (hPhiM : phi < M) :
    let out := arun k s accFinishClassifyPrefix
    out.regs 98 = phi ∧ out.regs 99 = (if sqf = 0 then 1 else 0) ∧
      out.regs 81 = 1 := by
  subst phi
  have hOneMod : 1 % M = 1 := by decide
  simp [accFinishClassifyPrefix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hPhi, hSqf, hFactor,
    Nat.mod_eq_of_lt hPhiM, hOneMod]

#eval IO.println "checkpoint: finish-classify"

set_option maxRecDepth 100000 in
theorem accClassifyPrefix_run (k r radical phiSmall sqf phi : Nat)
    (s : AState) (hR : s.regs 85 = r) (hRad : s.regs 90 = radical)
    (hPhi : s.regs 91 = phiSmall) (hSqf : s.regs 92 = sqf)
    (hrM : r < M) (hRadPos : 0 < radical) (hRadM : radical < M)
    (hRadDvd : radical ∣ r) (hRadLe : radical ≤ r)
    (hPhiSmallM : phiSmall < M) (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = r then 1 else r / radical - 1)) :
    let out := arun k s accClassifyPrefix
    out.regs 98 = phi ∧ out.regs 99 = (if sqf = 0 then 1 else 0) ∧
      out.regs 81 = 1 := by
  let factored := arun k s accLargeFactorPrefix
  have hf := accLargeFactorPrefix_run k r radical s hR hRad hrM hRadPos
    hRadDvd hRadLe
  dsimp only at hf
  have hPhi' : factored.regs 91 = phiSmall :=
    (arun_frame k 91 accLargeFactorPrefix (by rfl) s).trans hPhi
  have hSqf' : factored.regs 92 = sqf :=
    (arun_frame k 92 accLargeFactorPrefix (by rfl) s).trans hSqf
  have hfinish := accFinishClassifyPrefix_run k phiSmall sqf
    (if radical = r then 1 else r / radical - 1) phi factored hPhi' hSqf'
      hf hPhiEq hPhiM
  dsimp only at hfinish
  simpa only [accClassifyPrefix, arun_append] using hfinish

#eval IO.println "checkpoint: classify"

/-- Small opaque frame lemmas keep the kernel from expanding the literal
instruction lists again when the three verified prefix stages are composed. -/
theorem accPositionPrefix_arr_frame (c : CellCfg) (k : Nat) (s : AState) :
    (arun k s (accPositionPrefix c)).arr = s.arr :=
  arun_arr_frame k (accPositionPrefix c) s (by rfl)

theorem accLoadPrefix_arr_frame (k : Nat) (s : AState) :
    (arun k s accLoadPrefix).arr = s.arr :=
  arun_arr_frame k accLoadPrefix s (by rfl)

theorem accClassifyPrefix_arr_frame (k : Nat) (s : AState) :
    (arun k s accClassifyPrefix).arr = s.arr :=
  arun_arr_frame k accClassifyPrefix s (by rfl)

theorem accLoadPrefix_reg85_frame (k : Nat) (s : AState) :
    (arun k s accLoadPrefix).regs 85 = s.regs 85 :=
  arun_frame k 85 accLoadPrefix (by rfl) s

theorem accLoadPrefix_reg86_frame (k : Nat) (s : AState) :
    (arun k s accLoadPrefix).regs 86 = s.regs 86 :=
  arun_frame k 86 accLoadPrefix (by rfl) s

theorem accClassifyPrefix_reg86_frame (k : Nat) (s : AState) :
    (arun k s accClassifyPrefix).regs 86 = s.regs 86 :=
  arun_frame k 86 accClassifyPrefix (by rfl) s

theorem accClassifyPrefix_reg85_frame (k : Nat) (s : AState) :
    (arun k s accClassifyPrefix).regs 85 = s.regs 85 :=
  arun_frame k 85 accClassifyPrefix (by rfl) s

theorem accPrefix_staged_position
    (c : CellCfg) (k i w : Nat) (s positioned loaded out : AState)
    (hPositioned : positioned = arun k s (accPositionPrefix c))
    (hLoaded : loaded = arun k positioned accLoadPrefix)
    (hOut : out = arun k loaded accClassifyPrefix)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1) (hW : s.regs rW = w)
    (hT : c.markSteps < M) (hTi : c.markSteps + i < M)
    (hr : w + i < M) (hL : i + 3 * c.segLen < M) :
    out.regs 86 = i ∧ out.regs 85 = w + i := by
  have hp : positioned.regs 86 = i ∧ positioned.regs 85 = w + i ∧
      positioned.regs 87 = i + c.segLen ∧
      positioned.regs 88 = i + 2 * c.segLen := by
    rw [hPositioned]
    exact accPositionPrefix_run c k i w s hR hAcc hW hT hTi hr hL
  have h85 : loaded.regs 85 = w + i :=
    hLoaded.symm ▸ (accLoadPrefix_reg85_frame k positioned).trans hp.2.1
  refine ⟨?_, hOut.symm ▸
    (accClassifyPrefix_reg85_frame k loaded).trans h85⟩
  exact hOut.symm ▸ (accClassifyPrefix_reg86_frame k loaded).trans
    (hLoaded.symm ▸ (accLoadPrefix_reg86_frame k positioned).trans hp.1)

theorem accPrefix_staged_classify
    (c : CellCfg) (k i w radical phiSmall sqf phi : Nat)
    (s positioned loaded out : AState)
    (hPositioned : positioned = arun k s (accPositionPrefix c))
    (hLoaded : loaded = arun k positioned accLoadPrefix)
    (hOut : out = arun k loaded accClassifyPrefix)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1) (hW : s.regs rW = w)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hr : w + i < M) (hL : i + 3 * c.segLen < M)
    (hT : c.markSteps < M) (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical) (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i) (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M) (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1)) :
    out.regs 98 = phi ∧
      out.regs 99 = (if sqf = 0 then 1 else 0) ∧ out.regs 81 = 1 := by
  have hp : positioned.regs 86 = i ∧ positioned.regs 85 = w + i ∧
      positioned.regs 87 = i + c.segLen ∧
      positioned.regs 88 = i + 2 * c.segLen := by
    rw [hPositioned]
    exact accPositionPrefix_run c k i w s hR hAcc hW hT hTi hr hL
  have hpArr : positioned.arr = s.arr := by
    rw [hPositioned]
    exact accPositionPrefix_arr_frame c k s
  have hProd' : positioned.arr i = radical := by rw [hpArr]; exact hProd
  have hPhi' : positioned.arr (positioned.regs 87) = phiSmall := by
    rw [hp.2.2.1, hpArr]
    exact hPhi
  have hSqf' : positioned.arr (positioned.regs 88) = sqf := by
    rw [hp.2.2.2, hpArr]
    exact hSqf
  have hload : loaded.regs 90 = radical ∧ loaded.regs 91 = phiSmall ∧
      loaded.regs 92 = sqf := by
    rw [hLoaded]
    exact accLoadPrefix_run k i radical phiSmall sqf positioned hp.1
      hProd' hPhi' hSqf'
  have h85 : loaded.regs 85 = w + i :=
    hLoaded.symm ▸ (accLoadPrefix_reg85_frame k positioned).trans hp.2.1
  rw [hOut]
  exact accClassifyPrefix_run k (w + i) radical phiSmall sqf phi loaded h85
    hload.1 hload.2.1 hload.2.2 hr hRadPos hRadM hRadDvd hRadLe
      hPhiSmallM hPhiM hPhiEq

theorem accPrefix_staged_arr (c : CellCfg) (k : Nat)
    (s positioned loaded out : AState)
    (hPositioned : positioned = arun k s (accPositionPrefix c))
    (hLoaded : loaded = arun k positioned accLoadPrefix)
    (hOut : out = arun k loaded accClassifyPrefix) : out.arr = s.arr := by
  calc
    out.arr = loaded.arr := hOut.symm ▸ accClassifyPrefix_arr_frame k loaded
    _ = positioned.arr := hLoaded.symm ▸ accLoadPrefix_arr_frame k positioned
    _ = s.arr := hPositioned.symm ▸ accPositionPrefix_arr_frame c k s

/-- Exact source meaning of the staged accumulation prefix.  This statement
is deliberately separated from `accPrefix_run`: the direct instruction-list
transport otherwise makes the kernel normalize the complete trace while it
checks the (already elaborated) semantic proof term. -/
theorem accPrefix_run_staged
    (c : CellCfg) (k i w radical phiSmall sqf phi : Nat)
    (s : AState)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hi : i < c.segLen)
    (hr : w + i < M)
    (hL : i + 3 * c.segLen < M)
    (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical)
    (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i)
    (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M)
    (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1)) :
    let out :=
      arun k (arun k (arun k s (accPositionPrefix c)) accLoadPrefix)
        accClassifyPrefix
    out.regs 86 = i ∧
      out.regs 85 = w + i ∧
      out.regs 98 = phi ∧
      out.regs 99 = (if sqf = 0 then 1 else 0) ∧
      out.regs 81 = 1 ∧ out.arr = s.arr := by
  let positioned := arun k s (accPositionPrefix c)
  let loaded := arun k positioned accLoadPrefix
  let out := arun k loaded accClassifyPrefix
  have hp := accPrefix_staged_position c k i w s positioned loaded out rfl rfl
    rfl hR hAcc hW hT hTi hr hL
  have hc := accPrefix_staged_classify c k i w radical phiSmall sqf phi s
    positioned loaded out rfl rfl rfl hR hAcc hW hProd hPhi hSqf hr hL hT hTi
      hRadPos hRadM hRadDvd hRadLe hPhiSmallM hPhiM hPhiEq
  have ha := accPrefix_staged_arr c k s positioned loaded out rfl rfl rfl
  dsimp only at hp hc ⊢
  exact ⟨hp.1, hp.2, hc.1, hc.2.1, hc.2.2, ha⟩

/-- Exact source meaning of the fixed accumulation prefix.  In the
squarefree case, `large = r / radical` is either one or the single remaining
prime, and `phi = phiSmall * (large - 1)` in the latter case. -/
theorem accPrefix_run (c : CellCfg) (k i w radical phiSmall sqf phi : Nat)
    (s : AState)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hi : i < c.segLen)
    (hr : w + i < M)
    (hL : i + 3 * c.segLen < M)
    (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical)
    (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i)
    (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M)
    (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1)) :
    let out := arun k s (accPrefix c)
    out.regs 86 = i ∧
      out.regs 85 = w + i ∧
      out.regs 98 = phi ∧
      out.regs 99 = (if sqf = 0 then 1 else 0) ∧
      out.regs 81 = 1 ∧ out.arr = s.arr := by
  rw [accPrefix_run_eq]
  exact accPrefix_run_staged c k i w radical phiSmall sqf phi s hR hAcc hW
    hProd hPhi hSqf hi hr hL hT hTi hRadPos hRadM hRadDvd hRadLe hPhiSmallM
      hPhiM hPhiEq

#eval IO.println "checkpoint: prefix"

theorem coprimeBody_reg_frame (ps : List Nat) (reg k : Nat) (s : AState)
    (h81 : reg ≠ 81) (h82 : reg ≠ 82) (h83 : reg ≠ 83) :
    (arun k s (coprimeBody ps)).regs reg = s.regs reg := by
  apply arun_frame
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [coprimeBody, instrWrites, sdest, h81.symm, h82.symm, h83.symm]
        using ih

theorem accGateSuffix_run (k sqbit cop : Nat) (s : AState)
    (hSq : s.regs 99 = sqbit) (hCop : s.regs 81 = cop)
    (hbit : sqbit ≤ 1) (hcopbit : cop ≤ 1) :
    let out := arun k s accGateSuffix
    out.regs 100 = sqbit * cop ∧ out.arr = s.arr := by
  have hOneMod : 1 % M = 1 := by decide
  have hsqcases : sqbit = 0 ∨ sqbit = 1 := by omega
  have hcopcases : cop = 0 ∨ cop = 1 := by omega
  rcases hsqcases with rfl | rfl <;> rcases hcopcases with rfl | rfl <;>
    simp [accGateSuffix, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, hSq, hCop, hOneMod]

theorem accCeilSuffix_run (k phi : Nat) (s : AState)
    (hPhi : s.regs 98 = phi) (hPhiPos : 0 < phi)
    (hSumM : 2 ^ C + phi < M) (hTermM : gqTerm phi < M) :
    let out := arun k s accCeilSuffix
    out.regs 103 = gqTerm phi ∧ out.arr = s.arr := by
  have hMpos : 0 < M := by decide
  have hApos : 0 < 2 ^ C + phi := Nat.add_pos_left (Nat.two_pow_pos C) phi
  have hNumeratorM : 2 ^ C + phi - 1 < M := by omega
  have hOneMod : 1 % M = 1 := by decide
  have hSubOne : (2 ^ C + phi + (M - 1)) % M = 2 ^ C + phi - 1 := by
    rw [show 2 ^ C + phi + (M - 1) = M + (2 ^ C + phi - 1) by omega]
    simp [Nat.mod_eq_of_lt hNumeratorM]
  have hCeilEq : (2 ^ C + phi - 1) / phi = gqTerm phi := by
    simp only [gqTerm, cdiv]
  simp [accCeilSuffix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hPhi, Nat.ne_of_gt hPhiPos, hOneMod,
    hSubOne, hCeilEq, Nat.mod_eq_of_lt hTermM]

theorem accAddSuffix_run (k term take g : Nat) (s : AState)
    (hTerm : s.regs 103 = term) (hTake : s.regs 100 = take)
    (hAcc : s.regs 12 = 1) (hG : s.regs rG = g)
    (hProductM : term * take < M) (hNewM : g + term * take < M) :
    let out := arun k s accAddSuffix
    out.regs rG = g + term * take ∧ out.arr = s.arr := by
  have hG180 : s.regs 180 = g := by simpa [rG] using hG
  simp [accAddSuffix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, rG, hTerm, hTake, hAcc, hG180,
    Nat.mod_eq_of_lt hProductM, Nat.mod_eq_of_lt hNewM]

theorem accComputeSuffix_run (k phi sqbit cop g : Nat) (s : AState)
    (hPhi : s.regs 98 = phi) (hSq : s.regs 99 = sqbit)
    (hCop : s.regs 81 = cop) (hAcc : s.regs 12 = 1)
    (hG : s.regs rG = g) (hPhiPos : 0 < phi) (hPhiM : phi < M)
    (hSumM : 2 ^ C + phi < M) (hTermM : gqTerm phi < M)
    (hbit : sqbit ≤ 1) (hcopbit : cop ≤ 1)
    (hGM : g + gqTerm phi < M) :
    let inc := gqTerm phi * (sqbit * cop)
    let out := arun k s accComputeSuffix
    out.regs rG = g + inc ∧ out.arr = s.arr := by
  have hsqcases : sqbit = 0 ∨ sqbit = 1 := by omega
  have hcopcases : cop = 0 ∨ cop = 1 := by omega
  have hIncLe : gqTerm phi * (sqbit * cop) ≤ gqTerm phi := by
    rcases hsqcases with rfl | rfl <;> rcases hcopcases with rfl | rfl <;> simp
  have hNewM : g + gqTerm phi * (sqbit * cop) < M :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hIncLe g) hGM
  have hIncM : gqTerm phi * (sqbit * cop) < M :=
    Nat.lt_of_le_of_lt hIncLe hTermM
  let gated := arun k s accGateSuffix
  have hg := accGateSuffix_run k sqbit cop s hSq hCop hbit hcopbit
  dsimp only at hg
  let ceiled := arun k gated accCeilSuffix
  have hPhi' : gated.regs 98 = phi :=
    (arun_frame k 98 accGateSuffix (by rfl) s).trans hPhi
  have hc := accCeilSuffix_run k phi gated hPhi' hPhiPos hSumM hTermM
  dsimp only at hc
  have hTake' : ceiled.regs 100 = sqbit * cop :=
    (arun_frame k 100 accCeilSuffix (by rfl) gated).trans hg.1
  have hAcc' : ceiled.regs 12 = 1 :=
    (arun_frame k 12 accCeilSuffix (by rfl) gated).trans
      ((arun_frame k 12 accGateSuffix (by rfl) s).trans hAcc)
  have hG' : ceiled.regs rG = g :=
    (arun_frame k rG accCeilSuffix (by rfl) gated).trans
      ((arun_frame k rG accGateSuffix (by rfl) s).trans hG)
  have ha := accAddSuffix_run k (gqTerm phi) (sqbit * cop) g ceiled hc.1
    hTake' hAcc' hG' hIncM hNewM
  dsimp only at ha
  rw [accComputeSuffix, arun_append, arun_append]
  exact ha

theorem accResetAddressSuffix_run (c : CellCfg) (k i : Nat) (s : AState)
    (hI : s.regs 86 = i) (hAcc : s.regs 12 = 1)
    (hIndexM : i + 3 * c.segLen < M) :
    let out := arun k s (accResetAddressSuffix c)
    out.regs 108 = i ∧ out.regs 109 = i + c.segLen ∧
      out.regs 110 = i + 2 * c.segLen ∧
      out.regs 111 = i + 3 * c.segLen := by
  have hiM : i < M := by omega
  have hiL : i + c.segLen < M := by omega
  have hi2L : i + 2 * c.segLen < M := by omega
  have hUnit : 1 + (M - 1) = M := by decide
  have hiMod : i % M = i := Nat.mod_eq_of_lt hiM
  have hSink : (i + (1 + (M - 1)) * c.sink) % M = i := by
    rw [hUnit, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hiM
  simp [accResetAddressSuffix, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hI, hAcc, hUnit, hSink,
    hiMod, Nat.mod_eq_of_lt hiL, Nat.mod_eq_of_lt hi2L,
    Nat.mod_eq_of_lt hIndexM]

theorem accResetStoreSuffix_run (c : CellCfg) (k i value : Nat) (s : AState)
    (h108 : s.regs 108 = i) (h109 : s.regs 109 = i + c.segLen)
    (h110 : s.regs 110 = i + 2 * c.segLen)
    (h111 : s.regs 111 = i + 3 * c.segLen)
    (hG : s.regs rG = value) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (hi : i < c.segLen)
    (hIndexM : i + 3 * c.segLen < M) :
    let out := arun k s accResetStoreSuffix
    out.regs rG = value ∧ out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = value := by
  have hG180 : s.regs 180 = value := by simpa [rG] using hG
  have hOne7 : s.regs 7 = 1 := by simpa [rOne] using hOne
  have hZero8 : s.regs 8 = 0 := by simpa [rZero] using hZero
  have hiM : i < M := by omega
  have hiL : i + c.segLen < M := by omega
  have hi2L : i + 2 * c.segLen < M := by omega
  let s1 := astep k s (.store 111 rG)
  let s2 := astep k s1 (.store 108 rOne)
  let s3 := astep k s2 (.store 109 rOne)
  let s4 := astep k s3 (.store 110 rZero)
  have hs1Regs : s1.regs = s.regs := rfl
  have hs2Regs : s2.regs = s.regs := rfl
  have hs3Regs : s3.regs = s.regs := rfl
  have hs4Regs : s4.regs = s.regs := rfl
  have ha3 : s1.arr (i + 3 * c.segLen) = value := by
    simp [s1, astep, AState.writeArr, rG, h111, hG180,
      Nat.mod_eq_of_lt hIndexM]
  have h1081 : s1.regs 108 = i := by rw [hs1Regs]; exact h108
  have hOne1 : s1.regs rOne = 1 := by rw [hs1Regs]; exact hOne
  have hOne1' : s1.regs 7 = 1 := by rw [hs1Regs]; exact hOne7
  have ha0 : s2.arr i = 1 := by
    simp [s2, astep, AState.writeArr, h1081, hOne1', rOne,
      Nat.mod_eq_of_lt hiM]
  have ha3' : s2.arr (i + 3 * c.segLen) = value := by
    simp [s2, astep, AState.writeArr, h1081, hOne1', rOne,
      Nat.mod_eq_of_lt hiM, ha3]
    omega
  have h1092 : s2.regs 109 = i + c.segLen := by rw [hs2Regs]; exact h109
  have hOne2 : s2.regs rOne = 1 := by rw [hs2Regs]; exact hOne
  have hOne2' : s2.regs 7 = 1 := by rw [hs2Regs]; exact hOne7
  have ha1 : s3.arr (i + c.segLen) = 1 := by
    simp [s3, astep, AState.writeArr, h1092, hOne2', rOne,
      Nat.mod_eq_of_lt hiL]
  have ha0' : s3.arr i = 1 := by
    simp [s3, astep, AState.writeArr, h1092, hOne2', rOne,
      Nat.mod_eq_of_lt hiL, ha0]
  have ha3'' : s3.arr (i + 3 * c.segLen) = value := by
    simp [s3, astep, AState.writeArr, h1092, hOne2', rOne,
      Nat.mod_eq_of_lt hiL, ha3']
    omega
  have h1103 : s3.regs 110 = i + 2 * c.segLen := by rw [hs3Regs]; exact h110
  have hZero3 : s3.regs rZero = 0 := by rw [hs3Regs]; exact hZero
  have hZero3' : s3.regs 8 = 0 := by rw [hs3Regs]; exact hZero8
  have ha2 : s4.arr (i + 2 * c.segLen) = 0 := by
    simp [s4, astep, AState.writeArr, h1103, hZero3', rZero,
      Nat.mod_eq_of_lt hi2L]
  have ha0'' : s4.arr i = 1 := by
    simp [s4, astep, AState.writeArr, h1103, hZero3', rZero,
      Nat.mod_eq_of_lt hi2L, ha0']
    omega
  have ha1' : s4.arr (i + c.segLen) = 1 := by
    simp [s4, astep, AState.writeArr, h1103, hZero3', rZero,
      Nat.mod_eq_of_lt hi2L, ha1]
    omega
  have ha3''' : s4.arr (i + 3 * c.segLen) = value := by
    simp [s4, astep, AState.writeArr, h1103, hZero3', rZero,
      Nat.mod_eq_of_lt hi2L, ha3'']
    omega
  have hG4 : s4.regs rG = value := by rw [hs4Regs]; exact hG
  exact ⟨hG4, ha0'', ha1', ha2, ha3'''⟩

theorem accResetSuffix_run (c : CellCfg) (k i value : Nat) (s : AState)
    (hI : s.regs 86 = i) (hAcc : s.regs 12 = 1)
    (hG : s.regs rG = value) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (hi : i < c.segLen)
    (hIndexM : i + 3 * c.segLen < M) (hValueM : value < M) :
    let out := arun k s (accResetSuffix c)
    out.regs rG = value ∧ out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = value := by
  let addressed := arun k s (accResetAddressSuffix c)
  have ha := accResetAddressSuffix_run c k i s hI hAcc hIndexM
  dsimp only at ha
  have hG' : addressed.regs rG = value :=
    (arun_frame k rG (accResetAddressSuffix c) (by rfl) s).trans hG
  have hOne' : addressed.regs rOne = 1 :=
    (arun_frame k rOne (accResetAddressSuffix c) (by rfl) s).trans hOne
  have hZero' : addressed.regs rZero = 0 :=
    (arun_frame k rZero (accResetAddressSuffix c) (by rfl) s).trans hZero
  have hs := accResetStoreSuffix_run c k i value addressed ha.1 ha.2.1
    ha.2.2.1 ha.2.2.2 hG' hOne' hZero' hi hIndexM
  dsimp only at hs
  rw [accResetSuffix, arun_append]
  exact hs

/-- Exact update performed by the fixed suffix.  It adds one upward-rounded
`G_q` term precisely when both the squarefree and coprimality bits are one,
publishes the new sum, and resets the three sieve planes. -/
theorem accSuffix_run (c : CellCfg) (k i phi sqbit cop g : Nat) (s : AState)
    (hI : s.regs 86 = i)
    (hPhi : s.regs 98 = phi)
    (hSq : s.regs 99 = sqbit)
    (hCop : s.regs 81 = cop)
    (hAcc : s.regs 12 = 1)
    (hG : s.regs rG = g)
    (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0)
    (hi : i < c.segLen)
    (hIndexM : i + 3 * c.segLen < M)
    (hPhiPos : 0 < phi)
    (hPhiM : phi < M)
    (hSumM : 2 ^ C + phi < M)
    (hTermM : gqTerm phi < M)
    (hbit : sqbit ≤ 1)
    (hcopbit : cop ≤ 1)
    (hGM : g + gqTerm phi < M) :
    let inc := gqTerm phi * (sqbit * cop)
    let out := arun k s (accSuffix c)
    out.regs rG = g + inc ∧
      out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = g + inc := by
  have hsqcases : sqbit = 0 ∨ sqbit = 1 := by omega
  have hcopcases : cop = 0 ∨ cop = 1 := by omega
  have hIncLe : gqTerm phi * (sqbit * cop) ≤ gqTerm phi := by
    rcases hsqcases with rfl | rfl <;> rcases hcopcases with rfl | rfl <;> simp
  have hNewM : g + gqTerm phi * (sqbit * cop) < M :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hIncLe g) hGM
  let computed := arun k s accComputeSuffix
  have hc := accComputeSuffix_run k phi sqbit cop g s hPhi hSq hCop hAcc hG
    hPhiPos hPhiM hSumM hTermM hbit hcopbit hGM
  dsimp only at hc
  have hI' : computed.regs 86 = i :=
    (arun_frame k 86 accComputeSuffix (by rfl) s).trans hI
  have hAcc' : computed.regs 12 = 1 :=
    (arun_frame k 12 accComputeSuffix (by rfl) s).trans hAcc
  have hOne' : computed.regs rOne = 1 :=
    (arun_frame k rOne accComputeSuffix (by rfl) s).trans hOne
  have hZero' : computed.regs rZero = 0 :=
    (arun_frame k rZero accComputeSuffix (by rfl) s).trans hZero
  have hr := accResetSuffix_run c k i
    (g + gqTerm phi * (sqbit * cop)) computed hI' hAcc' hc.1 hOne'
      hZero' hi hIndexM hNewM
  dsimp only at hr
  rw [accSuffix, arun_append]
  exact hr

/-- One literal accumulation phase computes the exact upward-rounded finite
`G_q` recurrence from a source-correct sieve cell.  The theorem is generic in
the row and cell; production-sized ranges are handled later by induction over
this step, not by reducing the loop. -/
theorem accBody_run (c : CellCfg) (k i w radical phiSmall sqf phi g : Nat)
    (s : AState)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hG : s.regs rG = g)
    (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0)
    (hi : i < c.segLen)
    (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M)
    (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical)
    (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i)
    (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M)
    (hPhiPos : 0 < phi)
    (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1))
    (hPrimes : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M)
    (hSumM : 2 ^ C + phi < M)
    (hTermM : gqTerm phi < M)
    (hGM : g + gqTerm phi < M) :
    let take := (if sqf = 0 then 1 else 0) *
      coprimeIndicator c.qPrimes (w + i)
    let inc := gqTerm phi * take
    let out := arun k s c.accBody
    out.regs rG = g + inc ∧
      out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = g + inc := by
  let pref := arun k s (accPrefix c)
  have hp := accPrefix_run c k i w radical phiSmall sqf phi s hR hAcc hW
    hProd hPhi hSqf hi hr hIndexM hT hTi hRadPos hRadM hRadDvd hRadLe
      hPhiSmallM hPhiM hPhiEq
  dsimp only at hp
  have hpAcc : pref.regs 12 = 1 :=
    (arun_frame k 12 (accPrefix c) (by rfl) s).trans hAcc
  have hpG : pref.regs rG = g :=
    (arun_frame k rG (accPrefix c) (by rfl) s).trans hG
  have hpOne : pref.regs rOne = 1 :=
    (arun_frame k rOne (accPrefix c) (by rfl) s).trans hOne
  have hpZero : pref.regs rZero = 0 :=
    (arun_frame k rZero (accPrefix c) (by rfl) s).trans hZero
  let copied := arun k pref (coprimeBody c.qPrimes)
  have hc := coprimeBody_run c.qPrimes k (w + i) pref hp.2.1 hp.2.2.2.2.1
    hPrimes
  dsimp only at hc
  have hcI : copied.regs 86 = i :=
    (coprimeBody_reg_frame c.qPrimes 86 k pref (by decide) (by decide)
      (by decide)).trans hp.1
  have hcPhi : copied.regs 98 = phi :=
    (coprimeBody_reg_frame c.qPrimes 98 k pref (by decide) (by decide)
      (by decide)).trans hp.2.2.1
  have hcSq : copied.regs 99 = (if sqf = 0 then 1 else 0) :=
    (coprimeBody_reg_frame c.qPrimes 99 k pref (by decide) (by decide)
      (by decide)).trans hp.2.2.2.1
  have hcAcc : copied.regs 12 = 1 :=
    (coprimeBody_reg_frame c.qPrimes 12 k pref (by decide) (by decide)
      (by decide)).trans hpAcc
  have hcG : copied.regs rG = g :=
    (coprimeBody_reg_frame c.qPrimes rG k pref (by decide) (by decide)
      (by decide)).trans hpG
  have hcOne : copied.regs rOne = 1 :=
    (coprimeBody_reg_frame c.qPrimes rOne k pref (by decide) (by decide)
      (by decide)).trans hpOne
  have hcZero : copied.regs rZero = 0 :=
    (coprimeBody_reg_frame c.qPrimes rZero k pref (by decide) (by decide)
      (by decide)).trans hpZero
  have hs := accSuffix_run c k i phi (if sqf = 0 then 1 else 0)
    (coprimeIndicator c.qPrimes (w + i)) g copied hcI hcPhi hcSq hc.1
    hcAcc hcG hcOne hcZero hi hIndexM hPhiPos hPhiM hSumM hTermM
    (by split <;> omega) (coprimeIndicator_le_one _ _) hGM
  dsimp only at hs
  rw [accBody_eq, arun_append, arun_append]
  exact hs

/-! ## Source-shaped exact step -/

/-- Natural recurrence accumulated by the machine before division by the
global fixed-point scale, parametrized by the source meanings of the two
sieve outputs.  The Mathlib-facing bridge later identifies `phi` with
`Nat.totient r` and `sqf = 0` with squarefreeness. -/
def cellMarkedStep (ps : List Nat) (r phi sqf : Nat) : Nat :=
  gqTerm phi * ((if sqf = 0 then 1 else 0) * coprimeIndicator ps r)

/-- Source meaning required of the three marked planes at one active cell.
The later marking proof has one stable target and the arithmetic body need
not know how those planes were produced. -/
structure AccCellInputCorrect (c : CellCfg) (s : AState) (w i : Nat) where
  radical : Nat
  phiSmall : Nat
  sqf : Nat
  phi : Nat
  prod_eq : s.arr i = radical
  phi_eq : s.arr (i + c.segLen) = phiSmall
  sqf_eq : s.arr (i + 2 * c.segLen) = sqf
  radical_pos : 0 < radical
  radical_lt : radical < M
  radical_dvd : radical ∣ w + i
  radical_le : radical ≤ w + i
  phiSmall_lt : phiSmall < M
  phi_pos : 0 < phi
  phi_lt : phi < M
  phi_eq_source : phi = phiSmall *
    (if radical = w + i then 1 else (w + i) / radical - 1)

/-- One active compiled accumulation block realizes the exact natural source
recurrence.  Production-scale iteration will use this theorem opaquely; it
does not reduce the instruction list or the finite source prefix. -/
theorem accBody_run_exact_step (c : CellCfg) (k i w g : Nat) (s : AState)
    (hInput : AccCellInputCorrect c s w i)
    (hR : s.regs rR = c.markSteps + i)
    (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w)
    (hG : s.regs rG = g)
    (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0)
    (hi : i < c.segLen)
    (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M)
    (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M)
    (hPrimes : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M)
    (hSumM : 2 ^ C + hInput.phi < M)
    (hTermM : gqTerm hInput.phi < M)
    (hGM : g + gqTerm hInput.phi < M) :
    let inc := cellMarkedStep c.qPrimes (w + i) hInput.phi hInput.sqf
    let out := arun k s c.accBody
    out.regs rG = g + inc ∧
      out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = g + inc := by
  have hrun := accBody_run c k i w hInput.radical hInput.phiSmall
    hInput.sqf hInput.phi g s hR hAcc hW hInput.prod_eq
      hInput.phi_eq hInput.sqf_eq hG hOne hZero hi hr hIndexM hT hTi
      hInput.radical_pos hInput.radical_lt hInput.radical_dvd
      hInput.radical_le hInput.phiSmall_lt hInput.phi_pos
      hInput.phi_lt hInput.phi_eq_source hPrimes hSumM hTermM hGM
  dsimp only at hrun ⊢
  simpa only [cellMarkedStep] using hrun

end LeanCompCert.Ports.Prop1224Cell
