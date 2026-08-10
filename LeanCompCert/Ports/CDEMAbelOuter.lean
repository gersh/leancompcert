import LeanCompCert.Ports.CDEMAbelSchedule

namespace LeanCompCert.Ports.CDEMAbelOuter

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan

def selectorsS (c : Cfg) : List Instr :=
  [ .binop 40 .lt .idx (.lit c.sieveLen)
  , .binop 41 .sub (.lit 1) (.reg 40)
  , .binop 42 .lt (.reg rR) (.lit c.markSteps)
  , .binop 42 .mul (.reg 42) (.reg 41)
  , .binop 43 .sub (.reg 41) (.reg 42) ]

theorem selectors_lift (c : Cfg) : c.selectors = lift (selectorsS c) := rfl

theorem selectors_acc_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR) :
    let out := arun idx st c.selectors
    out.regs 40 = 0 ∧ out.regs 41 = 1 ∧ out.regs 42 = 0 ∧
      out.regs 43 = 1 ∧ out.arr = st.arr := by
  rw [selectors_lift, arun_lift]
  have hidxmod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hsievemod : c.sieveLen % M = c.sieveLen := Nat.mod_eq_of_lt hsieveM
  have hmarkmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hmarkM
  have hnotS : ¬idx < c.sieveLen := Nat.not_lt.mpr hsieve
  have hnotM : ¬st.regs rR < c.markSteps := Nat.not_lt.mpr hR
  have hnotM' : ¬st.regs 2 < c.markSteps := by simpa [rR] using hnotM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hwrap1 : (1 + M) % M = 1 := by decide
  simp [selectorsS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, hidxmod, hsievemod, hmarkmod, hnotS, hnotM', h1M, hwrap1]

def tailS (c : Cfg) : List Instr :=
  [ .binop 210 .add (.reg rR) (.reg 41)
  , .binop 211 .eq (.reg 210) (.lit c.period)
  , .binop 212 .sub (.lit 1) (.reg 211)
  , .binop rR .mul (.reg 210) (.reg 212)
  , .binop 213 .mul (.reg 211) (.lit c.segLen)
  , .binop rW .add (.reg rW) (.reg 213) ]

theorem tail_lift (c : Cfg) : c.tailBody = lift (tailS c) := rfl

theorem tail_continue_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hnext : st.regs rR + 1 < c.period)
    (hnextM : st.regs rR + 1 < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hword : ∀ j, st.regs j < M) :
    let out := arun idx st c.tailBody
    out.regs rR = st.regs rR + 1 ∧ out.regs rW = st.regs rW ∧
      out.arr = st.arr := by
  rw [tail_lift, arun_lift]
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiodM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hwMod' : st.regs 3 % M = st.regs 3 := by
    exact Nat.mod_eq_of_lt (by simpa [rW] using hword rW)
  have hne : st.regs rR + 1 ≠ c.period := by omega
  have hnextM' : st.regs 2 + 1 < M := by simpa [rR] using hnextM
  have hnextMod' : (st.regs 2 + 1) % M = st.regs 2 + 1 := by
    exact Nat.mod_eq_of_lt hnextM'
  have hne' : st.regs 2 + 1 ≠ c.period := by simpa [rR] using hne
  simp [tailS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, rW, hgate, hnextMod', hperiodMod, hsegMod, hwMod', hne']

theorem tail_wrap_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hnext : st.regs rR + 1 = c.period)
    (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hWnext : st.regs rW + c.segLen < M) :
    let out := arun idx st c.tailBody
    out.regs rR = 0 ∧ out.regs rW = st.regs rW + c.segLen ∧
      out.arr = st.arr := by
  rw [tail_lift, arun_lift]
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiodM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hnext' : st.regs 2 + 1 = c.period := by simpa [rR] using hnext
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hWnext' : st.regs 3 + c.segLen < M := by simpa [rW] using hWnext
  have hWmod' : (st.regs 3 + c.segLen) % M = st.regs 3 + c.segLen :=
    Nat.mod_eq_of_lt hWnext'
  simp [tailS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, rW, hgate, hperiodMod, hsegMod, hnext', hzero, hWmod']

end LeanCompCert.Ports.CDEMAbelOuter
