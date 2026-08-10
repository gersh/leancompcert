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

def sieveInactiveSuffix (c : Cfg) : List AInstr :=
  [ .scalar (.binop 64 .mul (.reg 64) (.reg 40))
  , .scalar (.binop 65 .add (.reg rN) (.lit c.muBase)) ] ++
    muxBody 66 64 65 rZero 67 ++
  [ .scalar (.binop 68 .sub (.lit 1) (.reg 64))
  , .scalar (.binop 69 .mul (.reg 68) (.lit c.sink))
  , .scalar (.binop 66 .add (.reg 66) (.reg 69))
  , .store 66 63
  , .scalar (.binop 70 .add (.reg rPj) (.reg 40))
  , .scalar (.binop 71 .sub (.lit 1) (.reg 64))
  , .scalar (.binop rPj .mul (.reg 70) (.reg 71))
  , .scalar (.binop rN .add (.reg rN) (.reg 64)) ]

theorem sieveBody_inactive_split (c : Cfg) :
    c.sieveBody = c.sieveBody.take 30 ++ sieveInactiveSuffix c := by
  simp [Cfg.sieveBody, sieveInactiveSuffix, muxBody]

def avoidsStore : AInstr → Bool
  | .store _ _ => false
  | _ => true

theorem arun_store_free_arr (idx : Nat) : ∀ (l : List AInstr) (st : AState),
    l.all avoidsStore = true → (arun idx st l).arr = st.arr := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons i rest ih =>
      intro st h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load dest address => exact AState.writeReg_arr _ _ _
      | store address value => simp [avoidsStore] at h

theorem sieve_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink →
      (arun idx st c.sieveBody).arr j = st.arr j := by
  intro j hj
  let pre := arun idx st (c.sieveBody.take 30)
  have hgatePre : pre.regs 40 = 0 := by
    rw [show pre.regs 40 = st.regs 40 from
      ArrayRegFrame.arun_frame idx 40 (c.sieveBody.take 30) (by rfl) st,
      hgate]
  have hzeroPre : pre.regs rZero = 0 := by
    rw [show pre.regs rZero = st.regs rZero from
      ArrayRegFrame.arun_frame idx rZero (c.sieveBody.take 30) (by rfl) st,
      hzero]
  have hzeroPre1 : pre.regs 1 = 0 := by simpa [rZero] using hzeroPre
  have harrPre : pre.arr = st.arr := by
    exact arun_store_free_arr idx (c.sieveBody.take 30) st (by rfl)
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  rw [sieveBody_inactive_split, arun_append]
  change (arun idx pre (sieveInactiveSuffix c)).arr j = st.arr j
  simp [sieveInactiveSuffix, muxBody, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    AState.writeArr, rZero, rN, rPj, hgatePre, hzeroPre1, hsinkMod, hj,
    harrPre]

def markInactiveStoreBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop 82 .mul (.reg 82) (.reg 42))
  , .scalar (.binop 83 .mul (.reg 82) (.reg rJ))
  , .scalar (.binop 84 .sub (.lit 1) (.reg 82))
  , .scalar (.binop 85 .mul (.reg 84) (.lit c.sink))
  , .scalar (.binop 86 .mul (.reg 82) (.lit c.winBase))
  , .scalar (.binop 83 .add (.reg 83) (.reg 86))
  , .scalar (.binop 83 .add (.reg 83) (.reg 85))
  , .load 87 83
  , .scalar (.binop 88 .mul (.reg 82) (.reg rSg))
  , .scalar (.binop 87 .add (.reg 87) (.reg 88))
  , .store 83 87 ]

theorem markBody_inactive_split (c : Cfg) :
    c.markBody = c.markBody.take 21 ++ markInactiveStoreBlock c ++
      c.markBody.drop 32 := by
  simp [Cfg.markBody, markInactiveStoreBlock, muxBody]

theorem mark_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 42 = 0) (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink → (arun idx st c.markBody).arr j = st.arr j := by
  intro j hj
  let pre := arun idx st (c.markBody.take 21)
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hgatePre : pre.regs 42 = 0 := by
    rw [show pre.regs 42 = st.regs 42 from
      ArrayRegFrame.arun_frame idx 42 (c.markBody.take 21) (by rfl) st,
      hgate]
  have harrPre : pre.arr = st.arr :=
    arun_store_free_arr idx (c.markBody.take 21) st (by rfl)
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  have hstored : stored.arr j = st.arr j := by
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rJ, rSg, hgatePre, hsinkMod, hj, harrPre]
  have htail : (arun idx stored (c.markBody.drop 32)).arr = stored.arr :=
    arun_store_free_arr idx (c.markBody.drop 32) stored (by rfl)
  rw [markBody_inactive_split, arun_append, arun_append]
  exact (congrFun htail j).trans hstored

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
