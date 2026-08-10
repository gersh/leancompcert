import LeanCompCert.Ports.CDEMAbelMark
import LeanCompCert.Ports.CDEMAbelOuterSchedule

/-!
# Scheduling the CDEM Abel marking phase

This module lifts the literal active `markBody` contracts through the actual
selector, inactive sieve/accumulator, and period-tail blocks.  It starts with
the window-boundary iteration that seeds the resident plane with `mu(1)`.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkSchedule

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMark

/-- Selector semantics inside the active marking interval. -/
theorem selectors_mark_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : st.regs rR < c.markSteps) :
    let out := arun idx st c.selectors
    out.regs 40 = 0 ∧ out.regs 41 = 1 ∧ out.regs 42 = 1 ∧
      out.regs 43 = 0 ∧ out.arr = st.arr := by
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hsieveMod : c.sieveLen % M = c.sieveLen := Nat.mod_eq_of_lt hsieveM
  have hmarkMod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hmarkM
  have hnotS : ¬ idx < c.sieveLen := Nat.not_lt.mpr hsieve
  have hR2 : st.regs 2 < c.markSteps := by simpa [rR] using hR
  have h1M : (1 : Nat) % M = 1 := by decide
  have hwrap1 : (1 + M) % M = 1 := by decide
  have hwrap0 : (1 + (M - 1)) % M = 0 := by decide
  simp [Cfg.selectors, arun, astep, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, hidxMod, hsieveMod,
    hmarkMod, hnotS, hR2, h1M, hwrap1, hwrap0]

theorem body_mark_split (c : Cfg) :
    c.body = c.selectors ++ c.sieveBody ++ c.markBody ++ c.accBody ++
      c.tailBody := by
  simp [Cfg.body, Cfg.accBody, List.append_assoc]

/-- The inactive accumulation selector redirects the head store to the sink. -/
theorem headPre_inactive_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    let pre := srun idx st.regs (headPreS c)
    pre 140 = 0 ∧ pre 141 = 0 ∧ pre 144 = c.sink := by
  have h0M : (0 : Nat) % M = 0 := by decide
  have h1M : (1 : Nat) % M = 1 := by decide
  have hzero' : st.regs 1 = 0 := by simpa [rZero] using hzero
  simp [headPreS, Section413G1Denote.muxS, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rC, rZero, hgate, hzero',
    h0M, h1M, Nat.mod_eq_of_lt hsinkM]

/-- The inactive accumulation head changes no non-sink array cell. -/
theorem accHead_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink → (arun idx st c.accHead).arr j = st.arr j := by
  let pre := srun idx st.regs (headPreS c)
  have hpre := headPre_inactive_run c idx st hgate hzero hsinkM
  change pre 140 = 0 ∧ pre 141 = 0 ∧ pre 144 = c.sink at hpre
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  have hhead := accHead_arun c idx st
  dsimp only at hhead
  have hloaded144 : loaded 144 = c.sink := by
    simp [loaded, RegState.set, hpre.2.2]
  have hloadedZero : loaded rZero = 0 := by
    rw [show loaded rZero = pre rZero by
      simp [loaded, RegState.set, rZero]]
    rw [show pre rZero = st.regs rZero from
      RegFrame.srun_frame idx rZero (headPreS c) (by rfl) st.regs, hzero]
  intro j hj
  rw [show arun idx st c.accHead =
      ⟨srun idx loaded (headPostS c), cleared⟩ by
    simpa [pre, loaded, cleared] using hhead]
  simp [cleared, hloaded144, hj]

set_option maxRecDepth 4096 in
/-- Inactive head execution preserves the final-round and cell latches. -/
theorem accHead_inactive_last_cell (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    let out := arun idx st c.accHead
    out.regs 141 = 0 ∧ out.regs rC = st.regs rC := by
  let pre := srun idx st.regs (headPreS c)
  have hpre := headPre_inactive_run c idx st hgate hzero hsinkM
  change pre 140 = 0 ∧ pre 141 = 0 ∧ pre 144 = c.sink at hpre
  let loaded := RegState.set pre 148 (st.arr (pre 144))
  let cleared := fun j => if j = loaded 144 then loaded rZero else st.arr j
  have hhead := accHead_arun c idx st
  dsimp only at hhead
  have hloaded141 : loaded 141 = 0 := by
    rw [show loaded 141 = pre 141 by simp [loaded, RegState.set], hpre.2.1]
  have hloadedC : loaded rC = st.regs rC := by
    rw [show loaded rC = pre rC by simp [loaded, RegState.set, rC]]
    exact RegFrame.srun_frame idx rC (headPreS c) (by rfl) st.regs
  rw [hhead]
  exact
    ⟨(RegFrame.srun_frame idx 141 (headPostS c) (by rfl) loaded).trans
        hloaded141,
      (RegFrame.srun_frame idx rC (headPostS c) (by rfl) loaded).trans
        hloadedC⟩

/-- With the accumulation selector off, the accumulation head redirects its
only store to the sink.  The remaining accumulation blocks are store-free. -/
theorem accBody_head_split (c : Cfg) :
    c.accBody = c.accHead ++ (c.accProd ++ c.accBisect) := by
  simp [Cfg.accBody, List.append_assoc]

set_option maxRecDepth 4096 in
theorem accBody_tail_store_free (c : Cfg) :
    (c.accProd ++ c.accBisect).all avoidsStore = true := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem accBody_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink → (arun idx st c.accBody).arr j = st.arr j := by
  let headed := arun idx st c.accHead
  have hheaded := accHead_inactive_live_frame c idx st hgate hzero hsinkM
  let finished := arun idx headed (c.accProd ++ c.accBisect)
  have hfinishedArr : finished.arr = headed.arr :=
    arun_store_free_arr idx (c.accProd ++ c.accBisect) headed
      (accBody_tail_store_free c)
  intro j hj
  rw [accBody_head_split, arun_append]
  change finished.arr j = st.arr j
  rw [congrFun hfinishedArr j]
  exact hheaded j hj

set_option maxRecDepth 4096 in
theorem accBody_divisor_frame (c : Cfg) (idx : Nat) (st : AState) :
    (arun idx st c.accBody).regs rD = st.regs rD :=
  ArrayRegFrame.arun_frame idx rD c.accBody (by rfl) st

set_option maxRecDepth 4096 in
theorem accBody_sign_frame (c : Cfg) (idx : Nat) (st : AState) :
    (arun idx st c.accBody).regs rSg = st.regs rSg :=
  ArrayRegFrame.arun_frame idx rSg c.accBody (by rfl) st

set_option maxRecDepth 4096 in
theorem accBody_multiple_frame (c : Cfg) (idx : Nat) (st : AState) :
    (arun idx st c.accBody).regs rJ = st.regs rJ :=
  ArrayRegFrame.arun_frame idx rJ c.accBody (by rfl) st

structure AccProdLastCellFrame (before after : AState) : Prop where
  last : after.regs 141 = before.regs 141
  cell : after.regs rC = before.regs rC

set_option maxRecDepth 4096 in
theorem accProd_last_cell_frame (c : Cfg) (idx : Nat) (st : AState) :
    AccProdLastCellFrame st (arun idx st c.accProd) :=
  { last := ArrayRegFrame.arun_frame idx 141 c.accProd (by rfl) st
    cell := ArrayRegFrame.arun_frame idx rC c.accProd (by rfl) st }

def accBisectBeforeAdvanceS (c : Cfg) : List Instr :=
  openS c ++ roundS c ++ closeHeadS ++
    Section413G1Denote.mulWideG 4294967295 4294967296
      203 rSh 204 205 180 181 182 183 184 185 186 187 ++
    CDEMAbelPrimitives.addWideS rVLo rVHi 204 205 188

theorem accBisectScalar_advance_split (c : Cfg) :
    accBisectScalarS c = accBisectBeforeAdvanceS c ++ closeAdvanceS := by
  simp only [accBisectScalarS]
  rw [closeS_decomp]
  simp [accBisectBeforeAdvanceS, List.append_assoc]

set_option maxRecDepth 4096 in
theorem accBisect_cell_zero (c : Cfg) (idx : Nat) (st : AState)
    (hlast : st.regs 141 = 0) (hcell : st.regs rC = 0) :
    (arun idx st c.accBisect).regs rC = 0 := by
  let pre := srun idx st.regs (accBisectBeforeAdvanceS c)
  have hpreLast : pre 141 = 0 :=
    (RegFrame.srun_frame idx 141 (accBisectBeforeAdvanceS c) (by rfl)
      st.regs).trans hlast
  have hpreCell : pre rC = 0 :=
    (RegFrame.srun_frame idx rC (accBisectBeforeAdvanceS c) (by rfl)
      st.regs).trans hcell
  rw [accBisect_arun]
  change srun idx st.regs (accBisectScalarS c) rC = 0
  rw [accBisectScalar_advance_split, srun_append]
  change srun idx pre closeAdvanceS rC = 0
  have h0M : (0 : Nat) % M = 0 := by decide
  have hpre15 : pre 15 = 0 := by simpa [rC] using hpreCell
  simp [closeAdvanceS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rKr, rC, hpreLast, hpre15, h0M]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- The full inactive accumulation phase preserves a zero cell cursor. -/
theorem accBody_inactive_cell_zero (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 43 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hcell : st.regs rC = 0) :
    (arun idx st c.accBody).regs rC = 0 := by
  let headed := arun idx st c.accHead
  have hh := accHead_inactive_last_cell c idx st hgate hzero hsinkM
  change headed.regs 141 = 0 ∧ headed.regs rC = st.regs rC at hh
  let produced := arun idx headed c.accProd
  have hp := accProd_last_cell_frame c idx headed
  change AccProdLastCellFrame headed produced at hp
  have hb := accBisect_cell_zero c idx produced
    (hp.last.trans hh.1) (hp.cell.trans (hh.2.trans hcell))
  rw [Cfg.accBody, arun_append, arun_append]
  exact hb

def markBeforeAccRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (arun idx (arun idx st c.selectors) c.sieveBody) c.markBody

def markScheduledRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (markBeforeAccRun c idx st) c.accBody

theorem body_mark_schedule_run (c : Cfg) (idx : Nat) (st : AState) :
    arun idx st c.body = arun idx (markScheduledRun c idx st) c.tailBody := by
  rw [body_mark_split, arun_append, arun_append, arun_append, arun_append]
  rfl

structure FirstScheduledMarkBeforeAccSpec (c : Cfg)
    (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j =
    if j = c.winBase then (before.arr c.winBase + 1) % M else before.arr j
  divisor : after.regs rD = 1
  sign : after.regs rSg = 1
  multiple : after.regs rJ = 1
  cell : after.regs rC = 0
  phase : after.regs 41 = 1
  gate : after.regs 43 = 0
  zero : after.regs rZero = 0
  periodCursor : after.regs rR = 0
  window : after.regs rW = before.regs rW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem body_first_scheduled_mark_before_acc (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hsegPos : 0 < c.segLen) (hkPos : 0 < c.kBound)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hwinM : c.winBase < M) (hsinkM : c.sink < M) :
    FirstScheduledMarkBeforeAccSpec c st (markBeforeAccRun c idx st) := by
  let selected := arun idx st c.selectors
  have hsel := selectors_mark_run c idx st hidxM hsieveM hsieve hmarkM
    (by rw [hR]; exact hmarkPos)
  change selected.regs 40 = 0 ∧ selected.regs 41 = 1 ∧
      selected.regs 42 = 1 ∧ selected.regs 43 = 0 ∧
      selected.arr = st.arr at hsel
  have hselectedZero : selected.regs rZero = 0 := by
    rw [show selected.regs rZero = st.regs rZero from
      ArrayRegFrame.arun_frame idx rZero c.selectors (by rfl) st, hzero]
  let sieved := arun idx selected c.sieveBody
  have hsieveLive := sieve_inactive_live_frame c idx selected hsel.1
    hselectedZero hsinkM
  have sievedFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.sieveBody = false) :
      sieved.regs j = selected.regs j :=
    ArrayRegFrame.arun_frame idx j c.sieveBody hwrites selected
  have hs41 : sieved.regs 41 = 1 := (sievedFrame 41 (by rfl)).trans hsel.2.1
  have hs42 : sieved.regs 42 = 1 :=
    (sievedFrame 42 (by rfl)).trans hsel.2.2.1
  have hsR : sieved.regs rR = 0 := by
    rw [sievedFrame rR (by rfl),
      show selected.regs rR = st.regs rR from
        ArrayRegFrame.arun_frame idx rR c.selectors (by rfl) st, hR]
  have hsZero : sieved.regs rZero = 0 :=
    (sievedFrame rZero (by rfl)).trans hselectedZero
  let marked := arun idx sieved c.markBody
  have hm := markBody_first_active c idx sieved hs41 hs42 hsR hsZero
    hsegPos hkPos hsegM hkM hwinM
  have hwinNe : c.winBase ≠ c.sink := by
    unfold Cfg.sink
    omega
  have hmLive : ∀ j, j ≠ c.sink → marked.arr j =
      if j = c.winBase then (st.arr c.winBase + 1) % M else st.arr j := by
    intro j hj
    rw [hm.array j]
    by_cases hw : j = c.winBase
    · subst j
      rw [if_pos rfl, if_pos rfl, hsieveLive c.winBase hwinNe,
        congrFun hsel.2.2.2.2 c.winBase]
    · rw [if_neg hw, if_neg hw, hsieveLive j hj,
        congrFun hsel.2.2.2.2 j]
  have markFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.markBody = false) :
      marked.regs j = sieved.regs j :=
    ArrayRegFrame.arun_frame idx j c.markBody hwrites sieved
  have hall : FirstScheduledMarkBeforeAccSpec c st marked :=
    { live := hmLive
      divisor := hm.divisor
      sign := hm.sign
      multiple := hm.multiple
      cell := hm.cell
      phase := (markFrame 41 (by rfl)).trans hs41
      gate := (markFrame 43 (by rfl)).trans
        ((sievedFrame 43 (by rfl)).trans hsel.2.2.2.1)
      zero := (markFrame rZero (by rfl)).trans hsZero
      periodCursor := (markFrame rR (by rfl)).trans hsR
      window := (markFrame rW (by rfl)).trans
        ((sievedFrame rW (by rfl)).trans
          (ArrayRegFrame.arun_frame idx rW c.selectors (by rfl) st)) }
  simpa [markBeforeAccRun, selected, sieved, marked] using hall

/-- Observable result through the inactive accumulator, before the period
tail advances the schedule cursor. -/
structure FirstScheduledMarkCoreSpec (c : Cfg) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j =
    if j = c.winBase then (before.arr c.winBase + 1) % M else before.arr j
  divisor : after.regs rD = 1
  sign : after.regs rSg = 1
  multiple : after.regs rJ = 1
  cell : after.regs rC = 0
  phase : after.regs 41 = 1
  periodCursor : after.regs rR = 0
  window : after.regs rW = before.regs rW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem body_first_scheduled_mark_core (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hsegPos : 0 < c.segLen) (hkPos : 0 < c.kBound)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hwinM : c.winBase < M) (hsinkM : c.sink < M) :
    FirstScheduledMarkCoreSpec c st (markScheduledRun c idx st) := by
  let marked := markBeforeAccRun c idx st
  have hm := body_first_scheduled_mark_before_acc c idx st hidxM hsieveM
    hsieve hmarkPos hmarkM hR hzero hsegPos hkPos hsegM hkM hwinM hsinkM
  change FirstScheduledMarkBeforeAccSpec c st marked at hm
  have haccCursor := accBody_cursor_frame c idx marked
  have haccLive := accBody_inactive_live_frame c idx marked
    hm.gate hm.zero hsinkM
  have haccCell := accBody_inactive_cell_zero c idx marked hm.gate hm.zero
    hsinkM hm.cell
  have haccD : (arun idx marked c.accBody).regs rD = 1 :=
    (accBody_divisor_frame c idx marked).trans hm.divisor
  have haccSg : (arun idx marked c.accBody).regs rSg = 1 :=
    (accBody_sign_frame c idx marked).trans hm.sign
  have haccJ : (arun idx marked c.accBody).regs rJ = 1 :=
    (accBody_multiple_frame c idx marked).trans hm.multiple
  have hfinalLive : ∀ j, j ≠ c.sink →
      (arun idx marked c.accBody).arr j =
      if j = c.winBase then (st.arr c.winBase + 1) % M else st.arr j := by
    intro j hj
    exact (haccLive j hj).trans (hm.live j hj)
  have hall : FirstScheduledMarkCoreSpec c st
      (arun idx marked c.accBody) :=
    { live := hfinalLive
      divisor := haccD
      sign := haccSg
      multiple := haccJ
      cell := haccCell
      phase := haccCursor.phase.trans hm.phase
      periodCursor := haccCursor.cursor.trans hm.periodCursor
      window := haccCursor.window.trans hm.window }
  simpa [markScheduledRun, marked] using hall

/-- Observable result of the actual first marking body iteration, including
the period-tail cursor advance. -/
structure FirstScheduledMarkSpec (c : Cfg) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j =
    if j = c.winBase then (before.arr c.winBase + 1) % M else before.arr j
  divisor : after.regs rD = 1
  sign : after.regs rSg = 1
  multiple : after.regs rJ = 1
  cell : after.regs rC = 0
  periodCursor : after.regs rR = 1
  window : after.regs rW = before.regs rW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem body_first_scheduled_mark (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hperiodM : c.period < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hsegPos : 0 < c.segLen) (hkPos : 0 < c.kBound)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hwinM : c.winBase < M) (hsinkM : c.sink < M)
    (hWword : st.regs rW < M) :
    FirstScheduledMarkSpec c st (arun idx st c.body) := by
  let accumulated := markScheduledRun c idx st
  have hc := body_first_scheduled_mark_core c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hR hzero hsegPos hkPos hsegM hkM hwinM hsinkM
  change FirstScheduledMarkCoreSpec c st accumulated at hc
  have hperiodOne : 1 < c.period := by
    simp only [Cfg.period, Cfg.accSteps]
    have : 0 < c.segLen * (c.bsSteps + 1) := Nat.mul_pos hsegPos (by omega)
    omega
  have ht := tail_continue_window_run c idx accumulated hc.phase
    (by rw [hc.periodCursor]; exact hperiodOne)
    (by rw [hc.periodCursor]; decide) hperiodM hsegM
    (by rw [hc.window]; exact hWword)
  let finished := arun idx accumulated c.tailBody
  dsimp only at ht
  have htR : finished.regs rR = 1 := by
    change (arun idx accumulated c.tailBody).regs rR = 1
    rw [ht.1, hc.periodCursor]
  have htW : finished.regs rW = st.regs rW := by
    change (arun idx accumulated c.tailBody).regs rW = st.regs rW
    rw [ht.2, hc.window]
  have htailArr : finished.arr = accumulated.arr :=
    arun_store_free_arr idx c.tailBody accumulated (by rfl)
  have tailFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.tailBody = false) :
      finished.regs j = accumulated.regs j :=
    ArrayRegFrame.arun_frame idx j c.tailBody hwrites accumulated
  have hrun : arun idx st c.body = finished :=
    body_mark_schedule_run c idx st
  rw [hrun]
  exact
    { live := fun j hj => by
        rw [congrFun htailArr j]
        exact hc.live j hj
      divisor := (tailFrame rD (by rfl)).trans
        hc.divisor
      sign := (tailFrame rSg (by rfl)).trans
        hc.sign
      multiple := (tailFrame rJ (by rfl)).trans
        hc.multiple
      cell := (tailFrame rC (by rfl)).trans
        hc.cell
      periodCursor := htR
      window := htW }

end LeanCompCert.Ports.CDEMAbelMarkSchedule
