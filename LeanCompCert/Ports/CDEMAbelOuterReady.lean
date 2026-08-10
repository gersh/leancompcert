import LeanCompCert.Ports.CDEMAbelOuterSchedule

namespace LeanCompCert.Ports.CDEMAbelOuterReady

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelBody
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelSchedule
open LeanCompCert.Ports.CDEMAbelOuterSchedule

structure FirstStepReady (c : Cfg) (idx : Nat) (st : AState) : Prop where
  round0 : st.regs rKr = 0
  steps_pos : 0 < c.bsSteps
  steps_word : c.bsSteps < M
  gate : st.regs 43 = 1
  zero : st.regs rZero = 0
  addr_word : st.regs rC + c.winBase < M
  regs_word : ∀ j, st.regs j < M
  arr_word : ∀ j, st.arr j < M
  key_pos : 0 < st.regs rW + st.regs rC
  key_word : st.regs rW + st.regs rC < M
  key_closed : st.regs rW + st.regs rC <
    st.regs rT2 + (2 * (st.regs rT + 1) + 1)
  t_word : st.regs rT + 1 < M
  double_word : 2 * (st.regs rT + 1) + 1 < M
  t2_word : st.regs rT2 + (2 * (st.regs rT + 1) + 1) < M
  scale_word : c.wScale < M
  delta_sum_word :
    headDPos (headG ((st.regs rF +
      st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) +
    headDNeg (headG ((st.regs rF +
      st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) < M
  tv_word : st.regs rTv +
    (headDPos (headG ((st.regs rF +
      st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE) +
     headDNeg (headG ((st.regs rF +
      st.arr (st.regs rC + c.winBase)) % M)) (st.regs rE)) < M
  ceil_word : c.wScale - 1 + (st.regs rW + st.regs rC) < M
  sqrt_step : (if st.regs rW + st.regs rC < st.regs rT2 then
      st.regs rT else st.regs rT + 1) =
    Nat.sqrt (st.regs rW + st.regs rC)
  sqrt_pos : 0 < Nat.sqrt (st.regs rW + st.regs rC)
  scale_pos : 0 < c.wScale
  scale_plus_sqrt_word :
    c.wScale + Nat.sqrt (st.regs rW + st.regs rC) < M
  round_counter_word : st.regs rKr + st.regs 43 < M
  uPos_fit : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
    (arun idx st c.accHead).regs 169 *
      (arun idx st c.accHead).regs 167 < AddWide.B128
  uNeg_fit : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
    (arun idx st c.accHead).regs 170 *
      (arun idx st c.accHead).regs 168 < AddWide.B128

theorem accBody_first_of_ready (c : Cfg) (idx : Nat) (st : AState)
    (h : FirstStepReady c idx st) :
    FirstBodySpec c (st.regs rW + st.regs rC)
      ((arun idx st c.accHead).regs 169)
      ((arun idx st c.accHead).regs 170)
      ((arun idx st c.accHead).regs 167)
      ((arun idx st c.accHead).regs 168) st (arun idx st c.accBody) := by
  exact accBody_first_run c idx st h.round0 h.steps_pos h.steps_word h.gate
    h.zero h.addr_word h.regs_word h.arr_word h.key_pos h.key_word
    h.key_closed h.t_word h.double_word h.t2_word h.scale_word
    h.delta_sum_word h.tv_word h.ceil_word h.sqrt_step h.sqrt_pos
    h.scale_pos h.scale_plus_sqrt_word h.round_counter_word h.uPos_fit
    h.uNeg_fit

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem body_first_ready_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hcellRange : st.regs rC < c.segLen)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hready : FirstStepReady c idx (arun idx st (accPrefix c))) :
    let prefixed := arun idx st (accPrefix c)
    OuterFirstSpec c (prefixed.regs rW + prefixed.regs rC)
      ((arun idx prefixed c.accHead).regs 169)
      ((arun idx prefixed c.accHead).regs 170)
      ((arun idx prefixed c.accHead).regs 167)
      ((arun idx prefixed c.accHead).regs 168) st (arun idx st c.body) := by
  apply body_first_live_of_acc c idx st
    ((arun idx st (accPrefix c)).regs rW +
      (arun idx st (accPrefix c)).regs rC)
    ((arun idx (arun idx st (accPrefix c)) c.accHead).regs 169)
    ((arun idx (arun idx st (accPrefix c)) c.accHead).regs 170)
    ((arun idx (arun idx st (accPrefix c)) c.accHead).regs 167)
    ((arun idx (arun idx st (accPrefix c)) c.accHead).regs 168)
    hidxM hsieveM hsieve hmarkPos hmarkM hR hcellRange hzero hsinkM
    hword harrword
  exact accBody_first_of_ready c idx (arun idx st (accPrefix c)) hready

structure ProductionOuterMiddleCore (c : Cfg)
    (k dp dn n cell baseR baseW : Nat) (st : AState) : Prop where
  key : st.regs rK = k
  dPos : st.regs rDp = dp
  dNeg : st.regs rDn = dn
  gate : st.regs 43 = 1
  zero : st.regs rZero = 0
  round : st.regs rKr = n + 1
  cell : st.regs rC = cell
  cursor : st.regs rR = baseR + n
  window : st.regs rW = baseW
  regs_word : ∀ j, st.regs j < M
  arr_word : ∀ j, st.arr j < M

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem production_outer_middle_of_core (c : Cfg) (idx : Nat)
    (current first : AState) (k dp dn n cell baseR baseW : Nat)
    (hc : c.wScale = productionW)
    (hcore : ProductionOuterMiddleCore c k dp dn n cell baseR baseW current)
    (htrace : OuterMiddleTraceSpec c k (initial c.wScale k) n first current)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hbaseR : c.markSteps ≤ baseR)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hround : n + 1 < c.bsSteps) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hsum : dp + dn < M)
    (hceil : c.wScale - 1 + k < M) :
    OuterMiddleSpec c k
      (forwardIter c.wScale k n (initial c.wScale k)) current
      (arun idx current c.body) := by
  have hb := production_forward_bracket c hc k n hk
  dsimp only at hb
  apply body_middle_live_run c idx current k
    (forwardIter c.wScale k n (initial c.wScale k))
    hidxM hsieveM hsieve hmarkPos hmarkM
  · rw [hcore.cursor]
    omega
  · rw [hcore.round]
    omega
  · rw [hcore.round]
    omega
  · exact hcore.zero
  · exact hbsM
  · exact hsinkM
  · exact hcore.regs_word
  · exact hcore.arr_word
  · exact hcore.key
  · exact hk
  · rw [hc]
    decide
  · rw [hcore.dPos, hcore.dNeg]
    exact hsum
  · exact hceil
  · exact htrace.low
  · exact htrace.high
  · exact hb.1
  · exact hb.2
  · exact production_forward_roundFit c hc k n hk hkmax
  · exact production_forward_quotient_guard c hc k n hk hkmax
  · rw [hcore.round]
    omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem productionOuterMiddleCore_step (c : Cfg) (idx : Nat)
    (st : AState) (k dp dn n cell baseR baseW : Nat)
    (hcore : ProductionOuterMiddleCore c k dp dn n cell baseR baseW st)
    (p : Bracket)
    (hspec : OuterMiddleSpec c k p st (arun idx st c.body))
    (hcursor : (arun idx st c.body).regs rR = st.regs rR + 1 ∧
      (arun idx st c.body).regs rW = st.regs rW) :
    ProductionOuterMiddleCore c k dp dn (n + 1) cell baseR baseW
      (arun idx st c.body) := by
  have hw := arun_word idx c.body st hcore.regs_word hcore.arr_word
  exact
    { key := hspec.key.trans hcore.key
      dPos := hspec.dPos.trans hcore.dPos
      dNeg := hspec.dNeg.trans hcore.dNeg
      gate := hspec.gate
      zero := hspec.zero.trans hcore.zero
      round := by rw [hspec.round, hcore.round]
      cell := hspec.cell.trans hcore.cell
      cursor := by rw [hcursor.1, hcore.cursor]; omega
      window := hcursor.2.trans hcore.window
      regs_word := hw.1
      arr_word := hw.2 }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem bodyIter_production_middle_ready (c : Cfg) (idx count : Nat)
    (first : AState) (k dp dn cell baseR baseW : Nat)
    (hc : c.wScale = productionW) (hk : 0 < k)
    (hkmax : k ≤ productionKMax)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hbaseR : c.markSteps ≤ baseR)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsum : dp + dn < M) (hceil : c.wScale - 1 + k < M)
    (hperiodM : c.period < M) (hsegM : c.segLen < M)
    (hlo : first.regs rSl = (initial c.wScale k).lo)
    (hhi : first.regs rSh = (initial c.wScale k).hi)
    (hcore0 : ProductionOuterMiddleCore c k dp dn 0 cell baseR baseW first)
    (hcursorLt : ∀ i, i < count → baseR + i + 1 < c.period)
    (hcursorM : ∀ i, i < count → baseR + i + 1 < M)
    (hcount : count ≤ c.bsSteps - 1) :
    (∀ i, i < count →
      OuterMiddleSpec c k
        (forwardIter c.wScale k i (initial c.wScale k))
        (bodyIter c idx i first) (bodyIter c idx (i + 1) first)) ∧
      ProductionOuterMiddleCore c k dp dn count cell baseR baseW
        (bodyIter c idx count first) := by
  induction count with
  | zero =>
      exact ⟨fun _ hi => by omega, hcore0⟩
  | succ n ih =>
      have hncount : n ≤ c.bsSteps - 1 := by omega
      have hltPre : ∀ i, i < n → baseR + i + 1 < c.period :=
        fun i hi => hcursorLt i (by omega)
      have hMPre : ∀ i, i < n → baseR + i + 1 < M :=
        fun i hi => hcursorM i (by omega)
      have hprev := ih hltPre hMPre hncount
      have htrace := bodyIter_middle_contracts c idx n first k
        (initial c.wScale k) hlo hhi hprev.1
      have hnround : n + 1 < c.bsSteps := by omega
      have hspec := production_outer_middle_of_core c idx
        (bodyIter c idx n first) first k dp dn n cell baseR baseW hc
        hprev.2 htrace hidxM hsieveM hsieve hmarkPos hmarkM hbaseR hk
        hkmax hnround hbsM hsinkM hsum hceil
      have hcursor := body_cursor_continue_run c idx
        (bodyIter c idx n first) hidxM hsieveM hsieve hmarkM hmarkPos
        (by rw [hprev.2.cursor]; omega)
        (by rw [hprev.2.cursor]; exact hcursorLt n (by omega))
        (by rw [hprev.2.cursor]; exact hcursorM n (by omega))
        hperiodM hsegM hprev.2.regs_word hprev.2.arr_word
      dsimp only at hcursor
      have hnext := productionOuterMiddleCore_step c idx
        (bodyIter c idx n first) k dp dn n cell baseR baseW hprev.2
        (forwardIter c.wScale k n (initial c.wScale k)) hspec hcursor
      constructor
      · intro i hi
        by_cases hin : i < n
        · exact hprev.1 i hin
        · have hieq : i = n := by omega
          subst i
          change OuterMiddleSpec c k
            (forwardIter c.wScale k n (initial c.wScale k))
            (bodyIter c idx n first)
            (arun idx (bodyIter c idx n first) c.body)
          exact hspec
      · simpa [bodyIter] using hnext

theorem middle_cursor_lt_period (c : Cfg) (cell n : Nat)
    (hcell : cell < c.segLen) (hround : n < c.bsSteps - 1) :
    c.markSteps + cell * (c.bsSteps + 1) + 1 + n + 1 < c.period := by
  have hoff : n + 2 < c.bsSteps + 1 := by omega
  have hlocal :
      cell * (c.bsSteps + 1) + (n + 2) <
        (cell + 1) * (c.bsSteps + 1) := by
    rw [Nat.add_mul]
    simpa [Nat.add_assoc] using
      Nat.add_lt_add_left hoff (cell * (c.bsSteps + 1))
  have hmul :
      (cell + 1) * (c.bsSteps + 1) ≤
        c.segLen * (c.bsSteps + 1) :=
    Nat.mul_le_mul_right (c.bsSteps + 1) (by omega)
  have htotal := Nat.add_lt_add_left (Nat.lt_of_lt_of_le hlocal hmul)
    c.markSteps
  unfold Cfg.period Cfg.accSteps
  omega

theorem first_cursor_lt_period (c : Cfg) (cell : Nat)
    (hcell : cell < c.segLen) (hsteps : 0 < c.bsSteps) :
    c.markSteps + cell * (c.bsSteps + 1) + 1 < c.period := by
  have hoff : 1 < c.bsSteps + 1 := by omega
  have hlocal :
      cell * (c.bsSteps + 1) + 1 <
        (cell + 1) * (c.bsSteps + 1) := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left hoff (cell * (c.bsSteps + 1))
  have hmul :
      (cell + 1) * (c.bsSteps + 1) ≤
        c.segLen * (c.bsSteps + 1) :=
    Nat.mul_le_mul_right (c.bsSteps + 1) (by omega)
  have htotal := Nat.add_lt_add_left (Nat.lt_of_lt_of_le hlocal hmul)
    c.markSteps
  unfold Cfg.period Cfg.accSteps
  omega

theorem final_cursor_lt_period (c : Cfg) (cell : Nat)
    (hcell : cell + 1 < c.segLen) :
    c.markSteps + cell * (c.bsSteps + 1) + c.bsSteps + 1 < c.period := by
  have hs : 0 < c.bsSteps + 1 := by omega
  have hmul :
      (cell + 1) * (c.bsSteps + 1) <
        c.segLen * (c.bsSteps + 1) :=
    (Nat.mul_lt_mul_right hs).mpr hcell
  have htotal := Nat.add_lt_add_left hmul c.markSteps
  unfold Cfg.period Cfg.accSteps
  rw [Nat.add_mul] at htotal
  omega

theorem final_cursor_eq_period (c : Cfg) (cell : Nat)
    (hcell : cell + 1 = c.segLen) :
    c.markSteps + cell * (c.bsSteps + 1) + c.bsSteps + 1 = c.period := by
  unfold Cfg.period Cfg.accSteps
  rw [← hcell, Nat.add_mul]
  omega

theorem productionOuterCore_of_first (c : Cfg) (idx : Nat) (st : AState)
    (k dp dn ceil floor cell baseR baseW : Nat)
    (hf : OuterFirstSpec c k dp dn ceil floor st (arun idx st c.body))
    (hround : st.regs rKr = 0) (hzero : st.regs rZero = 0)
    (hcell : st.regs rC = cell)
    (hcursor : (arun idx st c.body).regs rR = baseR)
    (hwindow : (arun idx st c.body).regs rW = baseW)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    ProductionOuterMiddleCore c k dp dn 0 cell baseR baseW
      (arun idx st c.body) := by
  have hw := arun_word idx c.body st hword harrword
  exact
    { key := hf.key
      dPos := hf.dPos
      dNeg := hf.dNeg
      gate := hf.gate
      zero := hf.zero.trans hzero
      round := by rw [hf.round, hround]
      cell := hf.cell.trans hcell
      cursor := by simpa using hcursor
      window := hwindow
      regs_word := hw.1
      arr_word := hw.2 }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem production_outer_final_of_core (c : Cfg) (idx : Nat)
    (current first : AState) (k dp dn cell baseR baseW : Nat)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hbaseR : c.markSteps ≤ baseR)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsum : dp + dn < M) (hceil : c.wScale - 1 + k < M)
    (hcore : ProductionOuterMiddleCore c k dp dn (c.bsSteps - 1)
      cell baseR baseW current)
    (htrace : OuterMiddleTraceSpec c k (initial c.wScale k)
      (c.bsSteps - 1) first current)
    (hcellFit : cell + 1 < M)
    (haccFit : AddWide.wval (current.regs rVLo, current.regs rVHi) +
      (dp + dn) * exactRoot c.wScale k < AddWide.B128) :
    OuterFinalSpec c (exactRoot c.wScale k) (dp + dn) current
      (arun idx current c.body) := by
  have hbsPos : 0 < c.bsSteps := by
    rw [hsteps]
    simp [CDEMAbelScan.bsBudget]
  have hb := production_forward_bracket c hc k (c.bsSteps - 1) hk
  dsimp only at hb
  rw [← hcore.dPos, ← hcore.dNeg]
  apply body_final_live_run c idx current (exactRoot c.wScale k)
    hidxM hsieveM hsieve hmarkPos hmarkM
  · rw [hcore.cursor]
    omega
  · rw [hcore.round]
    omega
  · exact hbsPos
  · exact hcore.zero
  · exact hbsM
  · exact hsinkM
  · exact hcore.regs_word
  · exact hcore.arr_word
  · rw [hcore.key]
    exact hk
  · rw [hc]
    decide
  · rw [hcore.dPos, hcore.dNeg]
    exact hsum
  · rw [hcore.key]
    exact hceil
  · rw [htrace.low, htrace.high]
    exact hb.1
  · rw [htrace.high]
    exact hb.2
  · rw [hcore.key, htrace.low, htrace.high]
    exact production_forward_roundFit c hc k (c.bsSteps - 1) hk hkmax
  · rw [htrace.low, htrace.high]
    exact production_forward_quotient_guard c hc k (c.bsSteps - 1) hk hkmax
  · rw [hcore.key, htrace.low, htrace.high]
    exact final_step_exact c k hsteps (by rw [hc]; decide) hk
  · rw [hcore.cell]
    exact hcellFit
  · rw [hcore.dPos, hcore.dNeg]
    exact haccFit

structure ProductionCellCursorSpec (c : Cfg) (cell startR startW : Nat)
    (after : AState) : Prop where
  cursor : after.regs rR =
    if cell + 1 = c.segLen then 0 else startR + c.bsSteps + 1
  window : after.regs rW =
    if cell + 1 = c.segLen then startW + c.segLen else startW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem bodySchedule_production_ready (c : Cfg) (idx : Nat) (st : AState)
    (k dp dn ceil floor cell : Nat)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hWnext : st.regs rW + c.segLen < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hround : st.regs rKr = 0) (hzero : st.regs rZero = 0)
    (hcell : st.regs rC = cell) (hcellRange : cell < c.segLen)
    (hstartR : st.regs rR =
      c.markSteps + cell * (c.bsSteps + 1))
    (hready : FirstStepReady c idx (arun idx st (accPrefix c)))
    (hkeyVal : (arun idx st (accPrefix c)).regs rW +
      (arun idx st (accPrefix c)).regs rC = k)
    (hdpVal :
      (arun idx (arun idx st (accPrefix c)) c.accHead).regs 169 = dp)
    (hdnVal :
      (arun idx (arun idx st (accPrefix c)) c.accHead).regs 170 = dn)
    (hceilVal :
      (arun idx (arun idx st (accPrefix c)) c.accHead).regs 167 = ceil)
    (hfloorVal :
      (arun idx (arun idx st (accPrefix c)) c.accHead).regs 168 = floor)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hsum : dp + dn < M) (hceil : c.wScale - 1 + k < M)
    (haccFit :
      let current := bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)
      AddWide.wval (current.regs rVLo, current.regs rVHi) +
        (dp + dn) * exactRoot c.wScale k < AddWide.B128) :
    OuterFullAccSpec c k dp dn ceil floor (exactRoot c.wScale k) (dp + dn)
        st (bodySchedule c idx (c.bsSteps - 1) st) ∧
      ProductionCellCursorSpec c cell (st.regs rR) (st.regs rW)
        (bodySchedule c idx (c.bsSteps - 1) st) := by
  have hbsPos : 0 < c.bsSteps := by
    rw [hsteps]
    simp [CDEMAbelScan.bsBudget]
  have hfirst0 := body_first_ready_run c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM (by rw [hstartR]; omega)
    (by rw [hcell]; exact hcellRange) hzero hsinkM hword
    harrword hready
  have hfirst : OuterFirstSpec c k dp dn ceil floor st
      (arun idx st c.body) := by
    simpa only [hkeyVal, hdpVal, hdnVal, hceilVal, hfloorVal] using hfirst0
  have hfirstCursor := body_cursor_continue_run c idx st hidxM hsieveM
    hsieve hmarkM hmarkPos (by rw [hstartR]; omega)
    (by rw [hstartR]; exact first_cursor_lt_period c cell hcellRange hbsPos)
    (by
      rw [hstartR]
      exact Nat.lt_trans (first_cursor_lt_period c cell hcellRange hbsPos)
        hperiodM)
    hperiodM hsegM hword harrword
  dsimp only at hfirstCursor
  have hcore0 := productionOuterCore_of_first c idx st k dp dn ceil floor
    cell (c.markSteps + cell * (c.bsSteps + 1) + 1) (st.regs rW)
    hfirst hround hzero hcell
    (by rw [hfirstCursor.1, hstartR]) hfirstCursor.2 hword harrword
  have hmiddle := bodyIter_production_middle_ready c idx
    (c.bsSteps - 1) (arun idx st c.body) k dp dn cell
    (c.markSteps + cell * (c.bsSteps + 1) + 1) (st.regs rW)
    hc hk hkmax hidxM hsieveM hsieve hmarkPos hmarkM (by omega)
    hbsM hsinkM hsum hceil hperiodM hsegM hfirst.low hfirst.high hcore0
    (by
      intro i hi
      exact middle_cursor_lt_period c cell i hcellRange hi)
    (by
      intro i hi
      exact Nat.lt_trans (middle_cursor_lt_period c cell i hcellRange hi)
        hperiodM)
    (by omega)
  have htrace := bodyIter_middle_contracts c idx (c.bsSteps - 1)
    (arun idx st c.body) k (initial c.wScale k) hfirst.low hfirst.high
    hmiddle.1
  have hfinal := production_outer_final_of_core c idx
    (bodyIter c idx (c.bsSteps - 1) (arun idx st c.body))
    (arun idx st c.body) k dp dn cell
    (c.markSteps + cell * (c.bsSteps + 1) + 1) (st.regs rW)
    hc hsteps hk hkmax hidxM hsieveM hsieve hmarkPos hmarkM (by omega)
    hbsM hsinkM hsum hceil hmiddle.2 htrace (by omega) haccFit
  have hfull := bodySchedule_of_contracts c idx (c.bsSteps - 1) st
    k dp dn ceil floor (exactRoot c.wScale k) (dp + dn)
    hfirst htrace hfinal
  constructor
  · exact hfull
  · by_cases hlast : cell + 1 = c.segLen
    · have hwrap := body_cursor_wrap_run c idx
        (bodyIter c idx (c.bsSteps - 1) (arun idx st c.body))
        hidxM hsieveM hsieve hmarkM hmarkPos
        (by rw [hmiddle.2.cursor]; omega)
        (by
          rw [hmiddle.2.cursor]
          have heq := final_cursor_eq_period c cell hlast
          omega)
        hperiodM hsegM
        (by rw [hmiddle.2.window]; exact hWnext)
        hmiddle.2.regs_word hmiddle.2.arr_word
      dsimp only at hwrap
      exact
        { cursor := by simpa [ProductionCellCursorSpec, hlast, bodySchedule]
            using hwrap.1
          window := by
            simpa [ProductionCellCursorSpec, hlast, bodySchedule,
              hmiddle.2.window] using hwrap.2 }
    · have hnextCell : cell + 1 < c.segLen := by omega
      have hcontinue := body_cursor_continue_run c idx
        (bodyIter c idx (c.bsSteps - 1) (arun idx st c.body))
        hidxM hsieveM hsieve hmarkM hmarkPos
        (by rw [hmiddle.2.cursor]; omega)
        (by
          rw [hmiddle.2.cursor]
          have hlt := final_cursor_lt_period c cell hnextCell
          omega)
        (by
          rw [hmiddle.2.cursor]
          have hlt := final_cursor_lt_period c cell hnextCell
          omega)
        hperiodM hsegM hmiddle.2.regs_word hmiddle.2.arr_word
      dsimp only at hcontinue
      exact
        { cursor := by
            simp only [hlast, if_false]
            rw [show (bodySchedule c idx (c.bsSteps - 1) st).regs rR =
              (bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)).regs rR + 1
              from hcontinue.1,
              hmiddle.2.cursor, hstartR]
            omega
          window := by
            simp only [hlast, if_false]
            exact hcontinue.2.trans hmiddle.2.window }

theorem bodyIter_succ_start (c : Cfg) (idx n : Nat) (st : AState) :
    bodyIter c idx n (arun idx st c.body) = bodyIter c idx (n + 1) st := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change arun idx (bodyIter c idx n (arun idx st c.body)) c.body =
        arun idx (bodyIter c idx (n + 1) st) c.body
      exact congrArg (fun s => arun idx s c.body) ih

theorem bodySchedule_eq_bodyIter (c : Cfg) (idx middleCount : Nat)
    (st : AState) :
    bodySchedule c idx middleCount st = bodyIter c idx (middleCount + 2) st := by
  rw [bodySchedule, bodyIter_succ_start]
  rfl

structure CursorTraceSpec (n : Nat) (before after : AState) : Prop where
  cursor : after.regs rR = before.regs rR + n
  window : after.regs rW = before.regs rW

theorem bodyIter_cursor_contracts (c : Cfg) (idx n : Nat) (st : AState)
    (hcontract : ∀ i, i < n →
      let before := bodyIter c idx i st
      let after := bodyIter c idx (i + 1) st
      after.regs rR = before.regs rR + 1 ∧
        after.regs rW = before.regs rW) :
    CursorTraceSpec n st (bodyIter c idx n st) := by
  induction n with
  | zero =>
      exact
        { cursor := by simp [bodyIter]
          window := rfl }
  | succ n ih =>
      have hpre : ∀ i, i < n →
          let before := bodyIter c idx i st
          let after := bodyIter c idx (i + 1) st
          after.regs rR = before.regs rR + 1 ∧
            after.regs rW = before.regs rW :=
        fun i hi => hcontract i (by omega)
      have hi := ih hpre
      have hs := hcontract n (by omega)
      dsimp only at hs
      exact
        { cursor := by rw [hs.1, hi.cursor]; omega
          window := hs.2.trans hi.window }

theorem bodySchedule_cursor_of_contracts (c : Cfg) (idx middleCount : Nat)
    (st : AState)
    (hcontract : ∀ i, i < middleCount + 2 →
      let before := bodyIter c idx i st
      let after := bodyIter c idx (i + 1) st
      after.regs rR = before.regs rR + 1 ∧
        after.regs rW = before.regs rW) :
    let out := bodySchedule c idx middleCount st
    out.regs rR = st.regs rR + (middleCount + 2) ∧
      out.regs rW = st.regs rW := by
  have ht := bodyIter_cursor_contracts c idx (middleCount + 2) st hcontract
  rw [bodySchedule_eq_bodyIter]
  exact ⟨ht.cursor, ht.window⟩

end LeanCompCert.Ports.CDEMAbelOuterReady
