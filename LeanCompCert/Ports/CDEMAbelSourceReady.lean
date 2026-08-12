import LeanCompCert.Ports.CDEMAbelOuterReady

/-!
# Source-facing readiness for the CDEM Abel scan

This module starts the refinement below the verified literal cell scheduler.
It packages the incremental square-root invariant in source-shaped arithmetic
form and derives the exact branch equation required by `FirstStepReady`.
-/

namespace LeanCompCert.Ports.CDEMAbelSourceReady

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelOuterReady

/-- The streamed square-root state immediately before processing the integer
`rW + rC`.  `rT2` is the next square, the current root is not too large, and
one increment is enough for the next integer. -/
structure SqrtStreamInv (st : AState) : Prop where
  nextSquare : st.regs rT2 = (st.regs rT + 1) * (st.regs rT + 1)
  lower : st.regs rT * st.regs rT ≤ st.regs rW + st.regs rC
  oneBump : st.regs rW + st.regs rC <
    (st.regs rT + 2) * (st.regs rT + 2)

theorem sqrt_eq_of_square_bounds (k q : Nat)
    (hlo : q * q ≤ k) (hhi : k < (q + 1) * (q + 1)) :
    Nat.sqrt k = q := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hn
    have hq : q + 1 ≤ Nat.sqrt k := by omega
    have hmul :
        (q + 1) * (q + 1) ≤ Nat.sqrt k * Nat.sqrt k :=
      Nat.mul_le_mul hq hq
    exact (Nat.not_lt_of_ge (Nat.le_trans hmul (Nat.sqrt_le k))) hhi
  · apply Nat.le_of_not_gt
    intro hn
    have hs : Nat.sqrt k + 1 ≤ q := by omega
    have hmul :
        (Nat.sqrt k + 1) * (Nat.sqrt k + 1) ≤ q * q :=
      Nat.mul_le_mul hs hs
    exact (Nat.not_lt_of_ge (Nat.le_trans hmul hlo)) (Nat.lt_succ_sqrt k)

theorem sqrtStream_step (st : AState) (h : SqrtStreamInv st) :
    (if st.regs rW + st.regs rC < st.regs rT2 then
        st.regs rT else st.regs rT + 1) =
      Nat.sqrt (st.regs rW + st.regs rC) := by
  by_cases hlt : st.regs rW + st.regs rC < st.regs rT2
  · simp only [hlt, if_true]
    symm
    apply sqrt_eq_of_square_bounds
    · exact h.lower
    · rw [← h.nextSquare]
      exact hlt
  · simp only [hlt, if_false]
    symm
    apply sqrt_eq_of_square_bounds
    · rw [← h.nextSquare]
      exact Nat.le_of_not_gt hlt
    · simpa only [Nat.add_assoc] using h.oneBump

theorem sqrtStream_key_closed (st : AState) (h : SqrtStreamInv st) :
    st.regs rW + st.regs rC <
      st.regs rT2 + (2 * (st.regs rT + 1) + 1) := by
  rw [h.nextSquare]
  have hsquare :
      (st.regs rT + 2) * (st.regs rT + 2) =
        (st.regs rT + 1) * (st.regs rT + 1) +
          (2 * (st.regs rT + 1) + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  rw [← hsquare]
  exact h.oneBump

theorem sqrt_pos_of_pos {k : Nat} (hk : 0 < k) : 0 < Nat.sqrt k := by
  have hs := Nat.lt_succ_sqrt k
  by_cases hz : Nat.sqrt k = 0
  · rw [hz] at hs
    simp only [Nat.one_mul] at hs
    omega
  · exact Nat.pos_of_ne_zero hz

def nextKey (st : AState) : Nat := st.regs rW + st.regs rC

def nextF (c : Cfg) (st : AState) : Nat :=
  (st.regs rF + st.arr (st.regs rC + c.winBase)) % M

def nextDPos (c : Cfg) (st : AState) : Nat :=
  headDPos (headG (nextF c st)) (st.regs rE)

def nextDNeg (c : Cfg) (st : AState) : Nat :=
  headDNeg (headG (nextF c st)) (st.regs rE)

def nextCeil (c : Cfg) (st : AState) : Nat :=
  (c.wScale - 1 + nextKey st) / nextKey st

def nextFloor (c : Cfg) (st : AState) : Nat :=
  c.wScale / nextKey st

/-- Source-shaped state before the literal accumulation prefix.  The window
cell is the next floor-convolution increment; the wide no-wrap hypotheses are
stated with the mathematical delta and reciprocal values that the verified
head installs. -/
structure FirstEntryInv (c : Cfg) (st : AState) : Prop where
  round0 : st.regs rKr = 0
  zero : st.regs rZero = 0
  cell_range : st.regs rC < c.segLen
  sqrt : SqrtStreamInv st
  steps_pos : 0 < c.bsSteps
  steps_word : c.bsSteps < M
  addr_word : st.regs rC + c.winBase < M
  regs_word : ∀ j, st.regs j < M
  arr_word : ∀ j, st.arr j < M
  key_pos : 0 < nextKey st
  key_word : nextKey st < M
  t_word : st.regs rT + 1 < M
  double_word : 2 * (st.regs rT + 1) + 1 < M
  t2_word : st.regs rT2 + (2 * (st.regs rT + 1) + 1) < M
  scale_pos : 0 < c.wScale
  scale_word : c.wScale < M
  delta_sum_word : nextDPos c st + nextDNeg c st < M
  tv_word : st.regs rTv + (nextDPos c st + nextDNeg c st) < M
  ceil_word : c.wScale - 1 + nextKey st < M
  scale_plus_sqrt_word : c.wScale + Nat.sqrt (nextKey st) < M
  uPos_fit : AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
    nextDPos c st * nextCeil c st < AddWide.B128
  uNeg_fit : AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
    nextDNeg c st * nextFloor c st < AddWide.B128

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem firstStepReady_of_entry (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hsinkM : c.sink < M) (h : FirstEntryInv c st) :
    FirstStepReady c idx (arun idx st (accPrefix c)) := by
  let prefixed := arun idx st (accPrefix c)
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR h.regs_word h.arr_word
  have hw := arun_word idx (accPrefix c) st h.regs_word h.arr_word
  have hlive := accPrefix_live_frame c idx st hidxM hsieveM hsieve
    hmarkM hR h.zero hsinkM
  have frame (j : Nat)
      (hj : ArrayRegFrame.writes j (accPrefix c) = false) :
      prefixed.regs j = st.regs j := by
    exact ArrayRegFrame.arun_frame idx j (accPrefix c) hj st
  have haddrNe : st.regs rC + c.winBase ≠ c.sink := by
    unfold Cfg.sink
    have hc := h.cell_range
    omega
  have harrCell :
      prefixed.arr (st.regs rC + c.winBase) =
        st.arr (st.regs rC + c.winBase) := by
    exact hlive (st.regs rC + c.winBase) haddrNe
  have hhead := accHead_first_run c idx prefixed
    (by rw [hp.round]; exact h.round0) h.steps_pos h.steps_word hp.gate
    (by rw [hp.zero]; exact h.zero)
    (by rw [hp.cell]; exact h.addr_word) hw.1 hw.2
    (by rw [hp.window, hp.cell]; exact h.key_pos)
    (by rw [hp.window, hp.cell]; exact h.key_word)
    (by
      rw [hp.window, hp.cell, frame rT2 (by rfl), frame rT (by rfl)]
      exact sqrtStream_key_closed st h.sqrt)
    (by rw [frame rT (by rfl)]; exact h.t_word)
    (by rw [frame rT (by rfl)]; exact h.double_word)
    (by rw [frame rT2 (by rfl), frame rT (by rfl)]; exact h.t2_word)
    h.scale_word
    (by
      rw [frame rF (by rfl), frame rE (by rfl), hp.cell, harrCell]
      simpa [nextDPos, nextDNeg, nextF] using h.delta_sum_word)
    (by
      rw [frame rTv (by rfl), frame rF (by rfl), frame rE (by rfl),
        hp.cell, harrCell]
      simpa [nextDPos, nextDNeg, nextF] using h.tv_word)
    (by rw [hp.window, hp.cell]; exact h.ceil_word)
  exact
    { round0 := by rw [hp.round]; exact h.round0
      steps_pos := h.steps_pos
      steps_word := h.steps_word
      gate := hp.gate
      zero := by rw [hp.zero]; exact h.zero
      addr_word := by rw [hp.cell]; exact h.addr_word
      regs_word := hw.1
      arr_word := hw.2
      key_pos := by rw [hp.window, hp.cell]; exact h.key_pos
      key_word := by rw [hp.window, hp.cell]; exact h.key_word
      key_closed := by
        rw [hp.window, hp.cell, frame rT2 (by rfl), frame rT (by rfl)]
        exact sqrtStream_key_closed st h.sqrt
      t_word := by rw [frame rT (by rfl)]; exact h.t_word
      double_word := by rw [frame rT (by rfl)]; exact h.double_word
      t2_word := by
        rw [frame rT2 (by rfl), frame rT (by rfl)]
        exact h.t2_word
      scale_word := h.scale_word
      delta_sum_word := by
        rw [frame rF (by rfl), frame rE (by rfl), hp.cell, harrCell]
        simpa [nextDPos, nextDNeg, nextF] using h.delta_sum_word
      tv_word := by
        rw [frame rTv (by rfl), frame rF (by rfl), frame rE (by rfl),
          hp.cell, harrCell]
        simpa [nextDPos, nextDNeg, nextF] using h.tv_word
      ceil_word := by rw [hp.window, hp.cell]; exact h.ceil_word
      sqrt_step := by
        rw [hp.window, hp.cell, frame rT2 (by rfl), frame rT (by rfl)]
        exact sqrtStream_step st h.sqrt
      sqrt_pos := by
        rw [hp.window, hp.cell]
        exact sqrt_pos_of_pos (by simpa [nextKey] using h.key_pos)
      scale_pos := h.scale_pos
      scale_plus_sqrt_word := by
        rw [hp.window, hp.cell]
        exact h.scale_plus_sqrt_word
      round_counter_word := by
        rw [hp.round, hp.gate, h.round0]
        decide
      uPos_fit := by
        rw [hhead.posGate, hhead.ceil, frame rUpLo (by rfl),
          frame rUpHi (by rfl), hp.window, hp.cell, frame rF (by rfl),
          frame rE (by rfl), harrCell]
        simpa [nextDPos, nextF, nextCeil, nextKey] using h.uPos_fit
      uNeg_fit := by
        rw [hhead.negGate, hhead.floor, frame rUnLo (by rfl),
          frame rUnHi (by rfl), hp.window, hp.cell, frame rF (by rfl),
          frame rE (by rfl), harrCell]
        simpa [nextDNeg, nextF, nextFloor, nextKey] using h.uNeg_fit }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem firstValues_of_entry (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hsinkM : c.sink < M) (h : FirstEntryInv c st) :
    let prefixed := arun idx st (accPrefix c)
    prefixed.regs rW + prefixed.regs rC = nextKey st ∧
      (arun idx prefixed c.accHead).regs 169 = nextDPos c st ∧
      (arun idx prefixed c.accHead).regs 170 = nextDNeg c st ∧
      (arun idx prefixed c.accHead).regs 167 = nextCeil c st ∧
      (arun idx prefixed c.accHead).regs 168 = nextFloor c st := by
  let prefixed := arun idx st (accPrefix c)
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR h.regs_word h.arr_word
  have hready := firstStepReady_of_entry c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hR hsinkM h
  have hhead := accHead_first_run c idx prefixed hready.round0
    hready.steps_pos hready.steps_word hready.gate hready.zero
    hready.addr_word hready.regs_word hready.arr_word hready.key_pos
    hready.key_word hready.key_closed hready.t_word hready.double_word
    hready.t2_word hready.scale_word hready.delta_sum_word hready.tv_word
    hready.ceil_word
  have frame (j : Nat)
      (hj : ArrayRegFrame.writes j (accPrefix c) = false) :
      prefixed.regs j = st.regs j := by
    exact ArrayRegFrame.arun_frame idx j (accPrefix c) hj st
  have haddrNe : st.regs rC + c.winBase ≠ c.sink := by
    unfold Cfg.sink
    have hc := h.cell_range
    omega
  have harrCell :
      prefixed.arr (st.regs rC + c.winBase) =
        st.arr (st.regs rC + c.winBase) :=
    (accPrefix_live_frame c idx st hidxM hsieveM hsieve hmarkM hR
      h.zero hsinkM) (st.regs rC + c.winBase) haddrNe
  exact
    ⟨by rw [hp.window, hp.cell]; rfl,
      by
        rw [hhead.posGate, frame rF (by rfl), frame rE (by rfl),
          hp.cell, harrCell]
        rfl,
      by
        rw [hhead.negGate, frame rF (by rfl), frame rE (by rfl),
          hp.cell, harrCell]
        rfl,
      by rw [hhead.ceil, hp.window, hp.cell]; rfl,
      by rw [hhead.floor, hp.window, hp.cell]; rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem bodySchedule_preFinal_v_of_entry (c : Cfg) (idx : Nat)
    (st : AState)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hsinkM : c.sink < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M)
    (hstartR : st.regs rR =
      c.markSteps + st.regs rC * (c.bsSteps + 1))
    (h : FirstEntryInv c st) (hkmax : nextKey st ≤ productionKMax) :
    let current := bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)
    AddWide.wval (current.regs rVLo, current.regs rVHi) =
      AddWide.wval (st.regs rVLo, st.regs rVHi) := by
  have hready := firstStepReady_of_entry c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hR hsinkM h
  have hv := firstValues_of_entry c idx st hidxM hsieveM hsieve hmarkPos
    hmarkM hR hsinkM h
  exact bodySchedule_preFinal_v_production_ready c idx st
    (nextKey st) (nextDPos c st) (nextDNeg c st)
    (nextCeil c st) (nextFloor c st) (st.regs rC)
    hc hsteps hidxM hsieveM hsieve hmarkPos hmarkM h.steps_word hsinkM
    hperiodM hsegM h.regs_word h.arr_word h.round0 h.zero rfl
    h.cell_range hstartR hready hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    hv.2.2.2.2 h.key_pos hkmax h.delta_sum_word h.ceil_word

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem bodySchedule_production_latches_of_entry (c : Cfg) (idx : Nat)
    (st : AState)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hsinkM : c.sink < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M)
    (hstartR : st.regs rR =
      c.markSteps + st.regs rC * (c.bsSteps + 1))
    (h : FirstEntryInv c st) (hkmax : nextKey st ≤ productionKMax) :
    let after := bodySchedule c idx (c.bsSteps - 1) st
    after.regs rK = nextKey st ∧
      after.regs rDp = nextDPos c st ∧
      after.regs rDn = nextDNeg c st ∧ after.regs rZero = 0 := by
  have hready := firstStepReady_of_entry c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hR hsinkM h
  have hv := firstValues_of_entry c idx st hidxM hsieveM hsieve hmarkPos
    hmarkM hR hsinkM h
  exact bodySchedule_production_latches_ready c idx st
    (nextKey st) (nextDPos c st) (nextDNeg c st)
    (nextCeil c st) (nextFloor c st) (st.regs rC)
    hc hsteps hidxM hsieveM hsieve hmarkPos hmarkM h.steps_word hsinkM
    hperiodM hsegM h.regs_word h.arr_word h.round0 h.zero rfl
    h.cell_range hstartR hready hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    hv.2.2.2.2 h.key_pos hkmax h.delta_sum_word h.ceil_word

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem bodySchedule_production_of_entry (c : Cfg) (idx : Nat) (st : AState)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hsinkM : c.sink < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hWnext : st.regs rW + c.segLen < M)
    (hstartR : st.regs rR =
      c.markSteps + st.regs rC * (c.bsSteps + 1))
    (h : FirstEntryInv c st) (hkmax : nextKey st ≤ productionKMax)
    (haccFit :
      let current := bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)
      AddWide.wval (current.regs rVLo, current.regs rVHi) +
        (nextDPos c st + nextDNeg c st) *
          exactRoot c.wScale (nextKey st) < AddWide.B128) :
    OuterFullAccSpec c (nextKey st) (nextDPos c st) (nextDNeg c st)
        (nextCeil c st) (nextFloor c st)
        (exactRoot c.wScale (nextKey st))
        (nextDPos c st + nextDNeg c st)
        st (bodySchedule c idx (c.bsSteps - 1) st) ∧
      ProductionCellCursorSpec c (st.regs rC) (st.regs rR) (st.regs rW)
        (bodySchedule c idx (c.bsSteps - 1) st) := by
  have hready := firstStepReady_of_entry c idx st hidxM hsieveM hsieve
    hmarkPos hmarkM hR hsinkM h
  have hv := firstValues_of_entry c idx st hidxM hsieveM hsieve hmarkPos
    hmarkM hR hsinkM h
  exact bodySchedule_production_ready c idx st
    (nextKey st) (nextDPos c st) (nextDNeg c st)
    (nextCeil c st) (nextFloor c st) (st.regs rC)
    hc hsteps hidxM hsieveM hsieve hmarkPos hmarkM h.steps_word hsinkM
    hperiodM hsegM hWnext h.regs_word h.arr_word h.round0 h.zero rfl
    h.cell_range hstartR hready hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    hv.2.2.2.2 h.key_pos hkmax h.delta_sum_word h.ceil_word haccFit

end LeanCompCert.Ports.CDEMAbelSourceReady
