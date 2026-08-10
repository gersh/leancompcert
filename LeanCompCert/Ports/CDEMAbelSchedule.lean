import LeanCompCert.Ports.CDEMAbelBody

namespace LeanCompCert.Ports.CDEMAbelSchedule

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

def forwardIter (w k : Nat) : Nat → Bracket → Bracket
  | 0, p => p
  | n + 1, p => step w k (forwardIter w k n p)

theorem iter_step_comm (w k n : Nat) (p : Bracket) :
    step w k (iter w k n p) = iter w k n (step w k p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      change step w k (iter w k n (step w k p)) =
        iter w k n (step w k (step w k p))
      exact ih (step w k p)

theorem forwardIter_eq_iter (w k n : Nat) (p : Bracket) :
    forwardIter w k n p = iter w k n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [forwardIter, ih, iter_step_comm]
      rfl

theorem forward_initial_budget_exact (w k : Nat) (hw : 0 < w)
    (hk : 0 < k) :
    forwardIter w k (CDEMAbelScan.bsBudget w) (initial w k) =
      ⟨exactRoot w k, exactRoot w k⟩ := by
  rw [forwardIter_eq_iter]
  exact initial_budget_exact w k hw hk

theorem production_forward_roundFit (c : Cfg)
    (hc : c.wScale = productionW) (k n : Nat)
    (hk : 0 < k) (hkmax : k ≤ productionKMax) :
    RoundFit c k (forwardIter c.wScale k n (initial c.wScale k)) := by
  rw [forwardIter_eq_iter]
  exact production_iter_roundFit c hc k n hk hkmax

theorem production_forward_quotient_guard (c : Cfg)
    (hc : c.wScale = productionW) (k n : Nat)
    (hk : 0 < k) (hkmax : k ≤ productionKMax) :
    c.wScale /
        midpoint (forwardIter c.wScale k n (initial c.wScale k)) ≤
      2147483648 := by
  rw [forwardIter_eq_iter]
  exact production_iter_quotient_guard c hc k n hk hkmax

theorem production_forward_bracket (c : Cfg)
    (hc : c.wScale = productionW) (k n : Nat) (hk : 0 < k) :
    let p := forwardIter c.wScale k n (initial c.wScale k)
    p.lo ≤ p.hi ∧ p.hi < M := by
  have hc0 := initial_contains productionW k (by decide) hk
  have hcn := iter_contains productionW k hk n (initial productionW k) hc0
  have hsub := iter_sub_initial productionW k n
    (initial productionW k) hk hc0
  have hsqrt : 0 < Nat.sqrt k := by
    have hs := Nat.lt_succ_sqrt k
    by_cases hz : Nat.sqrt k = 0
    · rw [hz] at hs
      simp at hs
      omega
    · exact Nat.pos_of_ne_zero hz
  have hinitHi : (initial productionW k).hi ≤ productionW := by
    change ceilDiv productionW (Nat.sqrt k) ≤ productionW
    exact ceilDiv_le_self productionW (Nat.sqrt k) (by decide) hsqrt
  have hp :
      (forwardIter productionW k n (initial productionW k)).lo ≤
          (forwardIter productionW k n (initial productionW k)).hi ∧
        (forwardIter productionW k n (initial productionW k)).hi < M := by
    rw [forwardIter_eq_iter]
    constructor
    · unfold Bracket.Contains at hcn
      omega
    · exact Nat.lt_of_le_of_lt (Nat.le_trans hsub.2 hinitHi) (by decide)
  simpa only [hc] using hp

theorem final_step_exact (c : Cfg) (k : Nat)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hw : 0 < c.wScale) (hk : 0 < k) :
    step c.wScale k
        (forwardIter c.wScale k (c.bsSteps - 1) (initial c.wScale k)) =
      ⟨exactRoot c.wScale k, exactRoot c.wScale k⟩ := by
  have hbpos : 0 < CDEMAbelScan.bsBudget c.wScale := by
    simp [CDEMAbelScan.bsBudget]
  have hspos : 0 < c.bsSteps := by rw [hsteps]; exact hbpos
  change forwardIter c.wScale k ((c.bsSteps - 1) + 1)
    (initial c.wScale k) = _
  rw [Nat.sub_add_cancel hspos, hsteps]
  exact forward_initial_budget_exact c.wScale k hw hk

def accIter (c : Cfg) (idx : Nat) : Nat → AState → AState
  | 0, st => st
  | n + 1, st => arun idx (accIter c idx n st) c.accBody

structure MiddleTraceSpec (c : Cfg) (k : Nat) (p : Bracket)
    (gate n : Nat) (before after : AState) : Prop where
  arr : after.arr = before.arr
  low : after.regs rSl = (forwardIter c.wScale k n p).lo
  high : after.regs rSh = (forwardIter c.wScale k n p).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + n * gate
  cell : after.regs rC = before.regs rC

theorem accIter_middle_contracts (c : Cfg) (idx n : Nat) (st : AState)
    (k gate : Nat) (p : Bracket)
    (hlo : st.regs rSl = p.lo) (hhi : st.regs rSh = p.hi)
    (hcontract : ∀ i, i < n →
      MiddleBodySpec c k (forwardIter c.wScale k i p)
        (accIter c idx i st) (accIter c idx (i + 1) st))
    (hgate : ∀ i, i < n → (accIter c idx i st).regs 43 = gate) :
    MiddleTraceSpec c k p gate n st (accIter c idx n st) := by
  induction n with
  | zero =>
      exact
        { arr := rfl
          low := hlo
          high := hhi
          uPos := rfl
          uNeg := rfl
          viol := rfl
          vDiv := rfl
          vBisect := rfl
          v := rfl
          round := by
            change st.regs rKr = st.regs rKr + 0 * gate
            simp
          cell := rfl }
  | succ n ih =>
      have hpre : ∀ i, i < n →
          MiddleBodySpec c k (forwardIter c.wScale k i p)
            (accIter c idx i st) (accIter c idx (i + 1) st) :=
        fun i hi => hcontract i (by omega)
      have hgpre : ∀ i, i < n → (accIter c idx i st).regs 43 = gate :=
        fun i hi => hgate i (by omega)
      have hi := ih hpre hgpre
      have hs := hcontract n (by omega)
      have hg := hgate n (by omega)
      exact
        { arr := hs.arr.trans hi.arr
          low := hs.low
          high := hs.high
          uPos := hs.uPos.trans hi.uPos
          uNeg := hs.uNeg.trans hi.uNeg
          viol := hs.viol.trans hi.viol
          vDiv := hs.vDiv.trans hi.vDiv
          vBisect := hs.vBisect.trans hi.vBisect
          v := hs.v.trans hi.v
          round := by
            rw [hs.round, hi.round, hg, Nat.succ_mul]
            omega
          cell := hs.cell.trans hi.cell }

structure MiddleStepReady (c : Cfg) (k : Nat) (p : Bracket)
    (st : AState) : Prop where
  key : st.regs rK = k
  low : st.regs rSl = p.lo
  high : st.regs rSh = p.hi
  round_ne_zero : st.regs rKr ≠ 0
  round_ne_last : st.regs rKr ≠ c.bsSteps
  gate : st.regs 43 = 1
  zero : st.regs rZero = 0
  steps_word : c.bsSteps < M
  sink_word : c.sink < M
  sink_zero : st.arr c.sink = 0
  regs_word : ∀ j, st.regs j < M
  arr_word : ∀ j, st.arr j < M
  key_pos : 0 < st.regs rK
  scale_word : c.wScale < M
  delta_sum_word : st.regs rDp + st.regs rDn < M
  ceil_word : c.wScale - 1 + st.regs rK < M
  bracket_order : p.lo ≤ p.hi
  high_word : p.hi < M
  round_fit : RoundFit c k p
  quotient_guard : c.wScale / midpoint p ≤ 2147483648
  round_counter_word : st.regs rKr + st.regs 43 < M

theorem accBody_middle_of_ready (c : Cfg) (idx : Nat) (st : AState)
    (k : Nat) (p : Bracket) (h : MiddleStepReady c k p st) :
    MiddleBodySpec c k p st (arun idx st c.accBody) := by
  have hr := accBody_middle_run c idx st h.round_ne_zero h.round_ne_last
    h.gate h.zero h.steps_word h.sink_word h.sink_zero h.regs_word
    h.arr_word h.key_pos h.scale_word h.delta_sum_word h.ceil_word
    (by simpa [h.low, h.high] using h.bracket_order)
    (by simpa [h.high] using h.high_word)
    (by simpa [h.key, h.low, h.high] using h.round_fit)
    (by simpa [h.low, h.high] using h.quotient_guard)
    h.round_counter_word
  simpa [h.key, h.low, h.high] using hr

structure ProductionMiddleCore (c : Cfg) (k dp dn n cell : Nat)
    (st : AState) : Prop where
  key : st.regs rK = k
  dPos : st.regs rDp = dp
  dNeg : st.regs rDn = dn
  gate : st.regs 43 = 1
  zero : st.regs rZero = 0
  round : st.regs rKr = n + 1
  cell : st.regs rC = cell
  sink_zero : st.arr c.sink = 0
  regs_word : ∀ j, st.regs j < M
  arr_word : ∀ j, st.arr j < M

theorem productionMiddleCore_step (c : Cfg) (idx : Nat) (st : AState)
    (k dp dn n cell : Nat) (p : Bracket)
    (hcore : ProductionMiddleCore c k dp dn n cell st)
    (hready : MiddleStepReady c k p st) :
    ProductionMiddleCore c k dp dn (n + 1) cell
      (arun idx st c.accBody) := by
  have hh := accHead_middle_run c idx st hready.round_ne_zero
    hready.round_ne_last hready.gate hready.zero hready.steps_word
    hready.sink_word hready.sink_zero hready.regs_word hready.arr_word
    hready.key_pos hready.scale_word hready.delta_sum_word hready.ceil_word
  have hl :
      (arun idx st c.accBody).regs rK = st.regs rK ∧
        (arun idx st c.accBody).regs rDp = st.regs rDp ∧
        (arun idx st c.accBody).regs rDn = st.regs rDn ∧
        (arun idx st c.accBody).regs 43 = st.regs 43 ∧
        (arun idx st c.accBody).regs rZero = st.regs rZero := by
    rw [arun_accBody_eq_parts]
    exact accBody_middle_latch_of_head c idx st hh hready.regs_word
      hready.arr_word
  have hs := accBody_middle_of_ready c idx st k p hready
  have hw := arun_word idx c.accBody st hready.regs_word hready.arr_word
  exact
    { key := by rw [hl.1, hcore.key]
      dPos := by rw [hl.2.1, hcore.dPos]
      dNeg := by rw [hl.2.2.1, hcore.dNeg]
      gate := by rw [hl.2.2.2.1, hcore.gate]
      zero := by rw [hl.2.2.2.2, hcore.zero]
      round := by rw [hs.round, hcore.round, hcore.gate]
      cell := by rw [hs.cell, hcore.cell]
      sink_zero := by rw [hs.arr, hcore.sink_zero]
      regs_word := hw.1
      arr_word := hw.2 }

theorem production_middle_ready_of_core (c : Cfg)
    (hc : c.wScale = productionW) (k dp dn n cell : Nat)
    (first current : AState)
    (hcore : ProductionMiddleCore c k dp dn n cell current)
    (htrace : MiddleTraceSpec c k (initial c.wScale k) 1 n first current)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hround : n + 1 < c.bsSteps) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hsum : dp + dn < M)
    (hceil : c.wScale - 1 + k < M) :
    MiddleStepReady c k
      (forwardIter c.wScale k n (initial c.wScale k)) current := by
  have hb := production_forward_bracket c hc k n hk
  dsimp only at hb
  exact
    { key := hcore.key
      low := htrace.low
      high := htrace.high
      round_ne_zero := by rw [hcore.round]; omega
      round_ne_last := by rw [hcore.round]; omega
      gate := hcore.gate
      zero := hcore.zero
      steps_word := hbsM
      sink_word := hsinkM
      sink_zero := hcore.sink_zero
      regs_word := hcore.regs_word
      arr_word := hcore.arr_word
      key_pos := by rw [hcore.key]; exact hk
      scale_word := by rw [hc]; decide
      delta_sum_word := by rw [hcore.dPos, hcore.dNeg]; exact hsum
      ceil_word := by rw [hcore.key]; exact hceil
      bracket_order := hb.1
      high_word := hb.2
      round_fit := production_forward_roundFit c hc k n hk hkmax
      quotient_guard := production_forward_quotient_guard c hc k n hk hkmax
      round_counter_word := by
        rw [hcore.round, hcore.gate]
        omega }

theorem accIter_middle_ready (c : Cfg) (idx n : Nat) (st : AState)
    (k : Nat) (p : Bracket) (hlo : st.regs rSl = p.lo)
    (hhi : st.regs rSh = p.hi)
    (hready : ∀ i, i < n →
      MiddleStepReady c k (forwardIter c.wScale k i p)
        (accIter c idx i st)) :
    MiddleTraceSpec c k p 1 n st (accIter c idx n st) := by
  apply accIter_middle_contracts c idx n st k 1 p hlo hhi
  · intro i hi
    simpa [accIter] using accBody_middle_of_ready c idx
      (accIter c idx i st) k (forwardIter c.wScale k i p) (hready i hi)
  · intro i hi
    exact (hready i hi).gate

theorem accIter_production_ready (c : Cfg) (idx count : Nat)
    (first : AState) (k dp dn cell : Nat)
    (hc : c.wScale = productionW) (hk : 0 < k)
    (hkmax : k ≤ productionKMax) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hsum : dp + dn < M)
    (hceil : c.wScale - 1 + k < M)
    (hlo : first.regs rSl = (initial c.wScale k).lo)
    (hhi : first.regs rSh = (initial c.wScale k).hi)
    (hcore0 : ProductionMiddleCore c k dp dn 0 cell first)
    (hcount : count ≤ c.bsSteps - 1) :
    (∀ i, i < count →
      MiddleStepReady c k
        (forwardIter c.wScale k i (initial c.wScale k))
        (accIter c idx i first)) ∧
      ProductionMiddleCore c k dp dn count cell
        (accIter c idx count first) := by
  induction count with
  | zero =>
      exact ⟨fun _ hi => by omega, hcore0⟩
  | succ n ih =>
      have hncount : n ≤ c.bsSteps - 1 := by omega
      have hprev := ih hncount
      have htrace := accIter_middle_ready c idx n first k
        (initial c.wScale k) hlo hhi hprev.1
      have hnround : n + 1 < c.bsSteps := by omega
      have hnready := production_middle_ready_of_core c hc k dp dn n cell
        first (accIter c idx n first) hprev.2 htrace hk hkmax hnround
        hbsM hsinkM hsum hceil
      have hnext := productionMiddleCore_step c idx
        (accIter c idx n first) k dp dn n cell
        (forwardIter c.wScale k n (initial c.wScale k)) hprev.2 hnready
      constructor
      · intro i hi
        by_cases hin : i < n
        · exact hprev.1 i hin
        · have hieq : i = n := by omega
          simpa [hieq] using hnready
      · simpa [accIter] using hnext

theorem production_core_of_first (c : Cfg) (idx : Nat) (st : AState)
    (k dp dn ceil floor : Nat)
    (hf : FirstBodySpec c k dp dn ceil floor st (arun idx st c.accBody))
    (hround : st.regs rKr = 0) (hgate : st.regs 43 = 1)
    (hzero : st.regs rZero = 0) (hcell : st.regs rC < c.segLen)
    (hsink0 : st.arr c.sink = 0) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) :
    ProductionMiddleCore c k dp dn 0 (st.regs rC)
      (arun idx st c.accBody) := by
  have hw := arun_word idx c.accBody st hword harrword
  have hne : c.sink ≠ st.regs rC + c.winBase := by
    unfold Cfg.sink
    omega
  exact
    { key := hf.key
      dPos := hf.dPos
      dNeg := hf.dNeg
      gate := by rw [hf.gate, hgate]
      zero := by rw [hf.zero, hzero]
      round := by rw [hf.round, hround, hgate]
      cell := hf.cell
      sink_zero := by rw [hf.arr]; simp [hne, hsink0]
      regs_word := hw.1
      arr_word := hw.2 }

theorem accBody_final_of_production_core (c : Cfg) (idx : Nat)
    (current first : AState) (k dp dn cell : Nat)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsum : dp + dn < M) (hceil : c.wScale - 1 + k < M)
    (hcore : ProductionMiddleCore c k dp dn (c.bsSteps - 1) cell current)
    (htrace : MiddleTraceSpec c k (initial c.wScale k) 1
      (c.bsSteps - 1) first current)
    (hcellFit : cell + 1 < M)
    (haccFit : AddWide.wval (current.regs rVLo, current.regs rVHi) +
      (dp + dn) * exactRoot c.wScale k < AddWide.B128) :
    FinalBodySpec (exactRoot c.wScale k) (dp + dn) current
      (arun idx current c.accBody) := by
  have hbsPos : 0 < c.bsSteps := by
    rw [hsteps]
    simp [CDEMAbelScan.bsBudget]
  have hround : current.regs rKr = c.bsSteps := by
    rw [hcore.round, Nat.sub_add_cancel hbsPos]
  have hb := production_forward_bracket c hc k (c.bsSteps - 1) hk
  dsimp only at hb
  have hfit := production_forward_roundFit c hc k (c.bsSteps - 1) hk hkmax
  have hquot := production_forward_quotient_guard c hc k
    (c.bsSteps - 1) hk hkmax
  have hlast := final_step_exact c k hsteps (by rw [hc]; decide) hk
  have hr := accBody_final_run c idx current (exactRoot c.wScale k)
    hround hbsPos hcore.gate hcore.zero hbsM hsinkM hcore.sink_zero
    hcore.regs_word hcore.arr_word
    (by rw [hcore.key]; exact hk)
    (by rw [hc]; decide)
    (by rw [hcore.dPos, hcore.dNeg]; exact hsum)
    (by rw [hcore.key]; exact hceil)
    (by simpa [htrace.low, htrace.high] using hb.1)
    (by simpa [htrace.high] using hb.2)
    (by simpa [hcore.key, htrace.low, htrace.high] using hfit)
    (by simpa [htrace.low, htrace.high] using hquot)
    (by simpa [hcore.key, htrace.low, htrace.high] using hlast)
    (by rw [hcore.cell]; exact hcellFit)
    (by simpa [hcore.dPos, hcore.dNeg] using haccFit)
  simpa [hcore.dPos, hcore.dNeg] using hr

def accSchedule (c : Cfg) (idx middleCount : Nat) (st : AState) : AState :=
  let first := arun idx st c.accBody
  let middle := accIter c idx middleCount first
  arun idx middle c.accBody

structure FullAccSpec (c : Cfg) (k dp dn ceil floor root d : Nat)
    (before after : AState) : Prop where
  arr : after.arr = fun j =>
    if j = before.regs rC + c.winBase then 0 else before.arr j
  low : after.regs rSl = root
  high : after.regs rSh = root
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi) + dp * ceil
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi) + dn * floor
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * root
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

theorem accSchedule_of_contracts (c : Cfg) (idx middleCount : Nat)
    (st : AState) (k dp dn ceil floor root d : Nat)
    (hf : FirstBodySpec c k dp dn ceil floor st (arun idx st c.accBody))
    (hm : MiddleTraceSpec c k (initial c.wScale k) 1 middleCount
      (arun idx st c.accBody)
      (accIter c idx middleCount (arun idx st c.accBody)))
    (hl : FinalBodySpec root d
      (accIter c idx middleCount (arun idx st c.accBody))
      (accSchedule c idx middleCount st)) :
    FullAccSpec c k dp dn ceil floor root d st
      (accSchedule c idx middleCount st) := by
  exact
    { arr := hl.arr.trans (hm.arr.trans hf.arr)
      low := hl.low
      high := hl.high
      uPos := hl.uPos.trans (hm.uPos.trans hf.uPos)
      uNeg := hl.uNeg.trans (hm.uNeg.trans hf.uNeg)
      viol := hl.viol.trans (hm.viol.trans hf.viol)
      vDiv := hl.vDiv.trans (hm.vDiv.trans hf.vDiv)
      vBisect := hl.vBisect.trans (hm.vBisect.trans hf.vBisect)
      v := by rw [hl.v, hm.v, hf.v]
      round := hl.round
      cell := by rw [hl.cell, hm.cell, hf.cell] }

theorem accSchedule_from_ready_middle (c : Cfg) (idx middleCount : Nat)
    (st : AState) (k dp dn ceil floor root d : Nat)
    (hf : FirstBodySpec c k dp dn ceil floor st (arun idx st c.accBody))
    (hready : ∀ i, i < middleCount →
      MiddleStepReady c k
        (forwardIter c.wScale k i (initial c.wScale k))
        (accIter c idx i (arun idx st c.accBody)))
    (hl : FinalBodySpec root d
      (accIter c idx middleCount (arun idx st c.accBody))
      (accSchedule c idx middleCount st)) :
    FullAccSpec c k dp dn ceil floor root d st
      (accSchedule c idx middleCount st) := by
  have hm := accIter_middle_ready c idx middleCount (arun idx st c.accBody)
    k (initial c.wScale k) hf.low hf.high hready
  exact accSchedule_of_contracts c idx middleCount st k dp dn ceil floor
    root d hf hm hl

theorem accSchedule_production (c : Cfg) (idx : Nat) (st : AState)
    (k dp dn ceil floor : Nat)
    (hc : c.wScale = productionW)
    (hsteps : c.bsSteps = CDEMAbelScan.bsBudget c.wScale)
    (hk : 0 < k) (hkmax : k ≤ productionKMax)
    (hbsM : c.bsSteps < M) (hsinkM : c.sink < M)
    (hsum : dp + dn < M) (hceil : c.wScale - 1 + k < M)
    (hf : FirstBodySpec c k dp dn ceil floor st (arun idx st c.accBody))
    (hround : st.regs rKr = 0) (hgate : st.regs 43 = 1)
    (hzero : st.regs rZero = 0) (hcell : st.regs rC < c.segLen)
    (hsink0 : st.arr c.sink = 0) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hcellFit : st.regs rC + 1 < M)
    (haccFit :
      let current := accIter c idx (c.bsSteps - 1) (arun idx st c.accBody)
      AddWide.wval (current.regs rVLo, current.regs rVHi) +
        (dp + dn) * exactRoot c.wScale k < AddWide.B128) :
    FullAccSpec c k dp dn ceil floor (exactRoot c.wScale k) (dp + dn) st
      (accSchedule c idx (c.bsSteps - 1) st) := by
  let first := arun idx st c.accBody
  let current := accIter c idx (c.bsSteps - 1) first
  have hcore0 : ProductionMiddleCore c k dp dn 0 (st.regs rC) first := by
    simpa [first] using production_core_of_first c idx st k dp dn ceil floor
      hf hround hgate hzero hcell hsink0 hword harrword
  have hprod := accIter_production_ready c idx (c.bsSteps - 1) first
    k dp dn (st.regs rC) hc hk hkmax hbsM hsinkM hsum hceil
    (by simpa [first] using hf.low) (by simpa [first] using hf.high)
    hcore0 (Nat.le_refl _)
  have htrace := accIter_middle_ready c idx (c.bsSteps - 1) first k
    (initial c.wScale k) (by simpa [first] using hf.low)
    (by simpa [first] using hf.high) hprod.1
  have hl0 := accBody_final_of_production_core c idx current first k dp dn
    (st.regs rC) hc hsteps hk hkmax hbsM hsinkM hsum hceil
    (by simpa [current] using hprod.2)
    (by simpa [current] using htrace) hcellFit
    (by simpa [current] using haccFit)
  have hl : FinalBodySpec (exactRoot c.wScale k) (dp + dn) current
      (accSchedule c idx (c.bsSteps - 1) st) := by
    simpa [accSchedule, first, current] using hl0
  exact accSchedule_of_contracts c idx (c.bsSteps - 1) st k dp dn ceil
    floor (exactRoot c.wScale k) (dp + dn) hf htrace hl

end LeanCompCert.Ports.CDEMAbelSchedule
