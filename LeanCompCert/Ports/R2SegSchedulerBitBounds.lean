import LeanCompCert.Ports.R2SegMarkingRoundPosition
import LeanCompCert.Ports.R2SegLogRoundCounter
import LeanCompCert.Verified.ArrayAudit

/-!
# Literal scheduler-bit bounds for `R₂*`

This leaf records bounds which hold for the emitted control circuit even on
an arbitrary input state.  In particular the two finish conditions are not
assumed disjoint: the literal finish register is bounded by two.  Reachable
source states later sharpen it to a bit, while the bound by two is already
enough to telescope the failure counters without modular wrap.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 10000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (arun_lift)
open LeanCompCert.Verified.InstrBlock

/-- The literal phase selector always writes a bit to the log-phase gate. -/
theorem markPhaseBody_log_gate_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    (arun k s (markPhaseBody c)).regs 15 ≤ 1 := by
  simp only [markPhaseBody, arun_lift]
  by_cases hlt : s.regs 5 <
      (c.markSteps + c.segLen) % 18446744073709551616
  · simp [markPhaseInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rR, hlt, M]
  · simp [markPhaseInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rR, hlt, M]

/-- The remaining marking instructions do not alter the phase gate. -/
theorem markBody_log_gate_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    (arun k s c.markBody).regs 15 ≤ 1 := by
  let phased := arun k s (markPhaseBody c)
  have hphase := markPhaseBody_log_gate_le_one c k s
  have hframe :
      (arun k phased (markAfterPhaseBody c)).regs 15 = phased.regs 15 :=
    arun_frame k 15 (markAfterPhaseBody c) (by rfl) phased
  rw [markBody_eq_phase_stages, arun_append, hframe]
  exact hphase

/-- The classifier does not alter the phase gate installed by `markBody`. -/
theorem classBody_log_gate_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 15 ≤ 1) :
    (arun k s c.classBody).regs 15 ≤ 1 := by
  rw [arun_frame k 15 c.classBody (by rfl) s]
  exact hphase

/-- Literal prefix ending at the assignment of the live-entry gate. -/
def logThroughLiveBody (c : R2Cfg) : List AInstr := c.logBody.take 7

/-- A bit-valued phase gate makes the emitted live-entry gate a bit too. -/
theorem logThroughLiveBody_live_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 15 ≤ 1) :
    (arun k s (logThroughLiveBody c)).regs 206 ≤ 1 := by
  have hphaseCases : s.regs 15 = 0 ∨ s.regs 15 = 1 := by omega
  rcases hphaseCases with hzero | hone
  · simp [logThroughLiveBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp, hzero,
      rEc, rWc, M]
  · simp [logThroughLiveBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp, hone,
      rEc, rWc, M]
    split <;> decide

/-- Literal log prefix ending immediately before the round-counter island. -/
def logBeforeRoundCounterBody (c : R2Cfg) : List AInstr :=
  c.logBody.take 52

def logAfterLiveBeforeRoundCounterBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 7).take 45

theorem logBeforeRoundCounterBody_eq_stages (c : R2Cfg) :
    logBeforeRoundCounterBody c = logThroughLiveBody c ++
      logAfterLiveBeforeRoundCounterBody c := by
  rfl

/-- The arithmetic between the live gate and round counter frames `live`. -/
theorem logBeforeRoundCounterBody_live_le_one
    (c : R2Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 15 ≤ 1) :
    (arun k s (logBeforeRoundCounterBody c)).regs 206 ≤ 1 := by
  let live := arun k s (logThroughLiveBody c)
  have hlive := logThroughLiveBody_live_le_one c k s hphase
  have hframe :
      (arun k live (logAfterLiveBeforeRoundCounterBody c)).regs 206 =
        live.regs 206 :=
    arun_frame k 206 (logAfterLiveBeforeRoundCounterBody c) (by rfl) live
  rw [logBeforeRoundCounterBody_eq_stages, arun_append, hframe]
  exact hlive

/-- Even without the source-mode invariant, the two literal finish
conditions can sum to at most two and the live gate is a bit. -/
theorem logRoundCounterBody_finish_le_two
    (S k : Nat) (s : AState) (hlive : s.regs 206 ≤ 1) :
    (arun k s (logRoundCounterBody S)).regs 247 ≤ 2 := by
  have hliveCases : s.regs 206 = 0 ∨ s.regs 206 = 1 := by omega
  rcases hliveCases with hzero | hone
  · rw [logRoundCounterBody, arun_lift]
    simp [logRoundCounterInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hzero, rK, rPl, M]
  · rw [logRoundCounterBody, arun_lift]
    simp [logRoundCounterInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hone, rK, rPl, M]
    split <;> split <;> decide

/-- Literal arithmetic between the counter island and the four instructions
which compute the gap-failure payload. -/
def logAfterRoundCounterBeforeGapComputeBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 61).take 36

def logBeforeGapComputeBody (c : R2Cfg) : List AInstr :=
  c.logBody.take 97

def logGapComputeBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 97).take 4

def logBeforeGapCommitExactBody (c : R2Cfg) : List AInstr :=
  c.logBody.take 101

theorem logBeforeGapComputeBody_eq_stages (c : R2Cfg) :
    logBeforeGapComputeBody c =
      logBeforeRoundCounterBody c ++ logRoundCounterBody c.sc ++
        logAfterRoundCounterBeforeGapComputeBody c := by
  rfl

theorem logBeforeGapCommitExactBody_eq_stages (c : R2Cfg) :
    logBeforeGapCommitExactBody c =
      logBeforeGapComputeBody c ++ logGapComputeBody c := by
  rfl

/-- The literal log prefix reaches the gap computation with a finish value
at most two, even for an inconsistent incoming scheduler state. -/
theorem logBeforeGapComputeBody_finish_le_two
    (c : R2Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 15 ≤ 1) :
    (arun k s (logBeforeGapComputeBody c)).regs 247 ≤ 2 := by
  let beforeCounter := arun k s (logBeforeRoundCounterBody c)
  have hlive := logBeforeRoundCounterBody_live_le_one c k s hphase
  let counted := arun k beforeCounter (logRoundCounterBody c.sc)
  have hfin := logRoundCounterBody_finish_le_two c.sc k beforeCounter hlive
  have hframe :
      (arun k counted
        (logAfterRoundCounterBeforeGapComputeBody c)).regs 247 =
          counted.regs 247 :=
    arun_frame k 247 (logAfterRoundCounterBeforeGapComputeBody c)
      (by rfl) counted
  rw [logBeforeGapComputeBody_eq_stages, arun_append, arun_append, hframe]
  exact hfin

/-- The gap payload is `(not gapFits) * finish`; hence the conservative
two-valued scheduler bound also bounds the literal payload by two. -/
theorem logGapComputeBody_bit_le_two
    (c : R2Cfg) (k : Nat) (s : AState)
    (hfin : s.regs 247 ≤ 2) :
    (arun k s (logGapComputeBody c)).regs 289 ≤ 2 := by
  have hfinCases : s.regs 247 = 0 ∨ s.regs 247 = 1 ∨
      s.regs 247 = 2 := by omega
  rcases hfinCases with hzero | hone | htwo
  · simp [logGapComputeBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hzero, rNe, rPrev, M]
  · simp [logGapComputeBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hone, rNe, rPrev, M]
    split <;> decide
  · simp [logGapComputeBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      htwo, rNe, rPrev, M]
    split <;> decide

/-- On a finished source event with ordered word-sized endpoints, zero of the
literal gap payload is exactly the intended sixteen-bit gap condition. -/
theorem logGapComputeBody_bit_eq_zero_iff
    (c : R2Cfg) (k : Nat) (s : AState) (n prev : Nat)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hfin : s.regs 247 = 1) (hprevn : prev < n) (hnM : n < M) :
    (arun k s (logGapComputeBody c)).regs 289 = 0 ↔
      n - prev < 65536 := by
  have hsub : denoteOp .sub n prev = some (n - prev) :=
    LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (Nat.le_of_lt hprevn) hnM
  have hgapM : n - prev < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le n prev) hnM
  have h65536M : 65536 < M := by decide
  simp_all [logGapComputeBody, R2Cfg.logBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    rNe, rPrev, Nat.mod_eq_of_lt]
  by_cases hgap : n - prev < 65536
  · simp [hgap, M]
  · simp [hgap, M]

/-- Full emitted body prefix immediately before the two gap-counter writes. -/
def bodyBeforeGapCompute (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ logBeforeGapComputeBody c

def beforeGapCompute (c : R2Cfg) (k : Nat) (s : AState) : AState :=
  arun k s (bodyBeforeGapCompute c)

def bodyBeforeGapCommit (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ logBeforeGapCommitExactBody c

def beforeGapCommit (c : R2Cfg) (k : Nat) (s : AState) : AState :=
  arun k s (bodyBeforeGapCommit c)

def bodyGapBit (c : R2Cfg) (k : Nat) (s : AState) : Nat :=
  (beforeGapCommit c k s).regs 289

theorem beforeGapCommit_eq_compute (c : R2Cfg) (k : Nat) (s : AState) :
    beforeGapCommit c k s =
      arun k (beforeGapCompute c k s) (logGapComputeBody c) := by
  simp only [beforeGapCommit, beforeGapCompute, bodyBeforeGapCommit,
    bodyBeforeGapCompute, logBeforeGapCommitExactBody_eq_stages,
    arun_append]

/-- Every literal scheduled body has a gap payload bounded by two.  No
reachable-state or source-mode premise is used here. -/
theorem bodyGapBit_le_two (c : R2Cfg) (k : Nat) (s : AState) :
    bodyGapBit c k s ≤ 2 := by
  let marked := arun k s c.markBody
  have hmark := markBody_log_gate_le_one c k s
  let classified := arun k marked c.classBody
  have hclass := classBody_log_gate_le_one c k marked hmark
  let beforeCompute := arun k classified (logBeforeGapComputeBody c)
  have hfin := logBeforeGapComputeBody_finish_le_two c k classified hclass
  have hbit := logGapComputeBody_bit_le_two c k beforeCompute hfin
  simpa only [bodyGapBit, beforeGapCommit, bodyBeforeGapCommit,
    logBeforeGapCommitExactBody_eq_stages, arun_append, marked,
    classified, beforeCompute] using hbit

/-! ## Exact dedicated-counter increment -/

def logGapCounterCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 101).take 2

def bodyAfterGapCounterCommit (c : R2Cfg) : List AInstr :=
  c.logBody.drop 103 ++ c.tailBody

theorem body_eq_gap_counter_stages (c : R2Cfg) :
    c.body = bodyBeforeGapCommit c ++ logGapCounterCommitBody c ++
      bodyAfterGapCounterCommit c := by
  rfl

/-- The two emitted writes add the same payload first to the aggregate and
then to the dedicated gap counter. -/
theorem logGapCounterCommitBody_rvgap_run
    (c : R2Cfg) (k : Nat) (s : AState) (bit gap : Nat)
    (hbit : s.regs 289 = bit) (hgap : s.regs rVGap = gap)
    (hroom : gap + bit < M) :
    (arun k s (logGapCounterCommitBody c)).regs rVGap = gap + bit := by
  have hgap' : s.regs 356 = gap := by simpa only [rVGap] using hgap
  simp [logGapCounterCommitBody, R2Cfg.logBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    hbit, hgap', rViol, rVGap, Nat.mod_eq_of_lt hroom]

/-- One complete emitted body adds its literal gap payload exactly whenever
the conservative two-unit margin is available. -/
theorem body_rvgap_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hroom : s.regs rVGap + 2 < M) :
    (arun k s c.body).regs rVGap =
      s.regs rVGap + bodyGapBit c k s := by
  let pre := beforeGapCommit c k s
  let bit := bodyGapBit c k s
  have hbitLe : bit ≤ 2 := bodyGapBit_le_two c k s
  have hpreGap : pre.regs rVGap = s.regs rVGap :=
    arun_frame k rVGap (bodyBeforeGapCommit c) (by rfl) s
  have hbitEq : pre.regs 289 = bit := rfl
  have hbitRoom : s.regs rVGap + bit < M := by omega
  let committed := arun k pre (logGapCounterCommitBody c)
  have hcommit := logGapCounterCommitBody_rvgap_run c k pre bit
    (s.regs rVGap) hbitEq hpreGap hbitRoom
  have hsuffix :
      (arun k committed (bodyAfterGapCounterCommit c)).regs rVGap =
        committed.regs rVGap :=
    arun_frame k rVGap (bodyAfterGapCounterCommit c) (by rfl) committed
  rw [body_eq_gap_counter_stages, arun_append, arun_append]
  exact hsuffix.trans hcommit

/-! ## Size-independent telescope -/

/-- Across any symbolic list of scheduled bodies, the dedicated gap counter
is monotone and grows by at most two per body. -/
theorem foldl_body_rvgap_bounds
    (c : R2Cfg) (indices : List Nat) (s : AState)
    (hword : WordState s)
    (hroom : s.regs rVGap + 2 * indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVGap ≤ out.regs rVGap ∧
      out.regs rVGap ≤ s.regs rVGap + 2 * indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      let bit := bodyGapBit c k s
      have hbit : bit ≤ 2 := bodyGapBit_le_two c k s
      have hfirstRoom : s.regs rVGap + 2 < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_rvgap_increment c k s hfirstRoom
      change (arun k s c.body).regs rVGap = s.regs rVGap + bit at hfirst
      have hnextWord : WordState (arun k s c.body) :=
        arun_word k c.body s hword.1 hword.2
      have htailRoom :
          (arun k s c.body).regs rVGap + 2 * ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) hnextWord htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVGap ≤ s.regs rVGap + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVGap := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVGap
              ≤ (arun k s c.body).regs rVGap + 2 * ks.length := htail.2
          _ = s.regs rVGap + bit + 2 * ks.length := by rw [hfirst]
          _ ≤ s.regs rVGap + 2 * (ks.length + 1) := by omega

/-- A terminal zero dedicated counter makes every earlier emitted gap
payload zero.  The production range remains a symbolic fold. -/
theorem every_bodyGapBit_zero_of_fold_zero
    (c : R2Cfg) (entry : AState) (N : Nat)
    (hword : WordState entry) (hentry : entry.regs rVGap = 0)
    (hNM : 2 * N < M)
    (hfinal :
      ((List.range N).foldl (fun st k => arun k st c.body) entry).regs
        rVGap = 0) :
    ∀ j, j < N →
      bodyGapBit c j
        ((List.range j).foldl (fun st k => arun k st c.body) entry) = 0 := by
  intro j hj
  let pre := (List.range j).foldl (fun st k => arun k st c.body) entry
  let bit := bodyGapBit c j pre
  let after := arun j pre c.body
  have hpreWord : WordState pre :=
    foldl_arun_word c.body (List.range j) entry hword.1 hword.2
  have hpreBounds := foldl_body_rvgap_bounds c (List.range j) entry hword (by
    rw [hentry]
    simp only [List.length_range, Nat.zero_add]
    omega)
  have hpreLe : pre.regs rVGap ≤ 2 * j := by
    simpa only [pre, List.length_range, hentry, Nat.zero_add] using
      hpreBounds.2
  have hbitLe : bit ≤ 2 := bodyGapBit_le_two c j pre
  have hfirstRoom : pre.regs rVGap + 2 < M := by omega
  have hfirst := body_rvgap_increment c j pre hfirstRoom
  change after.regs rVGap = pre.regs rVGap + bit at hfirst
  have hafterLe : after.regs rVGap ≤ 2 * (j + 1) := by omega
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [tailLen]
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have hafterWord : WordState after :=
    arun_word j c.body pre hpreWord.1 hpreWord.2
  have htailRoom : after.regs rVGap + 2 * tail.length < M := by
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_rvgap_bounds c tail after hafterWord
    htailRoom
  dsimp only at htailBounds
  have hfinal' :
      (tail.foldl (fun st k => arun k st c.body) after).regs rVGap = 0 := by
    rw [hrange, List.foldl_append] at hfinal
    simpa only [List.foldl_cons, List.foldl_nil, pre, after] using hfinal
  have hafterZero : after.regs rVGap = 0 := by omega
  change bit = 0
  omega

#print axioms markPhaseBody_log_gate_le_one
#print axioms markBody_log_gate_le_one
#print axioms classBody_log_gate_le_one
#print axioms logThroughLiveBody_live_le_one
#print axioms logBeforeRoundCounterBody_live_le_one
#print axioms logRoundCounterBody_finish_le_two
#print axioms logBeforeGapComputeBody_finish_le_two
#print axioms logGapComputeBody_bit_le_two
#print axioms logGapComputeBody_bit_eq_zero_iff
#print axioms beforeGapCommit_eq_compute
#print axioms bodyGapBit_le_two
#print axioms logGapCounterCommitBody_rvgap_run
#print axioms body_rvgap_increment
#print axioms foldl_body_rvgap_bounds
#print axioms every_bodyGapBit_zero_of_fold_zero

end LeanCompCert.Ports.R2SegSieve
