import LeanCompCert.Ports.Prop1224Row
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.ArrayPipeline

/-!
# Finite window-position telescope for the Prop. 12.2.4 row sweep

The row verifier's body is deliberately large, but its position proof is not:
all six mathematical phases frame `rR` and `rW`, and only the first six scalar
instructions of the tail advance them.  The theorems below stay generic in the
configuration, unroll factor, and window count.  Thus production computation
runs in compiled code rather than by kernel reduction.
-/

namespace LeanCompCert.Ports.Prop1224Row

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.PsiSegSieve (storeLits seedRegs)

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

@[simp] theorem writes_append (r : Nat) (xs ys : List AInstr) :
    writes r (xs ++ ys) = (writes r xs || writes r ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, writes_cons, ih, Bool.or_assoc]

theorem writes_replicate_flatten (r n : Nat) (l : List AInstr)
    (h : writes r l = false) :
    writes r ((List.replicate n l).flatten) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, writes_append, h, ih]
      rfl

theorem logEngine_position_frame (n : Nat) :
    writes rR (logEngine n) = false ∧ writes rW (logEngine n) = false := by
  constructor
  · simp only [logEngine, writes_append, Bool.or_eq_false_iff]
    exact ⟨by decide, writes_replicate_flatten rR n logRound (by decide)⟩
  · simp only [logEngine, writes_append, Bool.or_eq_false_iff]
    exact ⟨by decide, writes_replicate_flatten rW n logRound (by decide)⟩

theorem expEngine_position_frame (n : Nat) :
    writes rR (expEngine n) = false ∧ writes rW (expEngine n) = false := by
  constructor
  · simp only [expEngine, writes_append, Bool.or_eq_false_iff]
    exact ⟨by decide, writes_replicate_flatten rR n expRound (by decide)⟩
  · simp only [expEngine, writes_append, Bool.or_eq_false_iff]
    exact ⟨by decide, writes_replicate_flatten rW n expRound (by decide)⟩

theorem markBody_position_frame (c : RowCfg) :
    writes rR c.markBody = false ∧ writes rW c.markBody = false := by
  exact ⟨by rfl, by rfl⟩

theorem deriveBody_position_frame (c : RowCfg) :
    writes rR c.deriveBody = false ∧ writes rW c.deriveBody = false := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> exact ⟨by rfl, by rfl⟩

theorem latchBody_position_frame (c : RowCfg) :
    writes rR c.latchBody = false ∧ writes rW c.latchBody = false := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> exact ⟨by rfl, by rfl⟩

theorem finishBody_position_frame (c : RowCfg) :
    writes rR c.finishBody = false ∧ writes rW c.finishBody = false := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> exact ⟨by rfl, by rfl⟩

theorem payload_position_frame (c : RowCfg) :
    writes rR
        (c.markBody ++ c.deriveBody ++ logEngine c.expUnroll ++
          expEngine c.expUnroll ++ c.latchBody ++ c.finishBody) = false ∧
      writes rW
        (c.markBody ++ c.deriveBody ++ logEngine c.expUnroll ++
          expEngine c.expUnroll ++ c.latchBody ++ c.finishBody) = false := by
  constructor
  · simp only [writes_append, (markBody_position_frame c).1,
      (deriveBody_position_frame c).1, (logEngine_position_frame c.expUnroll).1,
      (expEngine_position_frame c.expUnroll).1, (latchBody_position_frame c).1,
      (finishBody_position_frame c).1, Bool.false_or]
  · simp only [writes_append, (markBody_position_frame c).2,
      (deriveBody_position_frame c).2, (logEngine_position_frame c.expUnroll).2,
      (expEngine_position_frame c.expUnroll).2, (latchBody_position_frame c).2,
      (finishBody_position_frame c).2, Bool.false_or]

/-- Exact round/window effect of the literal row tail.  Its later scheduling
and drain instructions frame these two position registers. -/
theorem tailBody_position_run (c : RowCfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := arun k s c.tailBody
    out.regs rR = (if r + 1 = c.period then 0 else r + 1) ∧
      out.regs rW = (if r + 1 = c.period then w + c.segLen else w) := by
  have hrNext : r + 1 < M := by omega
  have hwM : w < M := by omega
  have honeM : 1 < M := by decide
  have honeMod : 1 % M = 1 := Nat.mod_eq_of_lt honeM
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiod
  have hr' : s.regs 5 = r := by simpa only [rR] using hr
  have hw' : s.regs 6 = w := by simpa only [rW] using hw
  by_cases hturn : r + 1 = c.period
  · simp [RowCfg.tailBody, latchR, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, rR, rW, rRnd, rSlot, rCi, hr', hw', hturn,
      honeMod, hperiodMod, Nat.mod_eq_of_lt hwL,
      show 1 + (M - 1) = M by omega]
  · simp [RowCfg.tailBody, latchR, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, rR, rW, rRnd, rSlot, rCi, hr', hw', hturn,
      honeMod, hperiodMod, Nat.mod_eq_of_lt hrNext, Nat.mod_eq_of_lt hwM]

/-- One complete literal row body has exactly the small tail's position
effect, regardless of its mathematical payload. -/
theorem body_position_run (c : RowCfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := arun k s c.body
    out.regs rR = (if r + 1 = c.period then 0 else r + 1) ∧
      out.regs rW = (if r + 1 = c.period then w + c.segLen else w) := by
  let payload := c.markBody ++ c.deriveBody ++ logEngine c.expUnroll ++
    expEngine c.expUnroll ++ c.latchBody ++ c.finishBody
  let beforeTail := arun k s payload
  have beforeR : beforeTail.regs rR = r :=
    (arun_frame k rR payload (payload_position_frame c).1 s).trans hr
  have beforeW : beforeTail.regs rW = w :=
    (arun_frame k rW payload (payload_position_frame c).2 s).trans hw
  have ht := tailBody_position_run c k beforeTail r w beforeR beforeW
    hrP hperiod hwL
  simpa only [RowCfg.body, arun_append, payload, beforeTail] using ht

/-- At most one row window's worth of literal loop indices telescopes without
unfolding the 1,625-instruction payload. -/
theorem foldl_body_position (c : RowCfg) (indices : List Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hn : r + indices.length ≤ c.period)
    (hperiod : c.period < M) (hwL : w + c.segLen < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    out.regs rR =
        (if r + indices.length = c.period then 0 else r + indices.length) ∧
      out.regs rW =
        (if r + indices.length = c.period then w + c.segLen else w) := by
  induction indices generalizing s r w with
  | nil =>
      have hrNe : r ≠ c.period := Nat.ne_of_lt hrP
      simp [hrNe, hr, hw]
  | cons k ks ih =>
      simp only [List.length_cons] at hn ⊢
      have hstep := body_position_run c k s r w hr hw hrP hperiod hwL
      by_cases hturn : r + 1 = c.period
      · have hksZero : ks.length = 0 := by omega
        have hksNil : ks = [] := by
          cases ks with
          | nil => rfl
          | cons x xs => simp at hksZero
        subst ks
        simpa [hturn] using hstep
      · have hrNextP : r + 1 < c.period := by omega
        have hrest : r + 1 + ks.length ≤ c.period := by omega
        have hstepR : (arun k s c.body).regs rR = r + 1 := by
          simpa [hturn] using hstep.1
        have hstepW : (arun k s c.body).regs rW = w := by
          simpa [hturn] using hstep.2
        have hi := ih (s := arun k s c.body) (r := r + 1) (w := w)
          hstepR hstepW hrNextP hrest hwL
        simpa only [List.foldl_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hi

/-- One exact flattened row window advances by `segLen` and resets its round
cursor. -/
theorem range_body_full_window_position (c : RowCfg) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hperiod0 : 0 < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := (List.range c.period).foldl
      (fun st k => arun k st c.body) s
    out.regs rR = 0 ∧ out.regs rW = w + c.segLen := by
  have h := foldl_body_position c (List.range c.period) s 0 w hr hw
    hperiod0 (by simp) hperiod hwL
  simpa using h

/-- Literal indices belonging to window `q` in the flattened row program. -/
def bodyWindowIndices (c : RowCfg) (q : Nat) : List Nat :=
  (List.range c.period).map (fun j => q * c.period + j)

/-- Proof-oriented grouping of complete compiled row windows. -/
def bodyWindowPrefix (c : RowCfg) (s : AState) : Nat → AState
  | 0 => s
  | q + 1 =>
      (bodyWindowIndices c q).foldl (fun st k => arun k st c.body)
        (bodyWindowPrefix c s q)

/-- Grouping the flat loop into consecutive row periods preserves every
literal loop index and its order. -/
theorem bodyWindowPrefix_eq_range (c : RowCfg) (s : AState) (q : Nat) :
    bodyWindowPrefix c s q =
      (List.range (c.period * q)).foldl
        (fun st k => arun k st c.body) s := by
  induction q with
  | zero => simp [bodyWindowPrefix]
  | succ q ih =>
      rw [bodyWindowPrefix, ih]
      rw [Nat.mul_succ, List.range_add, List.foldl_append]
      simp only [bodyWindowIndices]
      congr 1
      apply List.map_congr_left
      intro j hj
      simp [Nat.mul_comm]

/-- Any finite number of complete compiled row windows advances the base by
the corresponding span.  This is symbolic in `q`; no production fold is
evaluated in Lean. -/
theorem bodyWindowPrefix_position (c : RowCfg) (q : Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hperiod0 : 0 < c.period) (hperiod : c.period < M)
    (hspan : w + q * c.segLen < M) :
    let out := bodyWindowPrefix c s q
    out.regs rR = 0 ∧ out.regs rW = w + q * c.segLen := by
  induction q generalizing s w with
  | zero => simpa [bodyWindowPrefix] using And.intro hr hw
  | succ q ih =>
      have hprefix : w + q * c.segLen < M := by
        rw [Nat.succ_mul] at hspan
        omega
      have hi := ih s w hr hw hprefix
      let before := bodyWindowPrefix c s q
      change before.regs rR = 0 ∧
        before.regs rW = w + q * c.segLen at hi
      have hnext : w + q * c.segLen + c.segLen < M := by
        rw [Nat.succ_mul] at hspan
        omega
      have hwindow := foldl_body_position c
        (bodyWindowIndices c q) before 0 (w + q * c.segLen)
        hi.1 hi.2 hperiod0 (by simp [bodyWindowIndices]) hperiod hnext
      rw [bodyWindowPrefix]
      simpa [bodyWindowIndices, Nat.succ_mul, Nat.add_assoc] using hwindow

/-- Dynamic literal table initialization writes only its two scratch
registers and frames the row position. -/
theorem storeLits_position_frame (l : List (Nat × Nat)) :
    writes rR (storeLits l) = false ∧ writes rW (storeLits l) = false := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simpa [storeLits, PsiSegSieve.storeLit, instrWrites, sdest, rR, rW]
        using ih

/-- The literal row initializer starts at round zero and at its configured
first `q`, for any incoming array. -/
theorem rowEntry_position (c : RowCfg) (arr : Nat → Nat) (hloM : c.lo < M) :
    let entry := arun 0 (initialAStateWithArray arr) (rowProgram c).init
    entry.regs rR = 0 ∧ entry.regs rW = c.lo := by
  let start := initialAStateWithArray arr
  let stored := arun 0 start (storeLits c.tableCells)
  have hstoredR : stored.regs rR = 0 := by
    rw [arun_frame 0 rR _ (storeLits_position_frame c.tableCells).1 start]
    rfl
  have hstored5 : stored.regs 5 = 0 := by simpa only [rR] using hstoredR
  have hloMod : c.lo % M = c.lo := Nat.mod_eq_of_lt hloM
  have hseed :
      let out := arun 0 stored (seedRegs c.seedList)
      out.regs rR = 0 ∧ out.regs rW = c.lo := by
    simp [RowCfg.seedList, seedRegs, arun, astep, AState.writeReg,
      sdest, sval, denoteOperand, rR, rW, rOne, rZero, rA13, rA23,
      rUlo, rT3m, rXx, hstored5, hloMod]
  simpa only [rowProgram, RowCfg.init, arun_append, start, stored] using hseed

/-- The actual flattened loop of the row program covers precisely
`segCount` complete windows. -/
theorem rowLoop_position (c : RowCfg) (arr : Nat → Nat) (hloM : c.lo < M)
    (hperiod0 : 0 < c.period) (hperiodM : c.period < M)
    (hspan : c.lo + c.segCount * c.segLen < M) :
    let entry := arun 0 (initialAStateWithArray arr) (rowProgram c).init
    let loopOut := (List.range (c.period * c.segCount)).foldl
      (fun s index => arun index s c.body) entry
    loopOut.regs rR = 0 ∧
      loopOut.regs rW = c.lo + c.segCount * c.segLen := by
  let entry := arun 0 (initialAStateWithArray arr) (rowProgram c).init
  have hentry := rowEntry_position c arr hloM
  change entry.regs rR = 0 ∧ entry.regs rW = c.lo at hentry
  have hprefix := bodyWindowPrefix_position c c.segCount entry c.lo
    hentry.1 hentry.2 hperiod0 hperiodM hspan
  rw [bodyWindowPrefix_eq_range] at hprefix
  simpa only [entry] using hprefix

/-- A successful source execution of the complete row program has traversed
the full configured `q` range; its epilogue frames the position. -/
theorem rowSource_position (c : RowCfg) (arr : Nat → Nat) (out : AState)
    (hloM : c.lo < M) (hperiod0 : 0 < c.period)
    (hperiodM : c.period < M)
    (hspan : c.lo + c.segCount * c.segLen < M)
    (hRun : (rowProgram c).runFromArray arr = some out) :
    out.regs rR = 0 ∧
      out.regs rW = c.lo + c.segCount * c.segLen := by
  let p := rowProgram c
  let entry := arun 0 (initialAStateWithArray arr) p.init
  let loopOut := (List.range (c.period * c.segCount)).foldl
    (fun s index => arun index s c.body) entry
  have hloop := rowLoop_position c arr hloM hperiod0 hperiodM hspan
  change loopOut.regs rR = 0 ∧
    loopOut.regs rW = c.lo + c.segCount * c.segLen at hloop
  have hout := AProgram.eq_arun_of_runFromArray_eq_some p arr out hRun
  change out = arun 0 loopOut c.epilogue at hout
  have hframeR : (arun 0 loopOut c.epilogue).regs rR = loopOut.regs rR :=
    arun_frame 0 rR c.epilogue (by rfl) loopOut
  have hframeW : (arun 0 loopOut c.epilogue).regs rW = loopOut.regs rW :=
    arun_frame 0 rW c.epilogue (by rfl) loopOut
  rw [hout]
  exact ⟨hframeR.trans hloop.1, hframeW.trans hloop.2⟩

#print axioms tailBody_position_run
#print axioms body_position_run
#print axioms foldl_body_position
#print axioms range_body_full_window_position
#print axioms bodyWindowPrefix_eq_range
#print axioms bodyWindowPrefix_position
#print axioms rowEntry_position
#print axioms rowLoop_position
#print axioms rowSource_position

end LeanCompCert.Ports.Prop1224Row
