import LeanCompCert.Ports.Prop1224CellMarkToAcc
import LeanCompCert.Ports.Prop1224CellAccArraySemantics
import LeanCompCert.Ports.Prop1224CellAccInactiveSemantics
import LeanCompCert.Ports.Prop1224CellAccTelescope
import LeanCompCert.Ports.Prop1224CellPosition
import LeanCompCert.Ports.Prop1224CellMarkArray

/-!
# Symbolic accumulation-window telescope for Proposition 12.2.4

This file connects a completely represented logical marking window to the
literal accumulation pass.  The induction is over an arbitrary symbolic
prefix; no production window, table, or arithmetic value is evaluated by the
Lean kernel.
-/

namespace LeanCompCert.Ports.Prop1224Cell

set_option maxRecDepth 100000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.Prop1224Margin (C S gqTerm)
open LeanCompCert.Ports.ArraySegMobiusSignal (arun_arr_frame)

/-! ## The disabled marker on an accumulation round -/

/-- The literal four phase selectors recognize exactly an accumulation
round `markSteps + i`, for `i < segLen`. -/
theorem p1224MarkPhaseBody_acc_run (c : CellCfg) (k : Nat)
    (s : AState) (i : Nat) (hr : s.regs rR = c.markSteps + i)
    (hi : i < c.segLen) (hperiod : c.markSteps + c.segLen < M) :
    let out := arun k s (p1224MarkPhaseBody c)
    out.regs 10 = 0 ∧ out.regs 11 = 1 ∧ out.regs 12 = 1 ∧
      out.regs 13 = 0 ∧ out.arr = s.arr := by
  have hTM : c.markSteps < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have hsubOne : 1 + (M - 1) = M := by omega
  have hnotMark : ¬c.markSteps + i < c.markSteps := by omega
  have hr5 : s.regs 5 = c.markSteps + i := by simpa [rR] using hr
  simp only [p1224MarkPhaseBody, arun_lift]
  simp [p1224MarkPhaseInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hr5, hi, hnotMark, rR, hsubOne,
    Nat.mod_eq_of_lt hTM, Nat.mod_eq_of_lt hperiod,
    Nat.mod_eq_of_lt h1M]

/-- The same four literal phase selectors recognize every logarithm round:
both mutation gates are clear and the log gate is set. -/
theorem p1224MarkPhaseBody_log_run (c : CellCfg) (k : Nat)
    (s : AState) (r : Nat) (hr : s.regs rR = r)
    (hlog : c.markSteps + c.segLen ≤ r)
    (hrM : r < M) (hlogStartM : c.markSteps + c.segLen < M) :
    let out := arun k s (p1224MarkPhaseBody c)
    out.regs 10 = 0 ∧ out.regs 11 = 0 ∧ out.regs 12 = 0 ∧
      out.regs 13 = 1 ∧ out.arr = s.arr := by
  have hTM : c.markSteps < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have hsubOne : 1 + (M - 1) = M := by omega
  have hnotMark : ¬r < c.markSteps := by omega
  have hnotPreLog : ¬r < c.markSteps + c.segLen := by omega
  have hr5 : s.regs 5 = r := by simpa [rR] using hr
  simp only [p1224MarkPhaseBody, arun_lift]
  simp [p1224MarkPhaseInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hr5, hnotMark, hnotPreLog, rR, hsubOne,
    Nat.mod_eq_of_lt hTM, Nat.mod_eq_of_lt hlogStartM,
    Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt h1M]

/-- With the marking gate zero, the literal address slice selects the three
dedicated sink words, independently of the stale marking cursor. -/
theorem p1224MarkAddressBody_inactive_run (c : CellCfg) (k : Nat)
    (s : AState) (hactive : s.regs 10 = 0)
    (haddr : 6 * c.segLen < M) :
    let out := arun k s (p1224MarkAddressBody c)
    out.regs 30 = 4 * c.segLen ∧
      out.regs 31 = 5 * c.segLen ∧
      out.regs 32 = 6 * c.segLen ∧ out.arr = s.arr := by
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have h4LM : 4 * c.segLen < M := by omega
  have h5LM : 5 * c.segLen < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have h4add : 4 * c.segLen + c.segLen = 5 * c.segLen := by omega
  have h4add2 : 4 * c.segLen + 2 * c.segLen = 6 * c.segLen := by omega
  simp only [p1224MarkAddressBody, arun_lift]
  simp [p1224MarkAddressInstrs, CellCfg.sink, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hactive, h4add, h4add2,
    Nat.mod_eq_of_lt hLM, Nat.mod_eq_of_lt h2LM,
    Nat.mod_eq_of_lt h4LM, Nat.mod_eq_of_lt h5LM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

/-- The literal three-store marking cell frames any address distinct from its
three selected destinations.  This theorem deliberately does not compute the
values written to the sinks. -/
private theorem p1224MarkRadicalBody_arr_frame_at
    (k : Nat) (s : AState) (a x : Nat)
    (h30 : s.regs 30 = a) (hx : x ≠ a) :
    (arun k s p1224MarkRadicalBody).arr x = s.arr x := by
  simp [p1224MarkRadicalBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, h30, hx]

private theorem p1224MarkPhiBody_arr_frame_at
    (k : Nat) (s : AState) (a x : Nat)
    (h31 : s.regs 31 = a) (hx : x ≠ a) :
    (arun k s p1224MarkPhiBody).arr x = s.arr x := by
  simp [p1224MarkPhiBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, h31, hx]

private theorem p1224MarkSqfBody_arr_frame_at
    (k : Nat) (s : AState) (a x : Nat)
    (h32 : s.regs 32 = a) (hx : x ≠ a) :
    (arun k s p1224MarkSqfBody).arr x = s.arr x := by
  simp [p1224MarkSqfBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, h32, hx]

theorem p1224MarkCellBody_arr_frame
    (k : Nat) (s : AState) (a0 a1 a2 x : Nat)
    (h30 : s.regs 30 = a0) (h31 : s.regs 31 = a1)
    (h32 : s.regs 32 = a2)
    (hx0 : x ≠ a0) (hx1 : x ≠ a1) (hx2 : x ≠ a2) :
    (arun k s p1224MarkCellBody).arr x = s.arr x := by
  let factored := arun k s p1224MarkFactorBody
  let radical := arun k factored p1224MarkRadicalBody
  let phi := arun k radical p1224MarkPhiBody
  have hfactorArr : factored.arr = s.arr :=
    arun_arr_frame k p1224MarkFactorBody s (by rfl)
  have hfactor30 : factored.regs 30 = a0 :=
    (arun_frame k 30 p1224MarkFactorBody (by rfl) s).trans h30
  have hfactor31 : factored.regs 31 = a1 :=
    (arun_frame k 31 p1224MarkFactorBody (by rfl) s).trans h31
  have hfactor32 : factored.regs 32 = a2 :=
    (arun_frame k 32 p1224MarkFactorBody (by rfl) s).trans h32
  have hradArr : radical.arr x = factored.arr x :=
    p1224MarkRadicalBody_arr_frame_at k factored a0 x hfactor30 hx0
  have hrad31 : radical.regs 31 = a1 :=
    (arun_frame k 31 p1224MarkRadicalBody (by rfl) factored).trans hfactor31
  have hrad32 : radical.regs 32 = a2 :=
    (arun_frame k 32 p1224MarkRadicalBody (by rfl) factored).trans hfactor32
  have hphiArr : phi.arr x = radical.arr x :=
    p1224MarkPhiBody_arr_frame_at k radical a1 x hrad31 hx1
  have hphi32 : phi.regs 32 = a2 :=
    (arun_frame k 32 p1224MarkPhiBody (by rfl) radical).trans hrad32
  have hsqfArr : (arun k phi p1224MarkSqfBody).arr x = phi.arr x :=
    p1224MarkSqfBody_arr_frame_at k phi a2 x hphi32 hx2
  simp only [p1224MarkCellBody, arun_append]
  exact hsqfArr.trans (hphiArr.trans (hradArr.trans (congrFun hfactorArr x)))

/-- On every accumulation round the complete literal marker frames the four
live planes.  Its only stores go to addresses `4L`, `5L`, and `6L`. -/
theorem markBody_acc_live_frame (c : CellCfg) (k : Nat) (s : AState)
    (i a : Nat) (hr : s.regs rR = c.markSteps + i)
    (hi : i < c.segLen) (hperiod : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M) (ha : a < 4 * c.segLen) :
    (arun k s c.markBody).arr a = s.arr a := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let prelude := arun k phased (p1224MarkResetBody c)
  let addressed := arun k prelude (p1224MarkAddressBody c)
  let marked := arun k addressed p1224MarkCellBody
  have hphase := p1224MarkPhaseBody_acc_run c k s i hr hi hperiod
  dsimp only at hphase
  have hpreludeArr : prelude.arr = s.arr :=
    (arun_arr_frame k (p1224MarkResetBody c) phased (by rfl)).trans hphase.2.2.2.2
  have hprelude10 : prelude.regs 10 = 0 :=
    (arun_frame k 10 (p1224MarkResetBody c) (by rfl) phased).trans hphase.1
  have haddrs := p1224MarkAddressBody_inactive_run c k prelude
    hprelude10 haddr
  dsimp only at haddrs
  have hmark : marked.arr a = addressed.arr a :=
    p1224MarkCellBody_arr_frame k addressed
      (4 * c.segLen) (5 * c.segLen) (6 * c.segLen) a
      haddrs.1 haddrs.2.1 haddrs.2.2.1 (by omega) (by omega) (by omega)
  have hadvance :
      (arun k marked (p1224MarkAdvanceBody c)).arr = marked.arr :=
    p1224MarkAdvanceBody_arr_frame c k marked
  rw [← p1224MarkFullBody_eq_markBody c]
  simp only [p1224MarkFullBody, p1224MarkPreludeBody,
    p1224MarkResidentBody, arun_append]
  rw [congrFun hadvance a, hmark, congrFun haddrs.2.2.2 a,
    congrFun hpreludeArr a]

/-- Value-independent form of the accumulation-round marker frame.  The
selected address may lie above the live planes (for example in the immutable
prime table); it need only differ from the three literal scratch sinks. -/
theorem markBody_acc_frame_at (c : CellCfg) (k : Nat) (s : AState)
    (i a : Nat) (hr : s.regs rR = c.markSteps + i)
    (hi : i < c.segLen) (hperiod : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M)
    (ha4 : a ≠ 4 * c.segLen) (ha5 : a ≠ 5 * c.segLen)
    (ha6 : a ≠ 6 * c.segLen) :
    (arun k s c.markBody).arr a = s.arr a := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let prelude := arun k phased (p1224MarkResetBody c)
  let addressed := arun k prelude (p1224MarkAddressBody c)
  let marked := arun k addressed p1224MarkCellBody
  have hphase := p1224MarkPhaseBody_acc_run c k s i hr hi hperiod
  dsimp only at hphase
  have hpreludeArr : prelude.arr = s.arr :=
    (arun_arr_frame k (p1224MarkResetBody c) phased (by rfl)).trans
      hphase.2.2.2.2
  have hprelude10 : prelude.regs 10 = 0 :=
    (arun_frame k 10 (p1224MarkResetBody c) (by rfl) phased).trans hphase.1
  have haddrs := p1224MarkAddressBody_inactive_run c k prelude
    hprelude10 haddr
  dsimp only at haddrs
  have hmark : marked.arr a = addressed.arr a :=
    p1224MarkCellBody_arr_frame k addressed
      (4 * c.segLen) (5 * c.segLen) (6 * c.segLen) a
      haddrs.1 haddrs.2.1 haddrs.2.2.1 ha4 ha5 ha6
  have hadvance :
      (arun k marked (p1224MarkAdvanceBody c)).arr = marked.arr :=
    p1224MarkAdvanceBody_arr_frame c k marked
  rw [← p1224MarkFullBody_eq_markBody c]
  simp only [p1224MarkFullBody, p1224MarkPreludeBody,
    p1224MarkResidentBody, arun_append]
  rw [congrFun hadvance a, hmark, congrFun haddrs.2.2.2 a,
    congrFun hpreludeArr a]

/-- On a logarithm round the marker writes only its three scratch sinks, so
it frames every address distinct from those sinks. -/
theorem markBody_log_frame_at (c : CellCfg) (k : Nat) (s : AState)
    (r a : Nat) (hr : s.regs rR = r)
    (hlog : c.markSteps + c.segLen ≤ r)
    (hrM : r < M) (hlogStartM : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M)
    (ha4 : a ≠ 4 * c.segLen) (ha5 : a ≠ 5 * c.segLen)
    (ha6 : a ≠ 6 * c.segLen) :
    (arun k s c.markBody).arr a = s.arr a := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let prelude := arun k phased (p1224MarkResetBody c)
  let addressed := arun k prelude (p1224MarkAddressBody c)
  let marked := arun k addressed p1224MarkCellBody
  have hphase := p1224MarkPhaseBody_log_run c k s r hr hlog hrM
    hlogStartM
  dsimp only at hphase
  have hpreludeArr : prelude.arr = s.arr :=
    (arun_arr_frame k (p1224MarkResetBody c) phased (by rfl)).trans
      hphase.2.2.2.2
  have hprelude10 : prelude.regs 10 = 0 :=
    (arun_frame k 10 (p1224MarkResetBody c) (by rfl) phased).trans hphase.1
  have haddrs := p1224MarkAddressBody_inactive_run c k prelude
    hprelude10 haddr
  dsimp only at haddrs
  have hmark : marked.arr a = addressed.arr a :=
    p1224MarkCellBody_arr_frame k addressed
      (4 * c.segLen) (5 * c.segLen) (6 * c.segLen) a
      haddrs.1 haddrs.2.1 haddrs.2.2.1 ha4 ha5 ha6
  have hadvance :
      (arun k marked (p1224MarkAdvanceBody c)).arr = marked.arr :=
    p1224MarkAdvanceBody_arr_frame c k marked
  rw [← p1224MarkFullBody_eq_markBody c]
  simp only [p1224MarkFullBody, p1224MarkPreludeBody,
    p1224MarkResidentBody, arun_append]
  rw [congrFun hadvance a, hmark, congrFun haddrs.2.2.2 a,
    congrFun hpreludeArr a]

/-- The accumulation selector stays clear through the complete literal
marker on a logarithm round. -/
theorem markBody_log_acc_gate (c : CellCfg) (k : Nat) (s : AState)
    (r : Nat) (hr : s.regs rR = r)
    (hlog : c.markSteps + c.segLen ≤ r)
    (hrM : r < M) (hlogStartM : c.markSteps + c.segLen < M) :
    (arun k s c.markBody).regs 12 = 0 := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let reset := arun k phased (p1224MarkResetBody c)
  have hp := p1224MarkPhaseBody_log_run c k s r hr hlog hrM
    hlogStartM
  dsimp only at hp
  have hreset : reset.regs 12 = 0 :=
    (arun_frame k 12 (p1224MarkResetBody c) (by rfl) phased).trans
      hp.2.2.1
  have hresident :
      (arun k reset (p1224MarkResidentBody c)).regs 12 = 0 :=
    (arun_frame k 12 (p1224MarkResidentBody c) (by rfl) reset).trans
      hreset
  rw [← p1224MarkFullBody_eq_markBody c]
  simpa only [p1224MarkFullBody, p1224MarkPreludeBody, arun_append]

/-- A complete logarithm-phase body frames every non-scratch array address.
In particular this covers all four live planes and the immutable table. -/
theorem body_log_frame_at (c : CellCfg) (k : Nat) (s : AState)
    (r a : Nat) (hr : s.regs rR = r)
    (hlog : c.markSteps + c.segLen ≤ r)
    (hrM : r < M) (hlogStartM : c.markSteps + c.segLen < M)
    (hOne : s.regs rOne = 1) (hZero : s.regs rZero = 0)
    (h7L : 7 * c.segLen < M)
    (ha4 : a ≠ 4 * c.segLen) (ha5 : a ≠ 5 * c.segLen)
    (ha6 : a ≠ 6 * c.segLen) (ha7 : a ≠ 7 * c.segLen) :
    (arun k s c.body).arr a = s.arr a := by
  let marked := arun k s c.markBody
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  have hmark : marked.arr a = s.arr a :=
    markBody_log_frame_at c k s r a hr hlog hrM hlogStartM
      (by omega) ha4 ha5 ha6
  have hgate : marked.regs 12 = 0 :=
    markBody_log_acc_gate c k s r hr hlog hrM hlogStartM
  have hmarkedOne : marked.regs rOne = 1 :=
    (arun_frame k rOne c.markBody (by rfl) s).trans hOne
  have hmarkedZero : marked.regs rZero = 0 :=
    (arun_frame k rZero c.markBody (by rfl) s).trans hZero
  have hacc := accBody_inactive_arr_eq c k marked hgate hmarkedOne
    hmarkedZero h7L
  dsimp only at hacc
  have ha5' : a ≠ 4 * c.segLen + c.segLen := by omega
  have ha6' : a ≠ 4 * c.segLen + 2 * c.segLen := by omega
  have ha7' : a ≠ 4 * c.segLen + 3 * c.segLen := by omega
  have haccFrame : accumulated.arr a = marked.arr a := by
    rw [hacc]
    exact writeP1224AccCell_frame marked c.segLen (4 * c.segLen)
      (accumulated.regs rG) a ha4 ha5' ha6' ha7'
  have hlogArr : logged.arr = accumulated.arr :=
    arun_arr_frame k c.logBody accumulated (by rfl)
  have htailArr : (arun k logged c.tailBody).arr = logged.arr :=
    arun_arr_frame k c.tailBody logged (by rfl)
  simp only [CellCfg.body, arun_append, marked, accumulated, logged]
  rw [congrFun htailArr a, congrFun hlogArr a, haccFrame, hmark]

/-- The running `G_q` carry is also framed throughout a logarithm round. -/
theorem body_log_rG_frame (c : CellCfg) (k : Nat) (s : AState)
    (r : Nat) (hr : s.regs rR = r)
    (hlog : c.markSteps + c.segLen ≤ r)
    (hrM : r < M) (hlogStartM : c.markSteps + c.segLen < M)
    (hGWord : s.regs rG < M) :
    (arun k s c.body).regs rG = s.regs rG := by
  let marked := arun k s c.markBody
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  have hmarkedG : marked.regs rG = s.regs rG :=
    arun_frame k rG c.markBody (by rfl) s
  have hmarkedGWord : marked.regs rG < M := by
    rw [hmarkedG]
    exact hGWord
  have hgate : marked.regs 12 = 0 :=
    markBody_log_acc_gate c k s r hr hlog hrM hlogStartM
  have haccG : accumulated.regs rG = s.regs rG :=
    (accBody_inactive_rG c k marked hgate hmarkedGWord).trans hmarkedG
  have hlogG : logged.regs rG = s.regs rG :=
    (arun_frame k rG c.logBody (by rfl) accumulated).trans haccG
  have htailG : (arun k logged c.tailBody).regs rG = s.regs rG :=
    (arun_frame k rG c.tailBody (by rfl) logged).trans hlogG
  simpa only [CellCfg.body, arun_append, marked, accumulated, logged] using
    htailG

/-! ## Source schedule and exact one-body array effect -/

/-- Source meaning of a marked cell with the decoded totient named
externally.  The conversion to the stable marking-to-accumulation interface
is a definition, not an assumption. -/
structure P1224MarkedCellAccSourceAt
    (x : P1224MarkCell) (n phi : Nat) : Prop where
  radical_dvd : x.radical ∣ n
  radical_le : x.radical ≤ n
  phi_pos : 0 < phi
  phi_le : phi ≤ n
  phi_eq_source : phi = x.phiSmall *
    (if x.radical = n then 1 else n / x.radical - 1)

def P1224MarkedCellAccSourceAt.toSource
    {x : P1224MarkCell} {n phi : Nat}
    (h : P1224MarkedCellAccSourceAt x n phi) :
    P1224MarkedCellAccSource x n :=
  { phi := phi
    radical_dvd := h.radical_dvd
    radical_le := h.radical_le
    phi_pos := h.phi_pos
    phi_le := h.phi_le
    phi_eq_source := h.phi_eq_source }

/-- The datum consumed by the existing `runActiveBodies` telescope at
logical offset `i`. -/
def p1224MarkedAccDatum (_c : CellCfg) (window : P1224MarkWindow)
    (w : Nat) (phi : Nat → Nat) (firstIndex i : Nat) : AccCellDatum :=
  { index := firstIndex + i
    i := i
    w := w
    radical := (window.cells i).radical
    phiSmall := (window.cells i).phiSmall
    sqf := (window.cells i).sqf
    phi := phi i }

/-- Exact natural increment of logical offset `i`. -/
def p1224MarkedAccIncrement (c : CellCfg) (window : P1224MarkWindow)
    (w : Nat) (phi : Nat → Nat) (i : Nat) : Nat :=
  cellMarkedStep c.qPrimes (w + i) (phi i) (window.cells i).sqf

@[simp] theorem p1224MarkedAccDatum_increment
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) (firstIndex i : Nat) :
    (p1224MarkedAccDatum c window w phi firstIndex i).increment c =
      p1224MarkedAccIncrement c window w phi i := rfl

/-- Symbolic source prefix.  The recursive equation is the induction seam;
it never unfolds a concrete production prefix. -/
def p1224MarkedAccPrefix (c : CellCfg) (window : P1224MarkWindow)
    (w : Nat) (phi : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => p1224MarkedAccPrefix c window w phi i +
      p1224MarkedAccIncrement c window w phi i

/-- Consecutive literal body schedule beginning at logical offset `start`.
The external instruction index is equally consecutive. -/
def p1224MarkedAccDataFrom (c : CellCfg) (window : P1224MarkWindow)
    (w : Nat) (phi : Nat → Nat) (firstIndex : Nat) : Nat → Nat →
    List AccCellDatum
  | _, 0 => []
  | start, count + 1 =>
      p1224MarkedAccDatum c window w phi firstIndex start ::
        p1224MarkedAccDataFrom c window w phi firstIndex (start + 1) count

@[simp] theorem p1224MarkedAccDataFrom_nil
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) (firstIndex start : Nat) :
    p1224MarkedAccDataFrom c window w phi firstIndex start 0 = [] := rfl

@[simp] theorem p1224MarkedAccDataFrom_succ
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) (firstIndex start count : Nat) :
    p1224MarkedAccDataFrom c window w phi firstIndex start (count + 1) =
      p1224MarkedAccDatum c window w phi firstIndex start ::
        p1224MarkedAccDataFrom c window w phi firstIndex (start + 1) count :=
  rfl

/-- Exact array effect of one ready complete body at its current cell. -/
theorem body_acc_current_words
    (c : CellCfg) (d : AccCellDatum) (s : AState)
    (hL : 0 < c.segLen)
    (hready : AccCellReady c d (arun d.index s c.markBody)) :
    let out := arun d.index s c.body
    p1224PlaneWordsAt out c.segLen d.i = P1224MarkCell.empty.encode ∧
      out.arr (d.i + 3 * c.segLen) = out.regs rG := by
  have h2L0 : 2 * c.segLen ≠ 0 := by omega
  have hL2L : c.segLen ≠ 2 * c.segLen := by omega
  have h3L0 : 3 * c.segLen ≠ 0 := by omega
  have h3L1L : 3 * c.segLen ≠ c.segLen := by omega
  have h3L2L : 3 * c.segLen ≠ 2 * c.segLen := by omega
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  let out := arun d.index logged c.tailBody
  have harr := accBody_active_arr_eq c d.index d.i d.w marked
    hready.r_eq hready.acc_eq hready.w_eq hready.one_eq hready.zero_eq
    hready.markSteps_lt hready.markSteps_add_lt hready.r_lt hready.index_lt
  dsimp only at harr
  have hlogArr : logged.arr = accumulated.arr :=
    arun_arr_frame d.index c.logBody accumulated (by rfl)
  have htailArr : out.arr = logged.arr :=
    arun_arr_frame d.index c.tailBody logged (by rfl)
  have hlogG : logged.regs rG = accumulated.regs rG :=
    arun_frame d.index rG c.logBody (by rfl) accumulated
  have htailG : out.regs rG = logged.regs rG :=
    arun_frame d.index rG c.tailBody (by rfl) logged
  have houtArr : out.arr = accumulated.arr := htailArr.trans hlogArr
  have houtG : out.regs rG = accumulated.regs rG := htailG.trans hlogG
  simp only [CellCfg.body, arun_append]
  change p1224PlaneWordsAt out c.segLen d.i =
      P1224MarkCell.empty.encode ∧
    out.arr (d.i + 3 * c.segLen) = out.regs rG
  constructor
  · apply P1224PlaneWords.extensional <;>
      simp only [p1224PlaneWordsAt, P1224MarkCell.empty,
        P1224MarkCell.encode]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr, h2L0]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr, hL2L]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr]
  · rw [houtArr, harr, houtG]
    simp [writeP1224AccCell, AState.writeArr,
      h3L0, h3L1L, h3L2L, accumulated]

/-- A ready accumulation body frames all four words belonging to every other
live logical cell. -/
theorem body_acc_other_cell_frame
    (c : CellCfg) (d : AccCellDatum) (s : AState) (j : Nat)
    (hi : d.i < c.segLen) (hj : j < c.segLen) (hne : j ≠ d.i)
    (hmarkPeriod : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M)
    (hready : AccCellReady c d (arun d.index s c.markBody)) :
    let out := arun d.index s c.body
    p1224PlaneWordsAt out c.segLen j =
        p1224PlaneWordsAt s c.segLen j ∧
      out.arr (j + 3 * c.segLen) = s.arr (j + 3 * c.segLen) := by
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  let out := arun d.index logged c.tailBody
  have hmarkR : s.regs rR = c.markSteps + d.i :=
    (arun_frame d.index rR c.markBody (by rfl) s).symm.trans hready.r_eq
  have hmark (a : Nat) (ha : a < 4 * c.segLen) :
      marked.arr a = s.arr a :=
    markBody_acc_live_frame c d.index s d.i a hmarkR hi hmarkPeriod haddr ha
  have harr := accBody_active_arr_eq c d.index d.i d.w marked
    hready.r_eq hready.acc_eq hready.w_eq hready.one_eq hready.zero_eq
    hready.markSteps_lt hready.markSteps_add_lt hready.r_lt hready.index_lt
  dsimp only at harr
  have hlogArr : logged.arr = accumulated.arr :=
    arun_arr_frame d.index c.logBody accumulated (by rfl)
  have htailArr : out.arr = logged.arr :=
    arun_arr_frame d.index c.tailBody logged (by rfl)
  have houtArr : out.arr = accumulated.arr := htailArr.trans hlogArr
  have frame (a : Nat) (ha : a < 4 * c.segLen)
      (h0 : a ≠ d.i) (h1 : a ≠ d.i + c.segLen)
      (h2 : a ≠ d.i + 2 * c.segLen)
      (h3 : a ≠ d.i + 3 * c.segLen) : out.arr a = s.arr a := by
    rw [congrFun houtArr a, congrFun harr a,
      writeP1224AccCell_frame marked c.segLen d.i
        (accumulated.regs rG) a h0 h1 h2 h3,
      hmark a ha]
  simp only [CellCfg.body, arun_append]
  change p1224PlaneWordsAt out c.segLen j =
      p1224PlaneWordsAt s c.segLen j ∧
    out.arr (j + 3 * c.segLen) = s.arr (j + 3 * c.segLen)
  constructor
  · apply P1224PlaneWords.extensional <;> simp only [p1224PlaneWordsAt]
    · exact frame j (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact frame (j + c.segLen) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact frame (j + 2 * c.segLen) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · exact frame (j + 3 * c.segLen) (by omega)
      (by omega) (by omega) (by omega) (by omega)

/-! ## Prefix invariant -/

/-- All fixed-width and source obligations for a complete symbolic
accumulation window.  In particular, `accumulator_lt` is stated against the
exact source prefix, so wraparound is excluded rather than hidden. -/
structure P1224AccWindowGuards
    (c : CellCfg) (window : P1224MarkWindow) (w g : Nat)
    (phi : Nat → Nat) : Prop where
  segLen_pos : 0 < c.segLen
  mark_acc_lt : c.markSteps + c.segLen < M
  period_lt : c.period < M
  window_end_lt : w + c.segLen < M
  sink_end_lt : 6 * c.segLen < M
  primes_lt : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M
  source : ∀ i, i < c.segLen →
    P1224MarkedCellAccSourceAt (window.cells i) (w + i) (phi i)
  sum_lt : ∀ i, i < c.segLen → 2 ^ C + phi i < M
  term_lt : ∀ i, i < c.segLen → gqTerm (phi i) < M
  accumulator_lt : ∀ i, i < c.segLen →
    g + p1224MarkedAccPrefix c window w phi i + gqTerm (phi i) < M

/-- State invariant after exactly `start` consecutive accumulation bodies.
Past cells have been reset and retain their published prefix sums; future
cells still represent the completed logical marking window. -/
structure P1224AccWindowState
    (c : CellCfg) (window : P1224MarkWindow) (w g : Nat)
    (phi : Nat → Nat) (start : Nat) (s : AState) : Prop where
  r_eq : s.regs rR = c.markSteps + start
  w_eq : s.regs rW = w
  g_eq : s.regs rG = g + p1224MarkedAccPrefix c window w phi start
  one_eq : s.regs rOne = 1
  zero_eq : s.regs rZero = 0
  future_planes : ∀ j, start ≤ j → j < c.segLen →
    p1224PlaneWordsAt s c.segLen j = (window.cells j).encode
  past_planes : ∀ j, j < start →
    p1224PlaneWordsAt s c.segLen j = P1224MarkCell.empty.encode
  past_gval : ∀ j, j < start →
    s.arr (j + 3 * c.segLen) =
      g + p1224MarkedAccPrefix c window w phi (j + 1)

/-- A represented marked window at the first accumulation round establishes
the prefix invariant at zero. -/
theorem P1224AccWindowState.zero_of_rep
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {s : AState}
    (hrep : window.Rep c s)
    (hr : s.regs rR = c.markSteps) (hw : s.regs rW = w)
    (hg : s.regs rG = g) (hone : s.regs rOne = 1)
    (hzero : s.regs rZero = 0) :
    P1224AccWindowState c window w g phi 0 s := by
  refine {
    r_eq := by simpa using hr
    w_eq := hw
    g_eq := by simpa [p1224MarkedAccPrefix] using hg
    one_eq := hone
    zero_eq := hzero
    future_planes := ?_
    past_planes := ?_
    past_gval := ?_ }
  · intro j _ hj
    exact hrep.2 j hj
  · intro _ hj
    omega
  · intro _ hj
    omega

/-- Transfer the accumulation selector through the store-free remainder of
the literal marker. -/
theorem markBody_acc_gate
    (c : CellCfg) (k : Nat) (s : AState) (i : Nat)
    (hr : s.regs rR = c.markSteps + i) (hi : i < c.segLen)
    (hperiod : c.markSteps + c.segLen < M) :
    (arun k s c.markBody).regs 12 = 1 := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let reset := arun k phased (p1224MarkResetBody c)
  have hp := p1224MarkPhaseBody_acc_run c k s i hr hi hperiod
  dsimp only at hp
  have hreset : reset.regs 12 = 1 :=
    (arun_frame k 12 (p1224MarkResetBody c) (by rfl) phased).trans hp.2.2.1
  have hresident :
      (arun k reset (p1224MarkResidentBody c)).regs 12 = 1 :=
    (arun_frame k 12 (p1224MarkResidentBody c) (by rfl) reset).trans hreset
  rw [← p1224MarkFullBody_eq_markBody c]
  simpa only [p1224MarkFullBody, p1224MarkPreludeBody, arun_append]

/-- One symbolic accumulation round consumes the represented source cell and
advances the exact prefix invariant. -/
theorem P1224AccWindowState.step
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {initial s : AState} {firstIndex start : Nat}
    (hrep : window.Rep c initial) (hinv : window.CellsInv)
    (guards : P1224AccWindowGuards c window w g phi)
    (hstate : P1224AccWindowState c window w g phi start s)
    (hstart : start < c.segLen) :
    let d := p1224MarkedAccDatum c window w phi firstIndex start
    let out := arun d.index s c.body
    AccCellReady c d (arun d.index s c.markBody) ∧
      P1224AccWindowState c window w g phi (start + 1) out := by
  let d := p1224MarkedAccDatum c window w phi firstIndex start
  let marked := arun d.index s c.markBody
  let out := arun d.index s c.body
  have hnM : w + start < M := by
    have := guards.window_end_lt
    omega
  have hsource := guards.source start hstart
  have _hinput : AccCellInputCorrect c initial w start :=
    hrep.toAccCellInputCorrect hinv hstart hnM hsource.toSource
  have hxInv := hinv start
  have hmarkPlane : p1224PlaneWordsAt marked c.segLen start =
      p1224PlaneWordsAt s c.segLen start := by
    apply P1224PlaneWords.extensional <;> simp only [p1224PlaneWordsAt]
    · exact markBody_acc_live_frame c d.index s start start hstate.r_eq
        hstart guards.mark_acc_lt guards.sink_end_lt (by omega)
    · exact markBody_acc_live_frame c d.index s start
        (start + c.segLen) hstate.r_eq hstart guards.mark_acc_lt
        guards.sink_end_lt (by omega)
    · exact markBody_acc_live_frame c d.index s start
        (start + 2 * c.segLen) hstate.r_eq hstart guards.mark_acc_lt
        guards.sink_end_lt (by omega)
  have hlogical : p1224PlaneWordsAt marked c.segLen start =
      (window.cells start).encode :=
    hmarkPlane.trans (hstate.future_planes start (by omega) hstart)
  have hprod : marked.arr start = (window.cells start).radical := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.radical hlogical
  have hphi : marked.arr (start + c.segLen) =
      (window.cells start).phiSmall := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.phiSmall hlogical
  have hsqf : marked.arr (start + 2 * c.segLen) =
      (window.cells start).sqf := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.sqf hlogical
  have hmarkedR : marked.regs rR = c.markSteps + start :=
    (arun_frame d.index rR c.markBody (by rfl) s).trans hstate.r_eq
  have hmarkedW : marked.regs rW = w :=
    (arun_frame d.index rW c.markBody (by rfl) s).trans hstate.w_eq
  have hmarkedG : marked.regs rG =
      g + p1224MarkedAccPrefix c window w phi start :=
    (arun_frame d.index rG c.markBody (by rfl) s).trans hstate.g_eq
  have hmarkedOne : marked.regs rOne = 1 :=
    (arun_frame d.index rOne c.markBody (by rfl) s).trans hstate.one_eq
  have hmarkedZero : marked.regs rZero = 0 :=
    (arun_frame d.index rZero c.markBody (by rfl) s).trans hstate.zero_eq
  have hready : AccCellReady c d marked := by
    refine {
      prod_eq := by simpa [d, p1224MarkedAccDatum] using hprod
      phi_eq := by simpa [d, p1224MarkedAccDatum] using hphi
      sqf_eq := by simpa [d, p1224MarkedAccDatum] using hsqf
      radical_pos := hxInv.radical_pos
      radical_lt := by
        exact Nat.lt_of_le_of_lt hsource.radical_le hnM
      radical_dvd := hsource.radical_dvd
      radical_le := hsource.radical_le
      phiSmall_lt := by
        exact Nat.lt_of_le_of_lt
          (Nat.le_trans hxInv.phi_le_radical hsource.radical_le) hnM
      phi_pos := hsource.phi_pos
      phi_lt := Nat.lt_of_le_of_lt hsource.phi_le hnM
      phi_eq_source := hsource.phi_eq_source
      r_eq := by simpa [d, p1224MarkedAccDatum] using hmarkedR
      acc_eq := by
        simpa [marked, d] using markBody_acc_gate c d.index s start
          hstate.r_eq hstart guards.mark_acc_lt
      w_eq := by simpa [d, p1224MarkedAccDatum] using hmarkedW
      one_eq := hmarkedOne
      zero_eq := hmarkedZero
      i_lt := by simpa [d, p1224MarkedAccDatum] using hstart
      r_lt := by simpa [d, p1224MarkedAccDatum] using hnM
      index_lt := by
        have := guards.sink_end_lt
        simp [d, p1224MarkedAccDatum]
        omega
      markSteps_lt := by
        have := guards.mark_acc_lt
        omega
      markSteps_add_lt := by
        have := guards.mark_acc_lt
        simp [d, p1224MarkedAccDatum]
        omega
      primes_lt := guards.primes_lt
      sum_lt := by
        simpa [d, p1224MarkedAccDatum] using guards.sum_lt start hstart
      term_lt := by
        simpa [d, p1224MarkedAccDatum] using guards.term_lt start hstart
      accumulator_lt := by
        rw [hmarkedG]
        simpa [d, p1224MarkedAccDatum] using
          guards.accumulator_lt start hstart }
  have hcurrent := body_acc_current_words c d s guards.segLen_pos hready
  dsimp only at hcurrent
  have hstepG := body_run_active_rG c d s hready
  have houtG : out.regs rG =
      g + p1224MarkedAccPrefix c window w phi (start + 1) := by
    rw [hstepG, hstate.g_eq]
    simp [d, AccCellDatum.increment, p1224MarkedAccDatum,
      p1224MarkedAccPrefix,
      p1224MarkedAccIncrement, Nat.add_assoc]
  have hrPeriod : c.markSteps + start < c.period := by
    simp [CellCfg.period, S]
    omega
  have hnextPeriod : c.markSteps + start + 1 < c.period := by
    simp [CellCfg.period, S]
    omega
  have hturn : c.markSteps + start + 1 ≠ c.period :=
    Nat.ne_of_lt hnextPeriod
  have hturn' : c.markSteps + (start + 1) ≠ c.period := by omega
  have hposition := body_position_run c d.index s
    (c.markSteps + start) w hstate.r_eq hstate.w_eq hrPeriod
    guards.period_lt guards.window_end_lt
  dsimp only at hposition
  have houtR : out.regs rR = c.markSteps + (start + 1) := by
    simpa [out, hturn, hturn', Nat.add_assoc] using hposition.1
  have houtW : out.regs rW = w := by
    simpa [out, hturn] using hposition.2
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  have haccOne : accumulated.regs rOne = marked.regs rOne :=
    accBody_reg_frame c rOne d.index marked (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  have haccZero : accumulated.regs rZero = marked.regs rZero :=
    accBody_reg_frame c rZero d.index marked (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  have hlogOne : logged.regs rOne = accumulated.regs rOne :=
    arun_frame d.index rOne c.logBody (by rfl) accumulated
  have hlogZero : logged.regs rZero = accumulated.regs rZero :=
    arun_frame d.index rZero c.logBody (by rfl) accumulated
  have htailOne : (arun d.index logged c.tailBody).regs rOne =
      logged.regs rOne := arun_frame d.index rOne c.tailBody (by rfl) logged
  have htailZero : (arun d.index logged c.tailBody).regs rZero =
      logged.regs rZero := arun_frame d.index rZero c.tailBody (by rfl) logged
  have houtOne : out.regs rOne = 1 := by
    have hchain := htailOne.trans (hlogOne.trans (haccOne.trans hmarkedOne))
    simpa only [out, marked, accumulated, logged, CellCfg.body,
      arun_append] using hchain
  have houtZero : out.regs rZero = 0 := by
    have hchain := htailZero.trans (hlogZero.trans (haccZero.trans hmarkedZero))
    simpa only [out, marked, accumulated, logged, CellCfg.body,
      arun_append] using hchain
  refine ⟨hready, {
    r_eq := houtR
    w_eq := houtW
    g_eq := houtG
    one_eq := houtOne
    zero_eq := houtZero
    future_planes := ?_
    past_planes := ?_
    past_gval := ?_ }⟩
  · intro j hjNext hjL
    have hjNe : j ≠ start := by omega
    have hframe := body_acc_other_cell_frame c d s j hstart hjL hjNe
      guards.mark_acc_lt guards.sink_end_lt hready
    dsimp only at hframe
    exact hframe.1.trans (hstate.future_planes j (by omega) hjL)
  · intro j hjPast
    by_cases hj : j = start
    · subst j
      exact hcurrent.1
    · have hframe := body_acc_other_cell_frame c d s j hstart
          (by omega) hj guards.mark_acc_lt guards.sink_end_lt hready
      dsimp only at hframe
      exact hframe.1.trans (hstate.past_planes j (by omega))
  · intro j hjPast
    by_cases hj : j = start
    · subst j
      exact hcurrent.2.trans houtG
    · have hframe := body_acc_other_cell_frame c d s j hstart
          (by omega) hj guards.mark_acc_lt guards.sink_end_lt hready
      dsimp only at hframe
      exact hframe.2.trans (hstate.past_gval j (by omega))

/-! ## Symbolic finite telescope -/

/-- The generated consecutive datum schedule sums to the corresponding
source prefix. -/
theorem p1224MarkedAccDataFrom_increment_sum
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) (firstIndex start count : Nat) :
    p1224MarkedAccPrefix c window w phi start +
        ((p1224MarkedAccDataFrom c window w phi firstIndex start count).map
          (AccCellDatum.increment c)).sum =
      p1224MarkedAccPrefix c window w phi (start + count) := by
  induction count generalizing start with
  | zero => simp [p1224MarkedAccDataFrom]
  | succ count ih =>
      rw [p1224MarkedAccDataFrom_succ]
      simp only [List.map_cons, List.sum_cons,
        p1224MarkedAccDatum_increment]
      rw [← Nat.add_assoc,
        show p1224MarkedAccPrefix c window w phi start +
              p1224MarkedAccIncrement c window w phi start =
            p1224MarkedAccPrefix c window w phi (start + 1) by rfl,
        ih (start + 1)]
      congr 1
      omega

/-- The source integers visited by the generated schedule are exactly the
consecutive interval `w + start, ..., w + start + count - 1`. -/
theorem p1224MarkedAccDataFrom_candidates
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) (firstIndex start count : Nat) :
    (p1224MarkedAccDataFrom c window w phi firstIndex start count).map
        (fun d => d.w + d.i) =
      (List.range count).map (fun j => w + (start + j)) := by
  induction count generalizing start with
  | zero => simp [p1224MarkedAccDataFrom]
  | succ count ih =>
      rw [p1224MarkedAccDataFrom_succ, List.range_succ_eq_map]
      simp only [List.map_cons, p1224MarkedAccDatum, List.map_map, ih]
      congr 1
      apply List.map_congr_left
      intro j _
      congr 1
      omega

/-- The prefix invariant constructs the existing `ActiveBodyTraceReady` for
an arbitrary consecutive symbolic slice and returns the exact final state
invariant. -/
theorem p1224MarkedAccDataFrom_trace
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {initial : AState} {firstIndex : Nat}
    (hrep : window.Rep c initial) (hinv : window.CellsInv)
    (guards : P1224AccWindowGuards c window w g phi)
    (start count : Nat) (s : AState)
    (hspan : start + count ≤ c.segLen)
    (hstate : P1224AccWindowState c window w g phi start s) :
    let ds := p1224MarkedAccDataFrom c window w phi firstIndex start count
    let out := runActiveBodies c ds s
    ActiveBodyTraceReady c ds s ∧
      P1224AccWindowState c window w g phi (start + count) out := by
  induction count generalizing start s with
  | zero =>
      simp only [p1224MarkedAccDataFrom_nil, runActiveBodies, Nat.add_zero]
      exact ⟨True.intro, hstate⟩
  | succ count ih =>
      have hstart : start < c.segLen := by omega
      have hstep := hstate.step hrep hinv guards hstart
        (firstIndex := firstIndex)
      dsimp only at hstep
      let d := p1224MarkedAccDatum c window w phi firstIndex start
      let next := arun d.index s c.body
      have hrest := ih (start := start + 1) (s := next)
        (by omega) hstep.2
      dsimp only at hrest
      simp only [p1224MarkedAccDataFrom_succ, runActiveBodies]
      refine ⟨⟨hstep.1, hrest.1⟩, ?_⟩
      change P1224AccWindowState c window w g phi
        (start + (count + 1))
        (runActiveBodies c
          (p1224MarkedAccDataFrom c window w phi firstIndex (start + 1) count)
          next)
      have hidx : start + 1 + count = start + (count + 1) := by omega
      rw [← hidx]
      exact hrest.2

/-- Full represented accumulation window.  This is the reusable
signature-to-theorem endpoint: the actual consecutive complete bodies have a
ready trace, their accumulator is the exact source prefix, every source plane
is reset, and every published `gval` cell contains its exact prefix value. -/
theorem p1224MarkedAccWindow_run
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {s : AState} (firstIndex : Nat)
    (hrep : window.Rep c s) (hinv : window.CellsInv)
    (guards : P1224AccWindowGuards c window w g phi)
    (hr : s.regs rR = c.markSteps) (hw : s.regs rW = w)
    (hg : s.regs rG = g) (hone : s.regs rOne = 1)
    (hzero : s.regs rZero = 0) :
    let ds := p1224MarkedAccDataFrom c window w phi firstIndex 0 c.segLen
    let out := runActiveBodies c ds s
    ActiveBodyTraceReady c ds s ∧
      out.regs rG = g + p1224MarkedAccPrefix c window w phi c.segLen ∧
      (∀ i, i < c.segLen →
        p1224PlaneWordsAt out c.segLen i = P1224MarkCell.empty.encode) ∧
      (∀ i, i < c.segLen →
        out.arr (i + 3 * c.segLen) =
          g + p1224MarkedAccPrefix c window w phi (i + 1)) := by
  let ds := p1224MarkedAccDataFrom c window w phi firstIndex 0 c.segLen
  let out := runActiveBodies c ds s
  have hstate0 : P1224AccWindowState c window w g phi 0 s :=
    P1224AccWindowState.zero_of_rep hrep hr hw hg hone hzero
  have htrace := p1224MarkedAccDataFrom_trace hrep hinv guards
    0 c.segLen s (by omega) hstate0 (firstIndex := firstIndex)
  dsimp only at htrace
  have hsum := p1224MarkedAccDataFrom_increment_sum c window w phi
    firstIndex 0 c.segLen
  have hrunG := runActiveBodies_rG c ds s htrace.1
  have houtG : out.regs rG =
      g + p1224MarkedAccPrefix c window w phi c.segLen := by
    rw [hrunG, hg]
    simpa [ds, p1224MarkedAccPrefix] using congrArg (g + ·) hsum
  have hfinal : P1224AccWindowState c window w g phi c.segLen out := by
    simpa only [Nat.zero_add, ds, out] using htrace.2
  exact ⟨htrace.1, houtG,
    (fun i hi => hfinal.past_planes i hi),
    (fun i hi => hfinal.past_gval i hi)⟩

#print axioms P1224AccWindowState.step
#print axioms p1224MarkedAccDataFrom_increment_sum
#print axioms p1224MarkedAccDataFrom_candidates
#print axioms p1224MarkedAccDataFrom_trace
#print axioms p1224MarkedAccWindow_run

#print axioms p1224MarkPhaseBody_acc_run
#print axioms p1224MarkPhaseBody_log_run
#print axioms p1224MarkAddressBody_inactive_run
#print axioms p1224MarkCellBody_arr_frame
#print axioms markBody_acc_live_frame
#print axioms markBody_acc_frame_at
#print axioms markBody_log_frame_at
#print axioms markBody_log_acc_gate
#print axioms body_log_frame_at
#print axioms body_log_rG_frame
#print axioms body_acc_current_words
#print axioms body_acc_other_cell_frame

end LeanCompCert.Ports.Prop1224Cell
