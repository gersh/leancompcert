import LeanCompCert.Ports.RamareCombined100MShapeHostClassAdvancePre
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleMarkPre

/-!
# Production classification cursor state cut

This module establishes the advance premise after the phase/reset/mark-cell
prefix in a production classification round.  The proof is symbolic in the
state and treats the initialized table only as an array frame; no table fold
or sweep is evaluated.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def productionClassCursor (fuel : Nat) : PowerCursor :=
  { pi := productionCursorCfg.tableLen, pow := 1, base := 1,
    j := productionCursorCfg.segLen + 1 + fuel }

def productionTerminalCursor : PowerCursor := productionClassCursor 0

set_option maxRecDepth 10000 in
theorem productionClassAdvanceWordPre
    (fuel k : Nat) (s : AState)
    (hfuel : fuel ≤ productionCursorCfg.segLen)
    (hclass : productionCursorCfg.markSteps ≤ s.regs rR)
    (hcursor : machinePowerCursor s = productionClassCursor fuel)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    let phased := arun k s (lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let marked := arun k reset productionCursorCfg.markCellPrefix
    AdvanceWordPre productionCursorCfg marked
        (fun pi => marked.arr (pi + productionCursorCfg.tableBase)) ∧
      machinePowerCursor marked = productionClassCursor fuel ∧
      marked.regs 10 = 0 ∧ marked.regs 25 = 1 := by
  let c := productionCursorCfg
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let marked := arun k reset c.markCellPrefix
  have hsteps : c.markSteps < M := productionCursorCfg_markSteps_lt_word
  have hstepsPos : 0 < c.markSteps := by
    change 0 < productionCursorCfg.markSteps
    exact productionCursorCfg_markSteps_pos
  have hclassC : c.markSteps ≤ s.regs rR := by
    simpa only [c] using hclass
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : phased.regs 10 = 0 := by
    rw [hp.1, if_neg (Nat.not_lt_of_ge hclass)]
  have hpR : phased.regs rR = s.regs rR := hp.2.2.1
  have hnonzero : phased.regs rR ≠ 0 := by omega
  have hpCursor : machinePowerCursor phased = productionClassCursor fuel := by
    apply PowerCursor.ext
    · exact (arun_frame k rPi (lift c.markPhaseBody) (by rfl) s).trans
        (congrArg PowerCursor.pi hcursor)
    · exact (arun_frame k rPow (lift c.markPhaseBody) (by rfl) s).trans
        (congrArg PowerCursor.pow hcursor)
    · exact (arun_frame k rBase (lift c.markPhaseBody) (by rfl) s).trans
        (congrArg PowerCursor.base hcursor)
    · exact (arun_frame k rJ (lift c.markPhaseBody) (by rfl) s).trans
        (congrArg PowerCursor.j hcursor)
  rcases productionTableHead_word with ⟨hp0, hp0M⟩
  have hrCursor : machinePowerCursor reset = productionClassCursor fuel := by
    have hr := c.markResetBody_machinePowerCursor k phased hp0 hp0M
      (by
        intro _
        have h := congrArg PowerCursor.pi hpCursor
        change phased.regs rPi = c.tableLen at h
        rw [h]
        have hb := productionCursorStaticWordBounds.2.2.2.1
        have hbC : c.tableLen + 1 < M := by
          simpa only [c] using hb
        omega)
      (by
        intro _
        have h := congrArg PowerCursor.pow hpCursor
        change phased.regs rPow = 1 at h
        rw [h]
        exact one_lt_M)
      (by
        intro _
        have h := congrArg PowerCursor.base hpCursor
        change phased.regs rBase = 1 at h
        rw [h]
        exact one_lt_M)
      (by
        intro _
        have h := congrArg PowerCursor.j hpCursor
        change phased.regs rJ = c.segLen + 1 + fuel at h
        rw [h]
        have hb : 2 * productionCursorCfg.segLen + 2 < M := by
          change 2 * 999900 + 2 < M
          decide
        have hbC : 2 * c.segLen + 2 < M := by simpa only [c] using hb
        have hfuelC : fuel ≤ c.segLen := by simpa only [c] using hfuel
        omega)
    rw [hr, resetPowerCursor, if_neg hnonzero]
    exact hpCursor
  have hr10 : reset.regs 10 = 0 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  rcases productionStaticPlaneWordBounds with
    ⟨hseg, h7, h8, h9, h10, h11, h12, h13⟩
  have ha := c.markAddressBody_inactive_run k reset hr10
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha
  let addressed := arun k reset c.markAddressBody
  have ha25 : addressed.regs 25 = 1 := by
    -- The inactive address selector computes its complement bit as one.
    dsimp only [addressed]
    simp [Cfg.markAddressBody, Cfg.sink, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      hr10, Nat.mod_eq_of_lt one_lt_M]
  have hm25 : marked.regs 25 = 1 := by
    have hload := arun_frame k 25 Cfg.markLoadBody (by rfl) addressed
    have hcell := arun_frame k 25 Cfg.markCellBody (by rfl)
      (arun k addressed Cfg.markLoadBody)
    simpa only [marked, Cfg.markCellPrefix, arun_append] using
      hcell.trans (hload.trans ha25)
  have prefixFrame (r : Nat)
      (haF : writes r c.markAddressBody = false)
      (hlF : writes r Cfg.markLoadBody = false)
      (hcF : writes r Cfg.markCellBody = false) :
      marked.regs r = reset.regs r := by
    have haF' := arun_frame k r c.markAddressBody haF reset
    have hlF' := arun_frame k r Cfg.markLoadBody hlF addressed
    have hcF' := arun_frame k r Cfg.markCellBody hcF
      (arun k addressed Cfg.markLoadBody)
    simpa only [marked, Cfg.markCellPrefix, arun_append] using
      hcF'.trans (hlF'.trans haF')
  have hmCursor : machinePowerCursor marked = productionClassCursor fuel := by
    apply PowerCursor.ext
    · exact (prefixFrame rPi (by rfl) (by rfl) (by rfl)).trans
        (congrArg PowerCursor.pi hrCursor)
    · exact (prefixFrame rPow (by rfl) (by rfl) (by rfl)).trans
        (congrArg PowerCursor.pow hrCursor)
    · exact (prefixFrame rBase (by rfl) (by rfl) (by rfl)).trans
        (congrArg PowerCursor.base hrCursor)
    · exact (prefixFrame rJ (by rfl) (by rfl) (by rfl)).trans
        (congrArg PowerCursor.j hrCursor)
  have hm10 : marked.regs 10 = 0 :=
    (prefixFrame 10 (by rfl) (by rfl) (by rfl)).trans hr10
  have hmPi : marked.regs rPi = c.tableLen := by
    exact congrArg PowerCursor.pi hmCursor
  have hmPow : marked.regs rPow = 1 := by
    exact congrArg PowerCursor.pow hmCursor
  have hmBase : marked.regs rBase = 1 := by
    exact congrArg PowerCursor.base hmCursor
  have hmJ : marked.regs rJ = c.segLen + 1 + fuel := by
    exact congrArg PowerCursor.j hmCursor
  have frameIncoming (r : Nat)
      (hpF : writes r (lift c.markPhaseBody) = false)
      (hrF : writes r c.markResetBody = false)
      (haF : writes r c.markAddressBody = false)
      (hlF : writes r Cfg.markLoadBody = false)
      (hcF : writes r Cfg.markCellBody = false) :
      marked.regs r = s.regs r :=
    (prefixFrame r haF hlF hcF).trans
      ((arun_frame k r c.markResetBody hrF phased).trans
        (arun_frame k r (lift c.markPhaseBody) hpF s))
  refine ⟨?_, hmCursor, hm10, hm25⟩
  apply advanceWordPre_of_classCursor c marked
    (fun pi => marked.arr (pi + c.tableBase)) hm10 hm25 hmPi hmPow hmBase
  · intro pi _
    rfl
  · simpa only [c] using productionCursorStaticWordBounds.2.1
  · have hb : c.tableLen + 1 < M := by
      simpa only [c] using productionCursorStaticWordBounds.2.2.2.1
    omega
  · simpa only [c] using productionCursorStaticWordBounds.2.2.2.2.1
  · rw [hmJ]
    have hb : 2 * productionCursorCfg.segLen + 2 < M := by
      change 2 * 999900 + 2 < M
      decide
    have hbC : 2 * c.segLen + 2 < M := by simpa only [c] using hb
    have hfuelC : fuel ≤ c.segLen := by simpa only [c] using hfuel
    omega
  · exact hseg
  · exact hstepsPos
  · exact hsteps
  · rw [frameIncoming rR (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact hclassC
  · rw [frameIncoming rViol (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact hviol
  · rw [frameIncoming rVMark (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)]
    exact hvmark

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
