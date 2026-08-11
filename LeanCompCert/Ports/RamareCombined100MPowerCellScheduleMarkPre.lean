import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleMarkPreA

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount cursorLiveEvents)
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

/-- All seven live-plane addresses fit in one word for every live production
cursor offset. -/
theorem productionLivePlaneWordBounds {j : Nat}
    (hj : j < productionCursorCfg.segLen) :
    j < M ∧ j + productionCursorCfg.segLen < M ∧
      j + 2 * productionCursorCfg.segLen < M ∧
      j + 3 * productionCursorCfg.segLen < M ∧
      j + 4 * productionCursorCfg.segLen < M ∧
      j + 5 * productionCursorCfg.segLen < M ∧
      j + 6 * productionCursorCfg.segLen < M := by
  change j < M ∧ j + 999900 < M ∧ j + 2 * 999900 < M ∧
    j + 3 * 999900 < M ∧ j + 4 * 999900 < M ∧
    j + 5 * 999900 < M ∧ j + 6 * 999900 < M
  change j < 999900 at hj
  have hM : 7 * 999900 < M := by decide
  constructor <;> omega

/-- The seven live planes and seven sink planes all fit below the `u64`
modulus, as does the exhausted-cursor sentinel. -/
theorem productionStaticPlaneWordBounds :
    productionCursorCfg.segLen + 1 < M ∧
      7 * productionCursorCfg.segLen < M ∧
      8 * productionCursorCfg.segLen < M ∧
      9 * productionCursorCfg.segLen < M ∧
      10 * productionCursorCfg.segLen < M ∧
      11 * productionCursorCfg.segLen < M ∧
      12 * productionCursorCfg.segLen < M ∧
      13 * productionCursorCfg.segLen < M := by
  change 999900 + 1 < M ∧ 7 * 999900 < M ∧
    8 * 999900 < M ∧ 9 * 999900 < M ∧
    10 * 999900 < M ∧ 11 * 999900 < M ∧
    12 * 999900 < M ∧ 13 * 999900 < M
  decide

/-- The live whole-state invariant automatically supplies the advance
premise after phase selection, cursor reset, and the physical cell prefix. -/
theorem productionAdvanceWordPre_after_mark_prefix
    (k : Nat) (s : AState) (cur : PowerCursor)
    (hround : s.regs rR < productionCursorCfg.markSteps)
    (hcur :
      let phased := arun k s (lift productionCursorCfg.markPhaseBody)
      let reset := arun k phased productionCursorCfg.markResetBody
      machinePowerCursor reset = cur)
    (hbounds : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable cur)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hviol : s.regs rViol ≤ s.regs rR)
    (hvmark : s.regs rVMark ≤ s.regs rR) :
    let phased := arun k s (lift productionCursorCfg.markPhaseBody)
    let reset := arun k phased productionCursorCfg.markResetBody
    let marked := arun k reset productionCursorCfg.markCellPrefix
    AdvanceWordPre productionCursorCfg marked productionPowerTable := by
  let c := productionCursorCfg
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let marked := arun k reset c.markCellPrefix
  change machinePowerCursor reset = cur at hcur
  change ∀ pi, pi ≤ c.tableLen →
    s.arr (pi + c.tableBase) = productionPowerTable pi at htable
  have hp := c.markPhaseBody_run k s productionCursorCfg_markSteps_lt_word
  dsimp only at hp
  have hp10 : phased.regs 10 = 1 := by
    rw [hp.1, if_pos hround]
  have hr10 : reset.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  rcases productionStaticPlaneWordBounds with
    ⟨_hseg, h7, h8, h9, h10, h11, h12, h13⟩
  have hlive : reset.regs rJ < c.segLen →
      reset.regs rJ < M ∧ reset.regs rJ + c.segLen < M ∧
      reset.regs rJ + 2 * c.segLen < M ∧
      reset.regs rJ + 3 * c.segLen < M ∧
      reset.regs rJ + 4 * c.segLen < M ∧
      reset.regs rJ + 5 * c.segLen < M ∧
      reset.regs rJ + 6 * c.segLen < M := by
    intro hj
    exact productionLivePlaneWordBounds hj
  have hprefix := c.markCellPrefix_cursor_past k reset hr10 hlive
    h7 h8 h9 h10 h11 h12 h13
  have hmCur : machinePowerCursor marked = cur := by
    exact hprefix.1.trans hcur
  have hrJ : reset.regs rJ = cur.j := congrArg PowerCursor.j hcur
  have hmPast : marked.regs 25 =
      if cur.j < c.segLen then 0 else 1 := by
    simpa [hrJ] using hprefix.2
  have hmPhase : marked.regs 10 = 1 :=
    (arun_frame k 10 c.markCellPrefix (by rfl) reset).trans hr10
  have hresetArr : reset.arr = phased.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.markResetBody phased (by rfl)
  have hmTable : ∀ pi, pi ≤ c.tableLen →
      marked.arr (pi + c.tableBase) = productionPowerTable pi := by
    intro pi hpi
    have hmark := c.markCellPrefix_table_frame k reset
      (pi + c.tableBase) hr10 (by change 0 < 999900; omega)
      hlive h7 h8 h9 h10 h11 h12 h13 (by omega)
    exact hmark.trans ((congrFun hresetArr _).trans
      ((congrFun hp.2.2.2 _).trans (htable pi hpi)))
  have frameToMarked (r : Nat)
      (hphaseF : writes r (lift c.markPhaseBody) = false)
      (hresetF : writes r c.markResetBody = false)
      (hprefixF : writes r c.markCellPrefix = false) :
      marked.regs r = s.regs r := by
    exact (arun_frame k r c.markCellPrefix hprefixF reset).trans
      ((arun_frame k r c.markResetBody hresetF phased).trans
        (arun_frame k r (lift c.markPhaseBody) hphaseF s))
  have hmR : marked.regs rR = s.regs rR :=
    frameToMarked rR (by rfl) (by rfl) (by rfl)
  have hmViol : marked.regs rViol = s.regs rViol :=
    frameToMarked rViol (by rfl) (by rfl) (by rfl)
  have hmVMark : marked.regs rVMark = s.regs rVMark :=
    frameToMarked rVMark (by rfl) (by rfl) (by rfl)
  apply productionAdvanceWordPre_of_cursorBounds marked cur hmCur hmPhase
    hmPast hbounds hmTable
  · simpa [hmR] using hround
  · rw [hmViol, hmR]
    exact hviol
  · rw [hmVMark, hmR]
    exact hvmark

/-- The first physical table entry is positive and representable, as follows
from the already-proved indexed production table bounds. -/
theorem productionTableHead_word :
    productionCursorCfg.table.headD 1 ≠ 0 ∧
      productionCursorCfg.table.headD 1 < M := by
  have hpos := productionPowerTable_pos 0
  have hle := productionPowerTable_le_10000 0
  have heq : productionCursorCfg.table.headD 1 = productionPowerTable 0 := by
    cases htable : productionCursorCfg.table with
    | nil => simp [productionPowerTable, List.headD, htable]
    | cons p ps => simp [productionPowerTable, List.headD, htable]
  constructor
  · rw [heq]
    omega
  · rw [heq]
    have hM : 10000 < M := by decide
    omega

/-- The production mark budget is nonzero.  This is proved from the symbolic
`16 + ...` lower bound and the positive word-cap branch, without evaluating
the multi-million-round budget. -/
theorem productionCursorCfg_markSteps_pos :
    0 < productionCursorCfg.markSteps := by
  change 0 < LeanCompCert.Ports.R2SegSieve.markBudget
    (Nat.sqrt 100000000) (10001 + 999900 * 100 - 1) 999900
  have hraw : 0 < LeanCompCert.Ports.R2SegSieve.rawMarkBudget
      (Nat.sqrt 100000000) (10001 + 999900 * 100 - 1) 999900 := by
    unfold LeanCompCert.Ports.R2SegSieve.rawMarkBudget
    omega
  have hcap : 0 < M - 999900 - 1 := by
    have hword : 999901 < M := by decide
    omega
  unfold LeanCompCert.Ports.R2SegSieve.markBudget
  rw [Nat.min_def]
  split <;> assumption


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve
