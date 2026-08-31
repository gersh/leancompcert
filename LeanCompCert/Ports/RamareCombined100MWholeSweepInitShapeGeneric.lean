import LeanCompCert.Ports.RamareCombined100MProductionInit
import LeanCompCert.Ports.RamareCombined100MLambdaPsiSweep

/-!
# Generic framing theorem for the whole-sweep initializer

The theorem in this module is deliberately abstract in the base state.  This
prevents elaboration of a concrete certified prime table while proving that
the two register-seed blocks and the finite log stores preserve the shape
initializer's table, live planes, and control registers.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def seededInitState (c : LambdaPsiSweep.Cfg)
    (seed : LambdaPsiSweep.Seed) (base : AState) : AState :=
  let logSeeded := arun 0 base
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded (storeLits c.logCells)
  arun 0 stored
    (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
      (LambdaPsiSweep.rSumU, seed.sumU),
      (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
      (LambdaPsiSweep.rPsiLR, seed.psiL.r),
      (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
      (LambdaPsiSweep.rPsiUR, seed.psiU.r)])

/-- The finite seed/store decomposition preserves machine-word closure for
any opaque word-closed base state. -/
theorem seededInitState_word
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed) (base : AState)
    (hregs : ∀ j, base.regs j < LeanCompCert.Verified.Reflect.M)
    (harr : ∀ j, base.arr j < LeanCompCert.Verified.Reflect.M) :
    let out := seededInitState c seed base
    (∀ j, out.regs j < LeanCompCert.Verified.Reflect.M) ∧
      (∀ j, out.arr j < LeanCompCert.Verified.Reflect.M) := by
  let logSeeded := arun 0 base
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded (storeLits c.logCells)
  let out := arun 0 stored
    (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
      (LambdaPsiSweep.rSumU, seed.sumU),
      (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
      (LambdaPsiSweep.rPsiLR, seed.psiL.r),
      (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
      (LambdaPsiSweep.rPsiUR, seed.psiU.r)])
  have hlog := LeanCompCert.Verified.ArrayFoldBridge.arun_word 0
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)]) base hregs harr
  have hstored := LeanCompCert.Verified.ArrayFoldBridge.arun_word 0
    (storeLits c.logCells) logSeeded hlog.1 hlog.2
  have hout := LeanCompCert.Verified.ArrayFoldBridge.arun_word 0
    (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
      (LambdaPsiSweep.rSumU, seed.sumU),
      (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
      (LambdaPsiSweep.rPsiLR, seed.psiL.r),
      (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
      (LambdaPsiSweep.rPsiUR, seed.psiU.r)]) stored hstored.1 hstored.2
  change (∀ j, out.regs j < LeanCompCert.Verified.Reflect.M) ∧
    (∀ j, out.arr j < LeanCompCert.Verified.Reflect.M)
  exact hout

theorem arun_storeLit_arr_frame_generic
    (k cell value j : Nat) (s : AState)
    (hcell : cell < LeanCompCert.Verified.Reflect.M) (hne : j ≠ cell) :
    (arun k s (storeLit cell value)).arr j = s.arr j := by
  simp [storeLit, arun, LeanCompCert.Verified.ArrayFoldBridge.astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.ArrayState.AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    Nat.mod_eq_of_lt hcell, hne]

theorem arun_storeLits_arr_frame_generic
    (k j : Nat) (s : AState) (l : List (Nat × Nat))
    (haddr : ∀ x ∈ l, x.1 < LeanCompCert.Verified.Reflect.M)
    (hne : ∀ x ∈ l, j ≠ x.1) :
    (arun k s (storeLits l)).arr j = s.arr j := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).arr j = s.arr j
      rw [ih (arun k s (storeLit x.1 x.2))
        (fun y hy => haddr y (by simp [hy]))
        (fun y hy => hne y (by simp [hy]))]
      exact arun_storeLit_arr_frame_generic k x.1 x.2 j s
        (haddr x (by simp)) (hne x (by simp))

/-- A finite literal store installs a selected cell exactly.  Only addresses
and the selected value need be word-sized; values stored at distinct cells
are irrelevant.  This avoids forcing clients with large read-only tables to
prove global value bounds merely to identify one lookup cell. -/
theorem arun_storeLits_arr_eq_of_mem_generic
    (k j value : Nat) (s : AState) (l : List (Nat × Nat))
    (haddr : ∀ x ∈ l, x.1 < LeanCompCert.Verified.Reflect.M)
    (hmem : (j, value) ∈ l)
    (hvalue : ∀ x ∈ l, x.1 = j → x.2 = value)
    (hvalueM : value < LeanCompCert.Verified.Reflect.M) :
    (arun k s (storeLits l)).arr j = value := by
  induction l generalizing s with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).arr j = value
      by_cases htail : (j, value) ∈ xs
      · exact ih (arun k s (storeLit x.1 x.2))
          (fun y hy => haddr y (by simp [hy])) htail
          (fun y hy => hvalue y (by simp [hy]))
      · have hx : x = (j, value) := by
          rcases List.mem_cons.mp hmem with hx | hx
          · exact hx.symm
          · exact (htail hx).elim
        subst x
        have hhead : (arun k s (storeLit j value)).arr j = value := by
          exact ShapeSieve.arun_storeLit_arr k j value j s
            (haddr (j, value) (by simp)) hvalueM |>.trans (by simp)
        rw [arun_storeLits_arr_frame_generic k j
          (arun k s (storeLit j value)) xs
          (fun y hy => haddr y (by simp [hy]))]
        · exact hhead
        · intro y hy heq
          have hyv := hvalue y (by simp [hy]) heq.symm
          apply htail
          cases y
          simp_all

/-- The staged lambda/psi initializer installs one selected log cell exactly
without exposing the surrounding log list or either register-seed block. -/
theorem seededInitState_logCell
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed) (base : AState)
    (j value : Nat)
    (haddr : ∀ x ∈ c.logCells,
      x.1 < LeanCompCert.Verified.Reflect.M)
    (hmem : (j, value) ∈ c.logCells)
    (hunique : ∀ x ∈ c.logCells, x.1 = j → x.2 = value)
    (hvalueM : value < LeanCompCert.Verified.Reflect.M) :
    (seededInitState c seed base).arr j = value := by
  let logSeeded := arun 0 base
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded (storeLits c.logCells)
  have hstored : stored.arr j = value :=
    arun_storeLits_arr_eq_of_mem_generic 0 j value logSeeded c.logCells
      haddr hmem hunique hvalueM
  have hout : (arun 0 stored
      (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
        (LambdaPsiSweep.rSumU, seed.sumU),
        (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
        (LambdaPsiSweep.rPsiLR, seed.psiL.r),
        (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
        (LambdaPsiSweep.rPsiUR, seed.psiU.r)])).arr = stored.arr :=
    arun_seedRegs_arr 0 stored _
  unfold seededInitState
  rw [congrFun hout j]
  exact hstored

/-- The generated lambda/psi initializer installs one selected log cell
exactly.  Its potentially large shape initializer remains opaque. -/
theorem lambdaPsi_init_logCell
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed)
    (j value : Nat)
    (haddr : ∀ x ∈ c.logCells,
      x.1 < LeanCompCert.Verified.Reflect.M)
    (hmem : (j, value) ∈ c.logCells)
    (hunique : ∀ x ∈ c.logCells, x.1 = j → x.2 = value)
    (hvalueM : value < LeanCompCert.Verified.Reflect.M) :
    (arun 0 LeanCompCert.Verified.ArrayState.initialAState
      (LambdaPsiSweep.init c seed)).arr j = value := by
  rw [LambdaPsiSweep.init,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.init]
  simp only [arun_append]
  change (seededInitState c seed
    (arun 0 LeanCompCert.Verified.ArrayState.initialAState c.shape.init)).arr j =
      value
  exact seededInitState_logCell c seed _ j value
    haddr hmem hunique hvalueM

theorem seededInitState_shape
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed) (base : AState)
    (table : Nat → Nat)
    (haddrM : ∀ x ∈ c.logCells,
      x.1 < LeanCompCert.Verified.Reflect.M)
    (haddrAway : ∀ x ∈ c.logCells, c.shape.arrayLen ≤ x.1)
    (hplaneAddr : ∀ i, i < c.shape.segLen → ∀ m, m ≤ 6 →
      i + m * c.shape.segLen < c.shape.arrayLen)
    (htableAddr : ∀ pi, pi ≤ c.shape.tableLen →
      pi + c.shape.tableBase < c.shape.arrayLen)
    (hround : base.regs rR = 0)
    (hwindow : base.regs rW = c.shape.lo)
    (htable : ∀ pi, pi ≤ c.shape.tableLen →
      base.arr (pi + c.shape.tableBase) = table pi)
    (hplane : ∀ i, i < c.shape.segLen →
      c.shape.readPlaneCell i base = emptyPlaneCell)
    (hviol : base.regs rViol = 0)
    (hvmark : base.regs rVMark = 0) :
    let s := seededInitState c seed base
    s.regs rR = 0 ∧
      s.regs rW = c.shape.lo ∧
      (∀ pi, pi ≤ c.shape.tableLen →
        s.arr (pi + c.shape.tableBase) = table pi) ∧
      (∀ i, i < c.shape.segLen →
        c.shape.readPlaneCell i s = emptyPlaneCell) ∧
      s.regs rViol = 0 ∧ s.regs rVMark = 0 := by
  let logSeeded := arun 0 base
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded (storeLits c.logCells)
  let out := arun 0 stored
    (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
      (LambdaPsiSweep.rSumU, seed.sumU),
      (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
      (LambdaPsiSweep.rPsiLR, seed.psiL.r),
      (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
      (LambdaPsiSweep.rPsiUR, seed.psiU.r)])
  have hlow (j : Nat) (hj : j < c.shape.arrayLen) :
      out.arr j = base.arr j := by
    have hlogArr : logSeeded.arr = base.arr :=
      arun_seedRegs_arr 0 base _
    have hstored : stored.arr j = logSeeded.arr j := by
      exact arun_storeLits_arr_frame_generic 0 j logSeeded c.logCells
        haddrM (fun x hx heq => by
          have haway := haddrAway x hx
          omega)
    have houtArr : out.arr = stored.arr := arun_seedRegs_arr 0 stored _
    rw [houtArr, hstored, hlogArr]
  have hreg (r : Nat)
      (hlog : LambdaPsiSweep.ablockWritesReg r
        (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
          (LambdaPsiSweep.lRLogU, seed.log.logU)]) = false)
      (hcand : LambdaPsiSweep.ablockWritesReg r
        (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
          (LambdaPsiSweep.rSumU, seed.sumU),
          (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
          (LambdaPsiSweep.rPsiLR, seed.psiL.r),
          (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
          (LambdaPsiSweep.rPsiUR, seed.psiU.r)]) = false)
      (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
      out.regs r = base.regs r := by
    exact (LambdaPsiSweep.arun_reg_frame 0 r _ stored hcand).trans
      ((arun_storeLits_regs_frame 0 r logSeeded c.logCells hr90 hr91).trans
        (LambdaPsiSweep.arun_reg_frame 0 r _ base hlog))
  change out.regs rR = 0 ∧
    out.regs rW = c.shape.lo ∧
    (∀ pi, pi ≤ c.shape.tableLen →
      out.arr (pi + c.shape.tableBase) = table pi) ∧
    (∀ i, i < c.shape.segLen →
      c.shape.readPlaneCell i out = emptyPlaneCell) ∧
    out.regs rViol = 0 ∧ out.regs rVMark = 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg rR (by rfl) (by rfl) (by decide) (by decide)).trans hround
  · exact (hreg rW (by rfl) (by rfl) (by decide) (by decide)).trans hwindow
  · intro pi hpi
    rw [hlow]
    · exact htable pi hpi
    · exact htableAddr pi hpi
  · intro i hi
    have hread : c.shape.readPlaneCell i out =
        c.shape.readPlaneCell i base := by
      apply PlaneCell.ext <;> simp only [Cfg.readPlaneCell]
      · exact hlow i (by simpa using hplaneAddr i hi 0 (by omega))
      · exact hlow (i + c.shape.segLen)
          (by simpa using hplaneAddr i hi 1 (by omega))
      · exact hlow (i + 2 * c.shape.segLen) (hplaneAddr i hi 2 (by omega))
      · exact hlow (i + 3 * c.shape.segLen) (hplaneAddr i hi 3 (by omega))
      · exact hlow (i + 4 * c.shape.segLen) (hplaneAddr i hi 4 (by omega))
      · exact hlow (i + 5 * c.shape.segLen) (hplaneAddr i hi 5 (by omega))
      · exact hlow (i + 6 * c.shape.segLen) (hplaneAddr i hi 6 (by omega))
    exact hread.trans (hplane i hi)
  · exact (hreg rViol (by rfl) (by rfl) (by decide) (by decide)).trans hviol
  · exact (hreg rVMark (by rfl) (by rfl) (by decide) (by decide)).trans hvmark

end LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant
