import LeanCompCert.Ports.ArraySegMobiusCellRep
import LeanCompCert.Ports.ArraySegMobiusClear

/-!
# Main-window accumulation and clearing progress

This module follows the production core after the proved marking budget.  A
main accumulation iteration decodes one selected cell, clears exactly that
product/flag pair, frames all other live cells, and advances the window
position.  These are the local facts needed by the finite outer-window
induction.
-/

namespace LeanCompCert.Ports.ArraySegMobiusAccumulation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusCursorModel
open LeanCompCert.Ports.ArraySegMobiusCellRep
open LeanCompCert.Ports.ArraySegMobiusScheduleFold
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.MobiusResidueRealisation

private theorem rootCellState_eq {a b : RootCellState}
    (hprod : a.prod = b.prod) (hflag : a.flag = b.flag) : a = b := by
  cases a
  cases b
  simp_all

/-- In the main accumulation phase the root-collection gate is explicitly
zero in addition to the two already exposed selector outputs. -/
theorem selectorBlock_main_controls (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hRoot : c.rootSpan ≤ idx)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M) :
    let q := arun idx s (selectorBlock c)
    q.regs 9 = 1 ∧ q.regs 132 = 0 ∧ q.regs 133 = 1 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hImod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hRootmod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hrootM
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hT' : ¬s.regs 5 < c.markSteps := by
    have : c.markSteps ≤ s.regs 5 := by simpa [rR] using hT
    omega
  have hRoot' : ¬idx < c.rootSpan := by omega
  have hOne : (1 + M) % M = 1 := by decide
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rLimit, hTmod, hImod, hRootmod, h1mod, hT', hRoot', hOne]

/-- The disabled mark prefix frames selector controls and the persistent
window/table coordinates. -/
theorem signalInput_main_acc_controls (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M) :
    let q := signalInput c idx s
    q.regs rR = s.regs rR ∧ q.regs rW = s.regs rW ∧
      q.regs rWrite = s.regs rWrite ∧ q.regs 9 = 1 ∧
      q.regs 132 = 0 ∧ q.regs 133 = 1 := by
  let q := arun idx s (selectorBlock c)
  have hc := selectorBlock_main_controls c idx s hT hRoot hRM hTM
    hidxM hrootM
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact arun_reg_frame idx rR (preSignal c) s (by rfl)
  · exact arun_reg_frame idx rW (preSignal c) s (by rfl)
  · exact arun_reg_frame idx rWrite (preSignal c) s (by rfl)
  · rw [arun_reg_frame idx 9 (markPrefix c) q (by rfl)]
    exact hc.1
  · rw [arun_reg_frame idx 132 (markPrefix c) q (by rfl)]
    exact hc.2.1
  · rw [arun_reg_frame idx 133 (markPrefix c) q (by rfl)]
    exact hc.2.2

/-- The store-free decoder computes the accumulation offset and frames all
persistent controls needed by the production tail. -/
theorem signalBlock_main_acc_controls (c : Cfg) (idx : Nat) (s : AState)
    (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (h9 : s.regs 9 = 1) (h132 : s.regs 132 = 0)
    (hi : r - c.markSteps = i)
    (hT : c.markSteps ≤ r)
    (hRM : r < M) (hTM : c.markSteps < M) :
    let q := arun idx s (signalBlock c)
    q.regs rR = r ∧ q.regs rW = w ∧ q.regs rWrite = write ∧
      q.regs 9 = 1 ∧ q.regs 63 = i ∧ q.regs 132 = 0 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub : (r + (M - c.markSteps)) % M = r - c.markSteps := by
    have heq : r + (M - c.markSteps) = M + (r - c.markSteps) := by
      omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rR (signalBlock c) s (by rfl), hR]
  · rw [arun_reg_frame idx rW (signalBlock c) s (by rfl), hW]
  · rw [arun_reg_frame idx rWrite (signalBlock c) s (by rfl), hWrite]
  · rw [arun_reg_frame idx 9 (signalBlock c) s (by rfl), h9]
  · let q := arun idx s (signalIndexBlock c)
    have hq63 : q.regs 63 = i := by
      have hR5 : s.regs 5 = r := by simpa [rR] using hR
      have hiM : i < M := by omega
      have himod : i % M = i := Nat.mod_eq_of_lt hiM
      simp [q, signalIndexBlock, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg, rR, hR5, h9, hTmod,
        hsub, hi, himod]
    rw [signalBlock_eq_indexSlices, arun_append]
    rw [arun_reg_frame idx 63 (signalAfterIndex c) q (by rfl)]
    exact hq63
  · rw [arun_reg_frame idx 132 (signalBlock c) s (by rfl), h132]

/-- The accumulation tail frames every array cell except the current
product/flag pair and the disabled root-table sink. -/
theorem arun_postSignal_main_acc_frame (c : Cfg) (idx : Nat) (s : AState)
    (i x : Nat)
    (h9 : s.regs 9 = 1) (h63 : s.regs 63 = i)
    (h132 : s.regs 132 = 0)
    (hi : i < c.segLen) (hA : c.arrayLen < M)
    (hprod : x ≠ i) (hflag : x ≠ i + c.segLen)
    (hprime : x ≠ c.primeSink) :
    (arun idx s (postSignal c)).arr x = s.arr x := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hc := postBeforeClear_acc_addresses c idx s i h9 h63 hi hA
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (postBeforeClear c) s (by rfl)
  have hs0r84 : s0.regs 84 = i := hc.1
  have hs0r85 : s0.regs 85 = i + c.segLen := hc.2
  have hs2r132 : s2.regs 132 = 0 := by
    change s0.regs 132 = 0
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3arr : s3.arr = s2.arr :=
    arun_arr_frame idx (postBeforeRootStore c) s2 (by rfl)
  have hs3r141 : s3.regs 141 = c.primeSink :=
    postBeforeRootStore_mark_address c idx s2 hs2r132 hA
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  rw [hdecomp]
  rw [congrFun (arun_arr_frame idx (postAfterRootStore c) s4 (by rfl)) x]
  change s4.arr x = s.arr x
  have hp : x ≠ s3.regs 141 := by rw [hs3r141]; exact hprime
  change (s3.writeArr (s3.regs 141) (s3.regs 65)).arr x = s.arr x
  rw [AState.writeArr_arr_ne s3 _ hp, congrFun hs3arr x]
  change s2.arr x = s.arr x
  have hf : x ≠ s1.regs 85 := by
    change x ≠ s0.regs 85
    rw [hs0r85]
    exact hflag
  change (s1.writeArr (s1.regs 85) (s1.regs rZero)).arr x = s.arr x
  rw [AState.writeArr_arr_ne s1 _ hf]
  change s1.arr x = s.arr x
  have hp' : x ≠ s0.regs 84 := by rw [hs0r84]; exact hprod
  change (s0.writeArr (s0.regs 84) (s0.regs rZero)).arr x = s.arr x
  rw [AState.writeArr_arr_ne s0 _ hp']
  exact congrFun hs0arr x

/-- A complete main accumulation body frames every represented prime-table
cell, including the terminal guard. -/
theorem arun_coreBody_main_acc_tableCell (c : Cfg) (idx : Nat) (s : AState)
    (k : Nat)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hA : c.arrayLen < M) (hk : k ≤ c.tableLen) :
    (arun idx s c.coreBody).arr (c.primeBase + k) =
      s.arr (c.primeBase + k) := by
  let i := s.regs rR - c.markSteps
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let x := c.primeBase + k
  have hq := signalInput_main_acc_controls c idx s hT hRoot hRM hTM
    hidxM hrootM
  have ht := signalBlock_main_acc_controls c idx q (s.regs rR)
    (s.regs rW) (s.regs rWrite) i hq.1 hq.2.1 hq.2.2.1
    hq.2.2.2.1 hq.2.2.2.2.1 rfl hT hRM hTM
  have hxSinkProd : x ≠ c.sinkProd := by
    simp only [x, Cfg.primeBase, Cfg.sinkProd]
    omega
  have hxSinkFlag : x ≠ c.sinkProd + c.segLen := by
    simp only [x, Cfg.primeBase, Cfg.sinkProd]
    omega
  have hpre : q.arr x = s.arr x :=
    signalInput_main_frame c idx s hT hTM hA x hxSinkProd hxSinkFlag
  have htArr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hxProd : x ≠ i := by
    simp only [x, Cfg.primeBase]
    dsimp only [i]
    omega
  have hxFlag : x ≠ i + c.segLen := by
    simp only [x, Cfg.primeBase]
    dsimp only [i]
    omega
  have hxPrime : x ≠ c.primeSink := by
    simp only [x, Cfg.primeBase, Cfg.primeSink, Cfg.resultBase]
    omega
  have hpost := arun_postSignal_main_acc_frame c idx t i x
    ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 hi hA hxProd hxFlag hxPrime
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  exact hpost.trans ((congrFun htArr x).trans hpre)

/-- On the final main accumulation iteration, the disabled collection gate
keeps the table cursor fixed while the production suffix resets the position
and advances the represented window base. -/
theorem arun_postSignal_main_acc_wrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write : Nat)
    (h132 : s.regs 132 = 0)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hnext : r + 1 = c.period)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwNextM : w + c.segLen < M) :
    let out := arun idx s (postSignal c)
    out.regs rWrite = write ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hs0R : s0.regs rR = s.regs rR :=
    arun_reg_frame idx rR (postBeforeClear c) s (by rfl)
  have hs0W : s0.regs rW = s.regs rW :=
    arun_reg_frame idx rW (postBeforeClear c) s (by rfl)
  have hs0Write : s0.regs rWrite = s.regs rWrite :=
    arun_reg_frame idx rWrite (postBeforeClear c) s (by rfl)
  have hs0Control : s0.regs 132 = 0 := by
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3R : s3.regs rR = s0.regs rR :=
    arun_reg_frame idx rR (postBeforeRootStore c) s2 (by rfl)
  have hs3W : s3.regs rW = s0.regs rW :=
    arun_reg_frame idx rW (postBeforeRootStore c) s2 (by rfl)
  have hs3Write : s3.regs rWrite = s0.regs rWrite :=
    arun_reg_frame idx rWrite (postBeforeRootStore c) s2 (by rfl)
  have hs3Collect : s3.regs 137 = 0 :=
    postBeforeRootStore_mark_collect c idx s2 hs0Control
  have hs4R : s4.regs rR = r := hs3R.trans (hs0R.trans hR)
  have hs4W : s4.regs rW = w := hs3W.trans (hs0W.trans hW)
  have hs4Write : s4.regs rWrite = write :=
    hs3Write.trans (hs0Write.trans hWrite)
  have hs4Collect : s4.regs 137 = 0 := hs3Collect
  have htail := postAfterRootStore_wrap c idx s4 r w write 0 hs4R hs4W
    hs4Write hs4Collect hnext hPM hidxM hspanM hidxNe
    (by simpa using hwriteM) hwNextM
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  rw [hdecomp]
  simpa using htail

/-- One nonfinal main accumulation iteration clears its current cell, frames
every other live cell, and advances the persistent coordinates once. -/
theorem arun_coreBody_main_acc_nowrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hr : r = c.markSteps + i)
    (hiNext : i + 1 < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s c.coreBody
    machineCell c out i = ⟨0, 0⟩ ∧
      (∀ k, k < c.segLen → k ≠ i →
        machineCell c out k = machineCell c s k) ∧
      out.regs rWrite = write ∧ out.regs rR = r + 1 ∧
      out.regs rW = w := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hLPos : 0 < c.segLen := by omega
  have hTle : c.markSteps ≤ r := by omega
  have hrM : r < M := by
    simp only [Cfg.period] at hPM
    omega
  have hsRM : s.regs rR < M := by rw [hR]; exact hrM
  have hq := signalInput_main_acc_controls c idx s (by rw [hR]; exact hTle)
    hRoot hsRM hTM hidxM hrootM
  have hqR : q.regs rR = r := hq.1.trans hR
  have hqW : q.regs rW = w := hq.2.1.trans hW
  have hqWrite : q.regs rWrite = write := hq.2.2.1.trans hWrite
  have hiEq : r - c.markSteps = i := by omega
  have ht := signalBlock_main_acc_controls c idx q r w write i hqR
    hqW hqWrite hq.2.2.2.1 hq.2.2.2.2.1 hiEq hTle hrM hTM
  have htZero : t.regs rZero = 0 := by
    rw [arun_reg_frame idx rZero (signalBlock c) q (by rfl)]
    dsimp only [q]
    rw [signalInput]
    rw [arun_reg_frame idx rZero (preSignal c) s (by rfl)]
    exact hzero
  have hclear := arun_postSignal_acc_clears c idx t i ht.2.2.2.1
    ht.2.2.2.2.1 ht.2.2.2.2.2 htZero (by omega) hA
  have hprogress := arun_postSignal_mark_nowrap c idx t r w write
    ht.2.2.2.2.2 ht.1 ht.2.1 ht.2.2.1
    (by simp only [Cfg.period]; omega) hPM hidxM hrootM hidxNe
    hwriteM hwM
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  have hclearCell : machineCell c (arun idx t (postSignal c)) i =
      ⟨0, 0⟩ := by
    apply rootCellState_eq
    · exact hclear.1
    · exact hclear.2
  refine ⟨hclearCell, ?_, hprogress⟩
  intro k hk hki
  have hpre := signalInput_main_cells c idx s (by rw [hR]; exact hTle)
    hTM hA k hk
  have htArr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  apply rootCellState_eq
  · change (arun idx t (postSignal c)).arr k = s.arr k
    rw [arun_postSignal_main_acc_frame c idx t i k ht.2.2.2.1
      ht.2.2.2.2.1 ht.2.2.2.2.2 (by omega) hA hki]
    · rw [congrFun htArr, hpre.1]
    · omega
    · simp only [Cfg.primeSink, Cfg.resultBase]
      omega
  · change (arun idx t (postSignal c)).arr (k + c.segLen) =
      s.arr (k + c.segLen)
    rw [arun_postSignal_main_acc_frame c idx t i (k + c.segLen)
      ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 (by omega) hA]
    · rw [congrFun htArr, hpre.2]
    · omega
    · omega
    · simp only [Cfg.primeSink, Cfg.resultBase]
      omega

/-- The final main accumulation iteration has the same exact clearing and
framing effect as a nonfinal iteration, then wraps to the next finite window. -/
theorem arun_coreBody_main_acc_wrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hr : r = c.markSteps + i)
    (hiLast : i + 1 = c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwNextM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s c.coreBody
    machineCell c out i = ⟨0, 0⟩ ∧
      (∀ k, k < c.segLen → k ≠ i →
        machineCell c out k = machineCell c s k) ∧
      out.regs rWrite = write ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hi : i < c.segLen := by omega
  have hTle : c.markSteps ≤ r := by omega
  have hrM : r < M := by
    simp only [Cfg.period] at hPM
    omega
  have hsRM : s.regs rR < M := by rw [hR]; exact hrM
  have hq := signalInput_main_acc_controls c idx s (by rw [hR]; exact hTle)
    hRoot hsRM hTM hidxM hrootM
  have hqR : q.regs rR = r := hq.1.trans hR
  have hqW : q.regs rW = w := hq.2.1.trans hW
  have hqWrite : q.regs rWrite = write := hq.2.2.1.trans hWrite
  have hiEq : r - c.markSteps = i := by omega
  have ht := signalBlock_main_acc_controls c idx q r w write i hqR
    hqW hqWrite hq.2.2.2.1 hq.2.2.2.2.1 hiEq hTle hrM hTM
  have htZero : t.regs rZero = 0 := by
    rw [arun_reg_frame idx rZero (signalBlock c) q (by rfl)]
    dsimp only [q]
    rw [signalInput]
    rw [arun_reg_frame idx rZero (preSignal c) s (by rfl)]
    exact hzero
  have hclear := arun_postSignal_acc_clears c idx t i ht.2.2.2.1
    ht.2.2.2.2.1 ht.2.2.2.2.2 htZero hi hA
  have hnext : r + 1 = c.period := by
    simp only [Cfg.period]
    omega
  have hprogress := arun_postSignal_main_acc_wrap c idx t r w write
    ht.2.2.2.2.2 ht.1 ht.2.1 ht.2.2.1 hnext hPM hidxM hrootM
    hidxNe hwriteM hwNextM
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  have hclearCell : machineCell c (arun idx t (postSignal c)) i =
      ⟨0, 0⟩ := by
    apply rootCellState_eq
    · exact hclear.1
    · exact hclear.2
  refine ⟨hclearCell, ?_, hprogress⟩
  intro k hk hki
  have hpre := signalInput_main_cells c idx s (by rw [hR]; exact hTle)
    hTM hA k hk
  have htArr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  apply rootCellState_eq
  · change (arun idx t (postSignal c)).arr k = s.arr k
    rw [arun_postSignal_main_acc_frame c idx t i k ht.2.2.2.1
      ht.2.2.2.2.1 ht.2.2.2.2.2 hi hA hki]
    · rw [congrFun htArr, hpre.1]
    · omega
    · simp only [Cfg.primeSink, Cfg.resultBase]
      omega
  · change (arun idx t (postSignal c)).arr (k + c.segLen) =
      s.arr (k + c.segLen)
    rw [arun_postSignal_main_acc_frame c idx t i (k + c.segLen)
      ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 hi hA]
    · rw [congrFun htArr, hpre.2]
    · omega
    · omega
    · simp only [Cfg.primeSink, Cfg.resultBase]
      omega

/-- The architectural zero register remains zero through every finite body
prefix.  Keeping this fact separate avoids enlarging each local transition
statement with an otherwise unrelated framed register. -/
theorem bodyRun_rZero (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState)
    (hzero : s.regs rZero = 0) :
    (bodyRun idx c fuel s).regs rZero = 0 := by
  induction fuel with
  | zero => exact hzero
  | succ k ih =>
      rw [bodyRun_succ]
      rw [arun_reg_frame idx rZero c.coreBody (bodyRun idx c k s) (by rfl)]
      exact ih

set_option maxRecDepth 10000 in
/-- Every strict prefix of the finite accumulation half clears precisely the
consumed cells.  The remaining suffix still contains the marked values from
the input state, so its next cell can be decoded without re-running marking. -/
theorem bodyRun_main_acc_prefix (c : Cfg) (idx : Nat) (s : AState)
    (k w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hk : k < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M) :
    let out := bodyRun idx c k s
    out.regs rR = c.markSteps + k ∧ out.regs rW = w ∧
      out.regs rWrite = write ∧ out.regs rZero = 0 ∧
      (∀ j, j < k → machineCell c out j = ⟨0, 0⟩) ∧
      (∀ j, k ≤ j → j < c.segLen →
        machineCell c out j = machineCell c s j) := by
  induction k with
  | zero =>
      simp only [bodyRun_zero, Nat.add_zero]
      refine ⟨hR, hW, hWrite, hzero, ?_, ?_⟩
      · intro j hj
        omega
      · intro _ _ _
        trivial
  | succ k ih =>
      have hk' : k < c.segLen := by omega
      have hp := ih hk'
      let mid := bodyRun idx c k s
      have hstep := arun_coreBody_main_acc_nowrap c idx mid
        (c.markSteps + k) w write k hp.1 hp.2.1 hp.2.2.1 rfl hk hRoot
        hp.2.2.2.1 hTM hPM hidxM hrootM hidxNe hwriteM hwM hA
      have hstepClear := hstep.1
      have hstepFrame := hstep.2.1
      have hstepWrite := hstep.2.2.1
      have hstepR := hstep.2.2.2.1
      have hstepW := hstep.2.2.2.2
      have hstepZero := bodyRun_rZero idx c (k + 1) s hzero
      rw [bodyRun_succ]
      refine ⟨hstepR, hstepW, hstepWrite, hstepZero, ?_, ?_⟩
      · intro j hj
        by_cases hjk : j = k
        · simpa [hjk] using hstepClear
        · exact (hstepFrame j (by omega) hjk).trans
            (hp.2.2.2.2.1 j (by omega))
      · intro j hkj hjL
        exact (hstepFrame j hjL (by omega)).trans
          (hp.2.2.2.2.2 j (by omega) hjL)

set_option maxRecDepth 10000 in
/-- Every represented prime-table cell is constant throughout an arbitrary
finite accumulation prefix, including the final wrapping iteration. -/
theorem bodyRun_main_acc_tableCell (c : Cfg) (idx : Nat) (s : AState)
    (fuel k w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hfuel : fuel ≤ c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M) (hk : k ≤ c.tableLen) :
    (bodyRun idx c fuel s).arr (c.primeBase + k) =
      s.arr (c.primeBase + k) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hn : n < c.segLen := by omega
      have hp := bodyRun_main_acc_prefix c idx s n w write hR hW hWrite
        hn hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM hwM hA
      let mid := bodyRun idx c n s
      have hTle : c.markSteps ≤ mid.regs rR := by
        dsimp only [mid]
        rw [hp.1]
        omega
      have hoff : mid.regs rR - c.markSteps < c.segLen := by
        dsimp only [mid]
        rw [hp.1]
        omega
      have hmidRM : mid.regs rR < M := by
        dsimp only [mid]
        rw [hp.1]
        simp only [Cfg.period] at hPM
        omega
      have hstep := arun_coreBody_main_acc_tableCell c idx mid k hTle
        hoff hRoot hmidRM hTM hidxM hrootM hA hk
      rw [bodyRun_succ]
      exact hstep.trans (ih (by omega))

set_option maxRecDepth 10000 in
/-- Running the entire finite accumulation half clears the two live banks and
performs the ordinary window wrap. -/
theorem bodyRun_main_acc_complete (c : Cfg) (idx : Nat) (s : AState)
    (w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwNextM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    let out := bodyRun idx c c.segLen s
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rWrite = write ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen := by
  let last := c.segLen - 1
  have hlastLt : last < c.segLen := by omega
  have hp := bodyRun_main_acc_prefix c idx s last w write hR hW hWrite
    hlastLt hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM
    (by omega) hA
  let mid := bodyRun idx c last s
  have hlast : last + 1 = c.segLen := by omega
  have hstep := arun_coreBody_main_acc_wrap c idx mid
    (c.markSteps + last) w write last hp.1 hp.2.1 hp.2.2.1 rfl hlast
    hRoot hp.2.2.2.1 hTM hPM hidxM hrootM hidxNe hwriteM hwNextM hA
  have hout : bodyRun idx c c.segLen s = arun idx mid c.coreBody := by
    rw [← hlast, bodyRun_succ]
  rw [hout]
  refine ⟨?_, hstep.2.2⟩
  intro j hj
  by_cases hjLast : j = last
  · simpa [hjLast] using hstep.1
  · exact (hstep.2.1 j hj hjLast).trans
      (hp.2.2.2.2.1 j (by omega))

/-- A full accumulation half preserves the exact represented prime prefix,
its write cursor, and the positive terminal guard for the next window. -/
theorem bodyRun_main_acc_preserves_tableRep
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat) (w : Nat)
    (hRep : MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hLPos : 0 < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwNextM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    MachineTableRep c (bodyRun idx c c.segLen s) ps := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := hRep.cursor
  have hwriteM : write < M := by
    dsimp only [write]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwM : w < M := by omega
  have hcomplete := bodyRun_main_acc_complete c idx s w write hR hW
    hWrite hLPos hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM
    hwNextM hA
  refine { table := ?_, cursor := hcomplete.2.1, guard := ?_ }
  · apply TablePrefix.frame_cells hRep.table
    intro k hk
    exact bodyRun_main_acc_tableCell c idx s c.segLen k w write hR hW
      hWrite (Nat.le_refl _) hRoot hzero hTM hPM hidxM hrootM hidxNe
      hwriteM hwM hA (by omega)
  · exact (bodyRun_main_acc_tableCell c idx s c.segLen c.tableLen w write
      hR hW hWrite (Nat.le_refl _) hRoot hzero hTM hPM hidxM hrootM
      hidxNe hwriteM hwM hA (Nat.le_refl _)).trans hRep.guard

/-- At accumulation index `i`, the cell about to be decoded is still exactly
the finite root fold established by the compiled marking run. -/
theorem bodyRun_main_acc_current_cellRepresents
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (i w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hi : i < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M)
    (hmarked : machineCell c s i = rootCellFold ps (w + i)) :
    let cell := machineCell c (bodyRun idx c i s) i
    CellRepresents (rootFoldValue ps) (w + i) cell.prod cell.flag := by
  have hp := bodyRun_main_acc_prefix c idx s i w write hR hW hWrite hi
    hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM hwM hA
  have hcell := (hp.2.2.2.2.2 i (Nat.le_refl i) hi).trans hmarked
  exact cellRepresents_of_cell_eq_rootCellFold ps (w + i) _ hcell

/-- Observable accumulation theorem: the actual 111-instruction production
body emits the canonical signal of the runnable finite prime fold for the
current cell. -/
theorem readSig_bodyRun_main_acc_eq_rootFoldValue
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (i w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hi : i < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hrootM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwiM : w + i < M)
    (hA : c.arrayLen < M)
    (hmarked : machineCell c s i = rootCellFold ps (w + i)) :
    readSig (arun idx (bodyRun idx c i s) c.coreBody) =
      muSig (rootFoldValue ps) (w + i) := by
  let before := bodyRun idx c i s
  have hp := bodyRun_main_acc_prefix c idx s i w write hR hW hWrite hi
    hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM hwM hA
  have hrep := bodyRun_main_acc_current_cellRepresents c idx s ps i w write
    hR hW hWrite hi hRoot hzero hTM hPM hidxM hrootM hidxNe hwriteM
    hwM hA hmarked
  have hTle : c.markSteps ≤ before.regs rR := by
    dsimp only [before]
    rw [hp.1]
    omega
  have hoff : before.regs rR - c.markSteps < c.segLen := by
    dsimp only [before]
    rw [hp.1]
    omega
  have hRM : before.regs rR < M := by
    dsimp only [before]
    rw [hp.1]
    simp only [Cfg.period] at hPM
    omega
  have hWM : before.regs rW +
      (before.regs rR - c.markSteps) < M := by
    dsimp only [before]
    rw [hp.1, hp.2.1]
    simpa using hwiM
  have hcoord : before.regs rW +
      (before.regs rR - c.markSteps) = w + i := by
    dsimp only [before]
    rw [hp.1, hp.2.1]
    omega
  have hs := readSig_arun_coreBody_eq_muSig_of_input_cell c idx before
    (rootFoldValue ps) hTle hoff hRoot hRM hTM hidxM hrootM h2LM hWM hA
  rw [hcoord] at hs
  apply hs
  dsimp only [before]
  rw [hp.1]
  have hsub : c.markSteps + i - c.markSteps = i := by omega
  rw [hsub]
  change CellRepresents (rootFoldValue ps) (w + i)
    (machineCell c (bodyRun idx c i s) i).prod
    (machineCell c (bodyRun idx c i s) i).flag
  exact hrep

/-- End-to-end selected-cell theorem for one finite main window.  The first
`markSteps` executions are the compiled cursor schedule; the following `i`
executions are the compiled accumulation prefix; the next real production
body emits the runnable finite-fold value for `w + i`. -/
theorem readSig_compiled_main_window_cell_eq_rootFoldValue
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w write i : Nat)
    (hRep : MachineTableRep c s (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hzero : s.regs rZero = 0)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hclear : machineCell c s i = ⟨0, 0⟩)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwiM : w + i < M) :
    let marked := bodyRun idx c c.markSteps s
    readSig (arun idx (bodyRun idx c i marked) c.coreBody) =
      muSig (rootFoldValue (c.firstPrime :: ps)) (w + i) := by
  let marked := bodyRun idx c c.markSteps s
  have hLPos : 0 < c.segLen := by omega
  have hpos := bodyRun_mark_position c idx c.markSteps s w write
    (Nat.le_refl _) hR hW hWrite hLPos hTM hPM hidxM hspanM hidxNe
    hwriteM hwM
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedWrite : marked.regs rWrite = write := hpos.1
  have hmarkedZero : marked.regs rZero = 0 :=
    bodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCell : machineCell c marked i =
      rootCellFold (c.firstPrime :: ps) (w + i) :=
    bodyRun_main_cell_eq_rootCellFold c idx s ps bound w i hRep hInv
      hpsLen hR hW hmain htableLenPos htableLenM hTM hPM hidxM hspanM
      hidxNe hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM
      hwSegM hnStartM hA hbudget hi hclear
  exact readSig_bodyRun_main_acc_eq_rootFoldValue c idx marked
    (c.firstPrime :: ps) i w write hmarkedR hmarkedW hmarkedWrite hi hmain
    hmarkedZero hTM hPM hidxM hspanM hidxNe hwriteM hwM h2LM hwiM hA
    hmarkedCell

end LeanCompCert.Ports.ArraySegMobiusAccumulation
