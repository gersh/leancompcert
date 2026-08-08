import LeanCompCert.Ports.ArraySegMobiusRootSchedule
import LeanCompCert.Ports.ArraySegMobiusClear

/-!
# Root-window accumulation controls

The root half of the production segmented sieve uses the same decoder and
clear stores as a main window, but keeps `inAccRoot` enabled and
`inAccMain` disabled.  These lemmas expose the exact controls and candidate
test at the boundary immediately before the verified root-table store.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootAccumulation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusPrimeTable

private theorem rootCellState_ext {a b : RootCellState}
    (hprod : a.prod = b.prod) (hflag : a.flag = b.flag) : a = b := by
  cases a
  cases b
  simp_all

/-- Candidate one is rejected by the production lower-bound comparison,
even though its empty finite prime product is unmarked. -/
theorem postRootGate_one (c : Cfg) (idx : Nat) (s : AState)
    (h65 : s.regs 65 = 1) (hcapM : c.rootCap < M) :
    (arun idx s (postRootGate c)).regs 137 = 0 := by
  have hsub : (1 + (M - 2)) % M = M - 1 := by decide
  have hcapSubM : c.rootCap - 1 < M := by omega
  have hcapSubMod : (c.rootCap - 1) % M = c.rootCap - 1 :=
    Nat.mod_eq_of_lt hcapSubM
  have hlt : ¬M - 1 < c.rootCap - 1 := by omega
  have h65' : s.regs 65 = 1 := h65
  have h2mod : (2 : Nat) % M = 2 := by decide
  simp [postRootGate, postRootBeforeCollect, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    h65', h2mod, hsub, hcapSubMod, hlt]

/-- During root accumulation the compiled selector enables accumulation and
root collection, while disabling the main-output gate. -/
theorem selectorBlock_root_acc_controls (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M) :
    let q := arun idx s (selectorBlock c)
    q.regs 9 = 1 ∧ q.regs 132 = 1 ∧ q.regs 133 = 0 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hImod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hspanMod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hspanM
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hT' : ¬s.regs 5 < c.markSteps := by
    have : c.markSteps ≤ s.regs 5 := by simpa [rR] using hT
    omega
  have hRoot' : idx < c.rootSpan := hroot
  have hnegOne : (1 + (M - 1)) % M = 0 := by decide
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rLimit, hTmod, hImod, hspanMod, h1mod, hT', hRoot', hnegOne]

/-- The disabled marking prefix frames the persistent root controls and
window/table coordinates. -/
theorem signalInput_root_acc_controls (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M) :
    let q := signalInput c idx s
    q.regs rR = s.regs rR ∧ q.regs rW = s.regs rW ∧
      q.regs rWrite = s.regs rWrite ∧ q.regs 9 = 1 ∧
      q.regs 132 = 1 ∧ q.regs 133 = 0 := by
  let q := arun idx s (selectorBlock c)
  have hc := selectorBlock_root_acc_controls c idx s hT hroot hRM hTM
    hidxM hspanM
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

/-- The store-free decoder exposes the sequential root candidate and the
exact Boolean test used by the collection gate. -/
theorem signalBlock_root_candidate (c : Cfg) (idx : Nat) (s : AState)
    (r w i prod : Nat)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (h9 : s.regs 9 = 1)
    (hi : r - c.markSteps = i)
    (hT : c.markSteps ≤ r)
    (_hRM : r < M)
    (hTM : c.markSteps < M)
    (_hiL : i < c.segLen)
    (hwM : w + i < M)
    (hprod : s.arr i = prod) :
    let q := arun idx s (signalBlock c)
    q.regs 65 = w + i ∧ q.regs 67 = if prod = 0 then 1 else 0 := by
  have hsub : (r + (M - c.markSteps)) % M = r - c.markSteps := by
    have heq : r + (M - c.markSteps) = M + (r - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : i < M := by omega
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hsub' : (s.regs 5 + (M - c.markSteps)) % M = i := by
    rw [hR5, hsub, hi]
  have hwmod : w % M = w := Nat.mod_eq_of_lt (by omega)
  have hn : (r + (M - c.markSteps) + w) % M = w + i := by
    rw [Nat.add_mod, hsub, hi, hwmod, Nat.add_comm,
      Nat.mod_eq_of_lt hwM]
  have h1mod : (1 : Nat) % M = 1 := by decide
  set_option maxRecDepth 10000 in
  simp [signalBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, hR5, hW6, h9, hTmod, h1mod]
  exact ⟨hn, by rw [hsub, hi, hprod]⟩

/-- Besides the candidate test, the decoder frames every persistent root
coordinate needed by the table-store suffix. -/
theorem signalBlock_root_acc_controls (c : Cfg) (idx : Nat) (s : AState)
    (r w write i prod : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (h9 : s.regs 9 = 1) (h132 : s.regs 132 = 1)
    (hi : r - c.markSteps = i)
    (hT : c.markSteps ≤ r)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hiL : i < c.segLen) (hwM : w + i < M)
    (hprod : s.arr i = prod) :
    let q := arun idx s (signalBlock c)
    q.regs rR = r ∧ q.regs rW = w ∧ q.regs rWrite = write ∧
      q.regs 9 = 1 ∧ q.regs 132 = 1 ∧ q.regs 63 = i ∧
      q.regs 65 = w + i ∧
      q.regs 67 = if prod = 0 then 1 else 0 := by
  have hc := signalBlock_root_candidate c idx s r w i prod hR hW h9 hi
    hT hRM hTM hiL hwM hprod
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub : (r + (M - c.markSteps)) % M = i := by
    have heq : r + (M - c.markSteps) = M + (r - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hi]
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hiM : i < M := by omega
  have h63 : (arun idx s (signalBlock c)).regs 63 = i := by
    let q := arun idx s (signalIndexBlock c)
    have hq63 : q.regs 63 = i := by
      simp [q, signalIndexBlock, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval,
        denoteOperand, denoteOp, AState.writeReg, rR, hR5, h9, hTmod,
        hsub, Nat.mod_eq_of_lt hiM]
    rw [signalBlock_eq_indexSlices, arun_append]
    rw [arun_reg_frame idx 63 (signalAfterIndex c) q (by rfl)]
    exact hq63
  refine ⟨?_, ?_, ?_, ?_, ?_, h63, hc.1, hc.2⟩
  · rw [arun_reg_frame idx rR (signalBlock c) s (by rfl), hR]
  · rw [arun_reg_frame idx rW (signalBlock c) s (by rfl), hW]
  · rw [arun_reg_frame idx rWrite (signalBlock c) s (by rfl), hWrite]
  · rw [arun_reg_frame idx 9 (signalBlock c) s (by rfl), h9]
  · rw [arun_reg_frame idx 132 (signalBlock c) s (by rfl), h132]

/-- State immediately before the verified root-table suffix.  This is a
slice of the production body, not a replacement implementation. -/
def rootStoreInput (c : Cfg) (idx : Nat) (s : AState) : AState :=
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let u0 := arun idx t (postBeforeClear c)
  let u1 := astep idx u0 (.store 84 rZero)
  astep idx u1 (.store 85 rZero)

theorem arun_coreBody_eq_rootStoreInput (c : Cfg) (idx : Nat) (s : AState) :
    arun idx s c.coreBody =
      arun idx (rootStoreInput c idx s) (rootWriteSuffix c) := by
  rw [coreBody_eq_signalSlices, arun_append, arun_append,
    rootWriteSuffix, postSignal_eq_storeSlices]
  rfl

/-- State after the candidate store and immediately before the final scalar
cursor/window suffix. -/
def rootCursorInput (c : Cfg) (idx : Nat) (s : AState) : AState :=
  let u := rootStoreInput c idx s
  let g := arun idx u (postBeforeRootStore c)
  astep idx g (.store 141 65)

theorem arun_coreBody_eq_rootCursorInput (c : Cfg) (idx : Nat) (s : AState) :
    arun idx s c.coreBody =
      arun idx (rootCursorInput c idx s) (postAfterRootStore c) := by
  rw [arun_coreBody_eq_rootStoreInput, rootWriteSuffix, arun_append,
    arun_append]
  rfl

/-- The selector, decoder, and two clear stores preserve every represented
prime-table cell before collection chooses its one possible append cell. -/
theorem rootStoreInput_tableCell (c : Cfg) (idx : Nat) (s : AState)
    (r w write i k : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen)
    (hwM : w + i < M)
    (hA : c.arrayLen < M)
    (_hk : k ≤ c.tableLen) :
    (rootStoreInput c idx s).arr (c.primeBase + k) =
      s.arr (c.primeBase + k) := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let u0 := arun idx t (postBeforeClear c)
  let u1 := astep idx u0 (.store 84 rZero)
  let x := c.primeBase + k
  have hsRM : s.regs rR < M := by rw [hR]; exact hRM
  have hq := signalInput_root_acc_controls c idx s hT hroot hsRM hTM
    hidxM hspanM
  have ht := signalBlock_root_acc_controls c idx q r w write i (q.arr i)
    (hq.1.trans hR) (hq.2.1.trans hW) (hq.2.2.1.trans hWrite)
    hq.2.2.2.1 hq.2.2.2.2.1 hiEq (by rw [hR] at hT; exact hT)
    hRM hTM hi hwM rfl
  rcases ht with ⟨htR, htW, htWrite, ht9, ht132, ht63, ht65, ht67⟩
  have hc := postBeforeClear_acc_addresses c idx t i ht9 ht63 hi hA
  have hu0r84 : u0.regs 84 = i := hc.1
  have hu0r85 : u0.regs 85 = i + c.segLen := hc.2
  have hqarr : q.arr x = s.arr x := by
    apply signalInput_main_frame c idx s hT hTM hA x
    · simp only [x, Cfg.primeBase, Cfg.sinkProd]; omega
    · simp only [x, Cfg.primeBase, Cfg.sinkProd]; omega
  have htarr : t.arr x = q.arr x :=
    congrFun (arun_arr_frame idx (signalBlock c) q (by rfl)) x
  have hu0arr : u0.arr x = t.arr x :=
    congrFun (arun_arr_frame idx (postBeforeClear c) t (by rfl)) x
  have hxI : x ≠ i := by
    simp only [x, Cfg.primeBase]
    omega
  have hxFlag : x ≠ i + c.segLen := by
    simp only [x, Cfg.primeBase]
    omega
  have hu1arr : u1.arr x = u0.arr x := by
    change (u0.writeArr (u0.regs 84) (u0.regs rZero)).arr x = u0.arr x
    apply AState.writeArr_arr_ne
    intro heq
    rw [hu0r84] at heq
    exact hxI heq
  change (u1.writeArr (u1.regs 85) (u1.regs rZero)).arr x = s.arr x
  rw [AState.writeArr_arr_ne]
  · exact hu1arr.trans (hu0arr.trans (htarr.trans hqarr))
  · intro heq
    change x = u0.regs 85 at heq
    rw [hu0r85] at heq
    exact hxFlag heq

/-- Generic frame theorem for the decoder/clear prefix: only the current
product/flag pair and the two disabled-mark sinks may be touched. -/
theorem rootStoreInput_frame (c : Cfg) (idx : Nat) (s : AState)
    (r w write i x : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hA : c.arrayLen < M)
    (hxI : x ≠ i) (hxFlag : x ≠ i + c.segLen)
    (hxProdSink : x ≠ c.sinkProd)
    (hxFlagSink : x ≠ c.sinkProd + c.segLen) :
    (rootStoreInput c idx s).arr x = s.arr x := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let u0 := arun idx t (postBeforeClear c)
  let u1 := astep idx u0 (.store 84 rZero)
  have hsRM : s.regs rR < M := by rw [hR]; exact hRM
  have hq := signalInput_root_acc_controls c idx s hT hroot hsRM hTM
    hidxM hspanM
  have ht := signalBlock_root_acc_controls c idx q r w write i (q.arr i)
    (hq.1.trans hR) (hq.2.1.trans hW) (hq.2.2.1.trans hWrite)
    hq.2.2.2.1 hq.2.2.2.2.1 hiEq (by rw [hR] at hT; exact hT)
    hRM hTM hi hwM rfl
  rcases ht with ⟨htR, htW, htWrite, ht9, ht132, ht63, ht65, ht67⟩
  have hc := postBeforeClear_acc_addresses c idx t i ht9 ht63 hi hA
  have hu0r84 : u0.regs 84 = i := hc.1
  have hu0r85 : u0.regs 85 = i + c.segLen := hc.2
  have hqarr : q.arr x = s.arr x :=
    signalInput_main_frame c idx s hT hTM hA x hxProdSink hxFlagSink
  have htarr : t.arr x = q.arr x :=
    congrFun (arun_arr_frame idx (signalBlock c) q (by rfl)) x
  have hu0arr : u0.arr x = t.arr x :=
    congrFun (arun_arr_frame idx (postBeforeClear c) t (by rfl)) x
  have hu1arr : u1.arr x = u0.arr x := by
    change (u0.writeArr (u0.regs 84) (u0.regs rZero)).arr x = u0.arr x
    apply AState.writeArr_arr_ne
    intro heq
    rw [hu0r84] at heq
    exact hxI heq
  change (u1.writeArr (u1.regs 85) (u1.regs rZero)).arr x = s.arr x
  rw [AState.writeArr_arr_ne]
  · exact hu1arr.trans (hu0arr.trans (htarr.trans hqarr))
  · intro heq
    change x = u0.regs 85 at heq
    rw [hu0r85] at heq
    exact hxFlag heq

/-- At the root-store boundary the two cells just decoded have already been
cleared by the actual production stores. -/
theorem rootStoreInput_clears (c : Cfg) (idx : Nat) (s : AState)
    (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hzero : s.regs rZero = 0)
    (hA : c.arrayLen < M) :
    (rootStoreInput c idx s).arr i = 0 ∧
      (rootStoreInput c idx s).arr (i + c.segLen) = 0 := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let u0 := arun idx t (postBeforeClear c)
  let u1 := astep idx u0 (.store 84 rZero)
  have hsRM : s.regs rR < M := by rw [hR]; exact hRM
  have hq := signalInput_root_acc_controls c idx s hT hroot hsRM hTM
    hidxM hspanM
  have ht := signalBlock_root_acc_controls c idx q r w write i (q.arr i)
    (hq.1.trans hR) (hq.2.1.trans hW) (hq.2.2.1.trans hWrite)
    hq.2.2.2.1 hq.2.2.2.2.1 hiEq (by rw [hR] at hT; exact hT)
    hRM hTM hi hwM rfl
  rcases ht with ⟨htR, htW, htWrite, ht9, ht132, ht63, ht65, ht67⟩
  have hc := postBeforeClear_acc_addresses c idx t i ht9 ht63 hi hA
  have hu0r84 : u0.regs 84 = i := hc.1
  have hu0r85 : u0.regs 85 = i + c.segLen := hc.2
  have hu0zero : u0.regs rZero = 0 := by
    rw [arun_reg_frame idx rZero (postBeforeClear c) t (by rfl)]
    rw [arun_reg_frame idx rZero (signalBlock c) q (by rfl)]
    change (arun idx s (preSignal c)).regs rZero = 0
    rw [arun_reg_frame idx rZero (preSignal c) s (by rfl)]
    exact hzero
  have hLPos : 0 < c.segLen := by omega
  have hne : i ≠ i + c.segLen := by omega
  have hu1i : u1.arr i = 0 := by
    change (u0.writeArr (u0.regs 84) (u0.regs rZero)).arr i = 0
    rw [hu0r84, AState.writeArr_arr_self, hu0zero]
  have hu1zero : u1.regs rZero = 0 := hu0zero
  constructor
  · change (u1.writeArr (u1.regs 85) (u1.regs rZero)).arr i = 0
    have haddr : u1.regs 85 = i + c.segLen := hu0r85
    have hnot : i ≠ u1.regs 85 := by rw [haddr]; exact hne
    rw [AState.writeArr_arr_ne u1 _ hnot, hu1i]
  · change (u1.writeArr (u1.regs 85) (u1.regs rZero)).arr
        (i + c.segLen) = 0
    have haddr : u1.regs 85 = i + c.segLen := hu0r85
    rw [haddr, AState.writeArr_arr_self, hu1zero]

/-- The two clear stores do not alter a register framed by the address
prefix. -/
theorem rootStoreInput_reg_frame (c : Cfg) (idx : Nat) (s : AState)
    (reg : Nat) (hframe : (postBeforeClear c).all (avoidsReg reg) = true) :
    (rootStoreInput c idx s).regs reg =
      (arun idx (signalInput c idx s) (signalBlock c)).regs reg := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  let u0 := arun idx t (postBeforeClear c)
  have hu0 : u0.regs reg = t.regs reg :=
    arun_reg_frame idx reg (postBeforeClear c) t hframe
  change u0.regs reg = t.regs reg
  exact hu0

/-- All persistent coordinates and the finite candidate bit survive to the
root-store boundary. -/
theorem rootStoreInput_controls (c : Cfg) (idx : Nat) (s : AState)
    (r w write i prod : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hprod : (signalInput c idx s).arr i = prod) :
    let u := rootStoreInput c idx s
    u.regs rR = r ∧ u.regs rW = w ∧ u.regs rWrite = write ∧
      u.regs 9 = 1 ∧ u.regs 132 = 1 ∧ u.regs 63 = i ∧
      u.regs 65 = w + i ∧
      u.regs 67 = if prod = 0 then 1 else 0 := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hsRM : s.regs rR < M := by rw [hR]; exact hRM
  have hq := signalInput_root_acc_controls c idx s hT hroot hsRM hTM
    hidxM hspanM
  have ht := signalBlock_root_acc_controls c idx q r w write i prod
    (hq.1.trans hR) (hq.2.1.trans hW) (hq.2.2.1.trans hWrite)
    hq.2.2.2.1 hq.2.2.2.2.1 hiEq (by rw [hR] at hT; exact hT)
    hRM hTM hi hwM hprod
  rcases ht with ⟨htR, htW, htWrite, ht9, ht132, ht63, ht65, ht67⟩
  have frame (reg : Nat)
      (h : (postBeforeClear c).all (avoidsReg reg) = true) :
      (rootStoreInput c idx s).regs reg = t.regs reg :=
    rootStoreInput_reg_frame c idx s reg h
  exact ⟨(frame rR (by rfl)).trans htR,
    (frame rW (by rfl)).trans htW,
    (frame rWrite (by rfl)).trans htWrite,
    (frame 9 (by rfl)).trans ht9,
    (frame 132 (by rfl)).trans ht132,
    (frame 63 (by rfl)).trans ht63,
    (frame 65 (by rfl)).trans ht65,
    (frame 67 (by rfl)).trans ht67⟩

/-- The state just before the final cursor suffix carries the exact finite
collection bit selected by the root candidate test. -/
theorem rootCursorInput_controls (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (n r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0) :
    let t := rootCursorInput c idx s
    let collect := if unmarkedBool ps n then 1 else 0
    t.regs rR = r ∧ t.regs rW = w ∧ t.regs rWrite = write ∧
      t.regs 137 = collect := by
  let u := rootStoreInput c idx s
  let g := arun idx u (postBeforeRootStore c)
  let t := astep idx g (.store 141 65)
  let collect := if unmarkedBool ps n then 1 else 0
  let q := signalInput c idx s
  have hu := rootStoreInput_controls c idx s r w write i (q.arr i)
    hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  have hgR : g.regs rR = r := by
    rw [arun_reg_frame idx rR (postBeforeRootStore c) u (by rfl)]
    exact hu.1
  have hgW : g.regs rW = w := by
    rw [arun_reg_frame idx rW (postBeforeRootStore c) u (by rfl)]
    exact hu.2.1
  have hgWrite : g.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postBeforeRootStore c) u (by rfl)]
    exact hu.2.2.1
  have hg137 : g.regs 137 = collect := by
    change (arun idx u (postBeforeRootStore c)).regs 137 = collect
    rw [postBeforeRootStore_eq_slices, arun_append]
    let gate := arun idx u (postRootGate c)
    have hframe : (arun idx gate (postRootAddress c)).regs 137 =
        gate.regs 137 := arun_reg_frame idx 137 (postRootAddress c) gate
      (by rfl)
    rw [hframe]
    by_cases hb : unmarkedBool ps n = true
    · have hu67 : u.regs 67 = 1 := by simpa [hb] using hbit
      have hgate : gate.regs 137 = 1 :=
        postRootGate_collect c idx u n
          (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu67 hu.2.2.2.2.1
          hn2 hnCap (by rw [hn]; exact hwM) hcapM
      simpa [collect, hb] using hgate
    · have hfalse : unmarkedBool ps n = false := Bool.eq_false_iff.mpr hb
      have hu67 : u.regs 67 = 0 := by simpa [hfalse] using hbit
      have hgate : gate.regs 137 = 0 := postRootGate_marked c idx u hu67
      simpa [collect, hfalse] using hgate
  exact ⟨hgR, hgW, hgWrite, hg137⟩

/-- Candidate one reaches the cursor boundary with collection disabled by
the actual lower-bound gate, while all persistent coordinates are framed. -/
theorem rootCursorInput_one_controls (c : Cfg) (idx : Nat) (s : AState)
    (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : 1 = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hcapM : c.rootCap < M) :
    let t := rootCursorInput c idx s
    t.regs rR = r ∧ t.regs rW = w ∧ t.regs rWrite = write ∧
      t.regs 137 = 0 := by
  let u := rootStoreInput c idx s
  let g := arun idx u (postBeforeRootStore c)
  let t := astep idx g (.store 141 65)
  let q := signalInput c idx s
  have hu := rootStoreInput_controls c idx s r w write i (q.arr i)
    hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  let gate := arun idx u (postRootGate c)
  have hgate : gate.regs 137 = 0 :=
    postRootGate_one c idx u (by rw [hu.2.2.2.2.2.2.1, ← hn]) hcapM
  have hgR : g.regs rR = r := by
    change (arun idx u (postBeforeRootStore c)).regs rR = r
    rw [postBeforeRootStore_eq_slices, arun_append]
    rw [arun_reg_frame idx rR (postRootAddress c) gate (by rfl)]
    rw [arun_reg_frame idx rR (postRootGate c) u (by rfl)]
    exact hu.1
  have hgW : g.regs rW = w := by
    change (arun idx u (postBeforeRootStore c)).regs rW = w
    rw [postBeforeRootStore_eq_slices, arun_append]
    rw [arun_reg_frame idx rW (postRootAddress c) gate (by rfl)]
    rw [arun_reg_frame idx rW (postRootGate c) u (by rfl)]
    exact hu.2.1
  have hgWrite : g.regs rWrite = write := by
    change (arun idx u (postBeforeRootStore c)).regs rWrite = write
    rw [postBeforeRootStore_eq_slices, arun_append]
    rw [arun_reg_frame idx rWrite (postRootAddress c) gate (by rfl)]
    rw [arun_reg_frame idx rWrite (postRootGate c) u (by rfl)]
    exact hu.2.2.1
  have hg137 : g.regs 137 = 0 := by
    change (arun idx u (postBeforeRootStore c)).regs 137 = 0
    rw [postBeforeRootStore_eq_slices, arun_append]
    rw [arun_reg_frame idx 137 (postRootAddress c) gate (by rfl)]
    exact hgate
  exact ⟨hgR, hgW, hgWrite, hg137⟩

/-- The candidate-one body advances one position without changing either
the table cursor or the root-window base. -/
theorem arun_coreBody_root_acc_one_nowrap
    (c : Cfg) (idx : Nat) (s : AState) (r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : 1 = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hcapM : c.rootCap < M) (hnext : r + 1 < c.period)
    (hwriteM : write < M) :
    let out := arun idx s c.coreBody
    out.regs rWrite = write ∧ out.regs rR = r + 1 ∧
      out.regs rW = w := by
  let t := rootCursorInput c idx s
  have ht := rootCursorInput_one_controls c idx s r w write i hR hW
    hWrite hT hiEq hn hroot hRM hTM hidxM hspanM hi hwM hcapM
  rw [arun_coreBody_eq_rootCursorInput]
  simpa using postAfterRootStore_nowrap c idx t r w write 0 ht.1 ht.2.1
    ht.2.2.1 ht.2.2.2 hnext hPM hidxM hspanM hidxNe (by simpa)
    (by omega)

/-- An interior root-accumulation body advances one position and keeps the
window base fixed, with the write cursor increased by its finite table bit. -/
theorem arun_coreBody_root_acc_nowrap (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (n r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hnext : r + 1 < c.period)
    (hwriteNextM : write + 1 < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0) :
    let collect := if unmarkedBool ps n then 1 else 0
    let out := arun idx s c.coreBody
    out.regs rWrite = write + collect ∧ out.regs rR = r + 1 ∧
      out.regs rW = w := by
  let collect := if unmarkedBool ps n then 1 else 0
  let t := rootCursorInput c idx s
  have ht := rootCursorInput_controls c idx s ps n r w write i hR hW
    hWrite hT hiEq hn hroot hRM hTM hidxM hspanM hi hwM hn2 hnCap
    hcapM hbit
  have hwriteM : write + collect < M := by
    dsimp only [collect]
    split <;> omega
  rw [arun_coreBody_eq_rootCursorInput]
  exact postAfterRootStore_nowrap c idx t r w write collect ht.1 ht.2.1
    ht.2.2.1 ht.2.2.2 hnext hPM hidxM hspanM hidxNe hwriteM
    (by omega)

/-- The last accumulation body of an ordinary root window resets the
position and advances the root base by one segment. -/
theorem arun_coreBody_root_acc_wrap (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (n r w write i : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hnext : r + 1 = c.period)
    (hwriteNextM : write + 1 < M) (hwNextM : w + c.segLen < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0) :
    let collect := if unmarkedBool ps n then 1 else 0
    let out := arun idx s c.coreBody
    out.regs rWrite = write + collect ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen := by
  let collect := if unmarkedBool ps n then 1 else 0
  let t := rootCursorInput c idx s
  have ht := rootCursorInput_controls c idx s ps n r w write i hR hW
    hWrite hT hiEq hn hroot hRM hTM hidxM hspanM hi hwM hn2 hnCap
    hcapM hbit
  have hwriteM : write + collect < M := by
    dsimp only [collect]
    split <;> omega
  rw [arun_coreBody_eq_rootCursorInput]
  exact postAfterRootStore_wrap c idx t r w write collect ht.1 ht.2.1
    ht.2.2.1 ht.2.2.2 hnext hPM hidxM hspanM hidxNe hwriteM hwNextM

/-- On the last root body the same finite table decision is followed by the
already verified modular retargeting into the main range. -/
theorem arun_coreBody_root_acc_transition (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (n r w write i delta : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanPos : 0 < c.rootSpan)
    (hspanM : c.rootSpan < M) (hidx : idx = c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hnext : r + 1 = c.period)
    (hwriteNextM : write + 1 < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0) :
    let collect := if unmarkedBool ps n then 1 else 0
    let out := arun idx s c.coreBody
    out.regs rWrite = write + collect ∧ out.regs rR = 0 ∧
      out.regs rW = (w + ((c.segLen + delta) % M)) % M := by
  let collect := if unmarkedBool ps n then 1 else 0
  let t := rootCursorInput c idx s
  have hroot : idx < c.rootSpan := by omega
  have ht := rootCursorInput_controls c idx s ps n r w write i hR hW
    hWrite hT hiEq hn hroot hRM hTM hidxM hspanM hi hwM hn2 hnCap
    hcapM hbit
  have hwriteM : write + collect < M := by
    dsimp only [collect]
    split <;> omega
  rw [arun_coreBody_eq_rootCursorInput]
  exact postAfterRootStore_rootTransition c idx t r w write collect delta
    ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hDelta hDeltaM hnext hPM hspanPos
    hspanM hidx hwriteM

/-- Before the candidate store, the exact represented prime table and its
mathematical invariant are unchanged. -/
theorem rootStoreInput_rootTableInv (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (bound r w write i : Nat)
    (hInv : RootTableInv c s ps bound)
    (hpsLen : ps.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hA : c.arrayLen < M) :
    RootTableInv c (rootStoreInput c idx s) ps bound := by
  constructor
  · constructor
    · apply TablePrefix.frame_cells hInv.table
      intro k hk
      exact rootStoreInput_tableCell c idx s r w write i k hR hW hWrite
        hT hiEq hroot hRM hTM hidxM hspanM hi hwM hA (by omega)
    · have hframe := rootStoreInput_reg_frame c idx s rWrite (by rfl)
      rw [hframe]
      rw [arun_reg_frame idx rWrite (signalBlock c)
        (signalInput c idx s) (by rfl)]
      change (arun idx s (preSignal c)).regs rWrite = _
      rw [arun_reg_frame idx rWrite (preSignal c) s (by rfl)]
      exact hInv.cursor
    · exact (rootStoreInput_tableCell c idx s r w write i c.tableLen
        hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM hA
        (Nat.le_refl _)).trans hInv.guard
  · exact hInv.primeTable

/-- One actual root-table suffix implements the runnable finite table step.
The current `PrimeTableInv` turns the finite unmarked test into the exact
append/retain choice for the next sequential candidate. -/
theorem rootWriteSuffix_next_eq_rootTableStep (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (bound n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hFit : ps.length < c.tableLen)
    (hnext : n = bound + 1)
    (h65 : s.regs 65 = n)
    (h132 : s.regs 132 = 1)
    (hn2 : 2 ≤ n)
    (hnCap : n ≤ c.rootCap)
    (hnM : n < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hbit : s.regs 67 = if unmarkedBool ps n then 1 else 0) :
    RootTableInv c (arun idx s (rootWriteSuffix c))
      (rootTableStep ps n) n := by
  by_cases hu : unmarkedBool ps n = true
  · have hunmarked :
        LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy ps n :=
      (unmarkedBool_eq_true_iff ps n).mp hu
    have h67 : s.regs 67 = 1 := by simpa [hu] using hbit
    simpa [rootTableStep, hu] using
      hInv.append_next c idx s ps bound n hFit hnext hunmarked h65 h67
        h132 hn2 hnCap hnM hcapM hA
  · have hfalse : unmarkedBool ps n = false := by
      exact Bool.eq_false_iff.mpr hu
    have hmarked :
        ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy ps n := by
      intro hm
      exact hu ((unmarkedBool_eq_true_iff ps n).mpr hm)
    have h67 : s.regs 67 = 0 := by simpa [hfalse] using hbit
    simpa [rootTableStep, hfalse] using
      hInv.retain_next c idx s ps bound n (Nat.le_of_lt hFit) hnext
        hmarked h67 hn2 hA

/-- The same runnable append/retain choice frames every cell outside the live
table cursor and scratch sink. -/
theorem rootWriteSuffix_frame_of_rootTableStep (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (n write x : Nat)
    (h65 : s.regs 65 = n)
    (h132 : s.regs 132 = 1)
    (hWrite : s.regs rWrite = write)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hnM : n < M) (hcapM : c.rootCap < M)
    (hnextM : write + 1 < M)
    (hA : c.arrayLen < M)
    (hbit : s.regs 67 = if unmarkedBool ps n then 1 else 0)
    (hxWrite : x ≠ write) (hxSink : x ≠ c.primeSink) :
    (arun idx s (rootWriteSuffix c)).arr x = s.arr x := by
  by_cases hu : unmarkedBool ps n = true
  · have h67 : s.regs 67 = 1 := by simpa [hu] using hbit
    exact arun_rootWriteSuffix_collect_frame c idx s n write c.primeSink x
      h65 h67 h132 hWrite rfl hn2 hnCap hnM hcapM
      (by simp only [Cfg.primeSink, Cfg.arrayLen] at hA ⊢; omega)
      hnextM hxWrite
  · have hfalse : unmarkedBool ps n = false := Bool.eq_false_iff.mpr hu
    have h67 : s.regs 67 = 0 := by simpa [hfalse] using hbit
    exact (arun_rootWriteSuffix_marked_preserves c idx s write x h67
      hWrite (by omega) hA hxSink).1

/-- If the compiled range gate disables collection, the complete root-write
suffix preserves every non-sink cell and the table cursor.  Unlike the
marked-candidate theorem, this also covers candidate one, whose decoder bit
is set but whose lower-bound comparison rejects the store. -/
theorem rootWriteSuffix_disabled_preserves (c : Cfg) (idx : Nat)
    (s : AState) (write x : Nat)
    (hgate : (arun idx s (postRootGate c)).regs 137 = 0)
    (hWrite : s.regs rWrite = write)
    (hwriteM : write < M)
    (hA : c.arrayLen < M)
    (hx : x ≠ c.primeSink) :
    let out := arun idx s (rootWriteSuffix c)
    out.arr x = s.arr x ∧ out.regs rWrite = write := by
  let g := arun idx s (postRootGate c)
  let q := arun idx g (postRootAddress c)
  let t := astep idx q (.store 141 65)
  have hgWrite : g.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postRootGate c) s (by rfl)]
    exact hWrite
  have hgarr : g.arr = s.arr :=
    arun_arr_frame idx (postRootGate c) s (by rfl)
  have hq141 : q.regs 141 = c.primeSink :=
    postRootAddress_mark c idx g hgate hA
  have hq137 : q.regs 137 = 0 := by
    rw [arun_reg_frame idx 137 (postRootAddress c) g (by rfl)]
    exact hgate
  have hqWrite : q.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postRootAddress c) g (by rfl)]
    exact hgWrite
  have hqarr : q.arr = s.arr := by
    rw [arun_arr_frame idx (postRootAddress c) g (by rfl)]
    exact hgarr
  have ht137 : t.regs 137 = 0 := hq137
  have htWrite : t.regs rWrite = write := hqWrite
  rw [rootWriteSuffix, postBeforeRootStore_eq_slices, arun_append,
    arun_append, arun_append]
  exact ⟨by
    change (arun idx t (postAfterRootStore c)).arr x = s.arr x
    rw [congrFun (arun_arr_frame idx (postAfterRootStore c) t (by rfl)) x]
    change (q.writeArr (q.regs 141) (q.regs 65)).arr x = s.arr x
    rw [hq141, AState.writeArr_arr_ne q _ hx, congrFun hqarr x],
    by
      change (arun idx t (postAfterRootStore c)).regs rWrite = write
      exact postAfterRootStore_write_disabled c idx t write htWrite ht137
        hwriteM⟩

/-- A range-disabled root store retains the complete concrete table
representation, including its terminal guard. -/
theorem rootWriteSuffix_retain_of_gate_disabled
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (hRep : MachineTableRep c s ps)
    (hLen : ps.length ≤ c.tableLen)
    (hgate : (arun idx s (postRootGate c)).regs 137 = 0)
    (hA : c.arrayLen < M) :
    MachineTableRep c (arun idx s (rootWriteSuffix c)) ps := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := by
    simpa [write] using hRep.cursor
  have hwriteM : write < M := by
    have hwriteA : write < c.arrayLen := by
      dsimp [write]
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hLen ⊢
      omega
    exact Nat.lt_trans hwriteA hA
  have hbaseNe : c.primeBase ≠ c.primeSink := by
    simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase]
    omega
  have hcursor := (rootWriteSuffix_disabled_preserves c idx s write
    c.primeBase hgate hWrite hwriteM hA hbaseNe).2
  constructor
  · apply TablePrefix.frame_below hRep.table
    intro x hx
    have hxNe : x ≠ c.primeSink := by
      simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase,
        Cfg.tableLen] at hx hLen ⊢
      omega
    exact (rootWriteSuffix_disabled_preserves c idx s write x hgate
      hWrite hwriteM hA hxNe).1
  · exact hcursor
  · have hendNe : c.primeBase + c.tableLen ≠ c.primeSink := by
      simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase]
      omega
    exact (rootWriteSuffix_disabled_preserves c idx s write
      (c.primeBase + c.tableLen) hgate hWrite hwriteM hA hendNe).1.trans
        hRep.guard

/-- A complete root body with collection disabled by its range gate frames
every cell outside the decoder's clear pair and scratch sinks. -/
theorem arun_coreBody_root_acc_frame_of_gate_disabled
    (c : Cfg) (idx : Nat) (s : AState)
    (r w write i x : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwriteM : write < M) (hA : c.arrayLen < M)
    (hgate :
      (arun idx (rootStoreInput c idx s) (postRootGate c)).regs 137 = 0)
    (hxI : x ≠ i) (hxFlag : x ≠ i + c.segLen)
    (hxProdSink : x ≠ c.sinkProd)
    (hxFlagSink : x ≠ c.sinkProd + c.segLen)
    (hxPrimeSink : x ≠ c.primeSink) :
    (arun idx s c.coreBody).arr x = s.arr x := by
  let q := signalInput c idx s
  have hu := rootStoreInput_controls c idx s r w write i (q.arr i)
    hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  have hpre := rootStoreInput_frame c idx s r w write i x hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hA hxI hxFlag
    hxProdSink hxFlagSink
  rw [arun_coreBody_eq_rootStoreInput]
  exact (rootWriteSuffix_disabled_preserves c idx
    (rootStoreInput c idx s) write x hgate hu.2.2.1 hwriteM hA
    hxPrimeSink).1.trans hpre

/-- One complete root-accumulation body frames every cell other than the
current clear pair, disabled marking sinks, live table cursor, and root
scratch sink. -/
theorem arun_coreBody_root_acc_frame_of_rootTableStep
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (n r w write i x : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hnextM : write + 1 < M)
    (hA : c.arrayLen < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0)
    (hxI : x ≠ i) (hxFlag : x ≠ i + c.segLen)
    (hxProdSink : x ≠ c.sinkProd)
    (hxFlagSink : x ≠ c.sinkProd + c.segLen)
    (hxWrite : x ≠ write) (hxPrimeSink : x ≠ c.primeSink) :
    (arun idx s c.coreBody).arr x = s.arr x := by
  let q := signalInput c idx s
  let prod := q.arr i
  have hu := rootStoreInput_controls c idx s r w write i prod hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  have hpre := rootStoreInput_frame c idx s r w write i x hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hA hxI hxFlag
    hxProdSink hxFlagSink
  rw [arun_coreBody_eq_rootStoreInput]
  exact (rootWriteSuffix_frame_of_rootTableStep c idx
    (rootStoreInput c idx s) ps n write x
    (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1 hu.2.2.1
    hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA hbit
    hxWrite hxPrimeSink).trans hpre

/-- Paper-faithful bootstrap coverage: once the sequential scan has passed
the bootstrap bound, the fixed bootstrap primes and the growing exact table
make the same finite unmarked decision.  The strict square bound is the
usual segmented-sieve condition ensuring every possible small factor is in
the bootstrap table. -/
theorem unmarkedBool_boot_eq_current_next
    (boot ps : List Nat) (bootBound bound n : Nat)
    (hBoot : PrimeTableInv boot bootBound)
    (hCurrent : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n)
    (hbootLt : bootBound < n)
    (hcover : n < (bootBound + 1) * (bootBound + 1)) :
    unmarkedBool boot n = unmarkedBool ps n := by
  have hcomplete : ∀ p, LeanCompCert.Verified.PackedSieve.IsPrime p →
      p * p ≤ n → p ∈ boot := by
    intro p hp hpSq
    have hpLe : p ≤ bootBound := by
      by_cases hle : p ≤ bootBound
      · exact hle
      have hstep : bootBound + 1 ≤ p := by omega
      have hsqLe : (bootBound + 1) * (bootBound + 1) ≤ p * p :=
        Nat.mul_le_mul hstep hstep
      exact False.elim (by omega)
    exact hBoot.complete p hp hpLe
  have hbootIff : unmarkedBool boot n = true ↔
      LeanCompCert.Verified.PackedSieve.IsPrime n := by
    rw [unmarkedBool_eq_true_iff]
    constructor
    · exact LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.isPrime_of_unmarked_complete
        boot n hn2 hcomplete
    · intro hnPrime
      exact LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.unmarked_of_prime_lt
        boot n hnPrime hBoot.sound (fun p hp => by
          have := hBoot.upper p hp
          omega)
  have hcurrentIff : unmarkedBool ps n = true ↔
      LeanCompCert.Verified.PackedSieve.IsPrime n :=
    unmarkedBool_iff_prime_next hCurrent hnext hn2
  cases hb : unmarkedBool boot n <;>
    cases hp : unmarkedBool ps n <;> simp_all

/-- Every candidate already covered by a complete bootstrap table is marked.
This is the finite-computation counterpart of preloading the small primes:
the candidate has a prime divisor, and completeness puts that divisor in the
table before the root scan starts. -/
theorem not_unmarked_of_primeTableInv_le
    (ps : List Nat) (bound n : Nat)
    (hInv : PrimeTableInv ps bound)
    (hn2 : 2 ≤ n) (hnBound : n ≤ bound) :
    ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy ps n := by
  obtain ⟨p, hpPrime, hpDvd⟩ :=
    LeanCompCert.Verified.PackedSieve.exists_prime_dvd n hn2
  have hpLe : p ≤ n := Nat.le_of_dvd (by omega) hpDvd
  have hpMem : p ∈ ps := hInv.complete p hpPrime (by omega)
  intro hu
  exact hu p hpMem hpDvd

/-- The first production root candidate is exactly one.  Its finite product
is unmarked, but the compiled lower-bound comparison disables collection;
the complete body therefore clears the cell, retains the preloaded table,
and advances to candidate two. -/
theorem arun_coreBody_root_acc_one_retain
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound r w write i : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hn : 1 = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hnextPeriod : r + 1 < c.period)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hzero : s.regs rZero = 0) :
    RootTableInv c (arun idx s c.coreBody) boot bootBound ∧
      machineCell c (arun idx s c.coreBody) i = ⟨0, 0⟩ ∧
      (∀ j, j < c.segLen → j ≠ i →
        machineCell c (arun idx s c.coreBody) j = machineCell c s j) ∧
      (arun idx s c.coreBody).regs rR = r + 1 ∧
      (arun idx s c.coreBody).regs rW = w ∧
      (arun idx s c.coreBody).regs rZero = 0 := by
  let q := signalInput c idx s
  have huInv := rootStoreInput_rootTableInv c idx s boot bootBound r w
    write i hInv hLen hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM
    hi hwM hA
  have hu := rootStoreInput_controls c idx s r w write i (q.arr i) hR hW
    hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  have hgate :
      (arun idx (rootStoreInput c idx s) (postRootGate c)).regs 137 = 0 :=
    postRootGate_one c idx (rootStoreInput c idx s)
      (by rw [hu.2.2.2.2.2.2.1, ← hn]) hcapM
  have hclear := rootStoreInput_clears c idx s r w write i hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hzero hA
  have hwriteEq : write = c.primeBase + boot.length := by
    rw [← hInv.cursor, hWrite]
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    rw [hwriteEq]
    omega
  have hprogress := arun_coreBody_root_acc_one_nowrap c idx s r w write i
    hR hW hWrite hT hiEq hn hroot hRM hTM hPM hidxM hspanM hidxNe hi
    hwM hcapM hnextPeriod hwriteM
  rw [arun_coreBody_eq_rootStoreInput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact rootWriteSuffix_retain_of_gate_disabled c idx
        (rootStoreInput c idx s) boot huInv.toMachineTableRep hLen hgate hA
    · exact huInv.primeTable
  · apply rootCellState_ext
    · exact (rootWriteSuffix_disabled_preserves c idx
        (rootStoreInput c idx s) write i hgate hu.2.2.1 hwriteM hA
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).1.trans
          hclear.1
    · exact (rootWriteSuffix_disabled_preserves c idx
        (rootStoreInput c idx s) write (i + c.segLen) hgate hu.2.2.1
        hwriteM hA
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).1.trans
          hclear.2
  · intro j hj hjNe
    rw [← arun_coreBody_eq_rootStoreInput]
    apply rootCellState_ext
    · exact arun_coreBody_root_acc_frame_of_gate_disabled c idx s r w
        write i j hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM hi
        hwM hwriteM hA hgate hjNe (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
    · exact arun_coreBody_root_acc_frame_of_gate_disabled c idx s r w
        write i (j + c.segLen) hR hW hWrite hT hiEq hroot hRM hTM hidxM
        hspanM hi hwM hwriteM hA hgate (by omega) (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.1
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.2
  · rw [← arun_coreBody_eq_rootStoreInput]
    rw [arun_reg_frame idx rZero c.coreBody s (by rfl)]
    exact hzero

/-- A production root-accumulation iteration over a candidate already
covered by the preloaded bootstrap table retains that table exactly.  The
actual decoder, clear stores, disabled collection store, and cursor suffix
are all included, so this theorem supplies the early half of the root-window
induction without pretending that the preloaded table was built a second
time. -/
theorem arun_coreBody_root_acc_bootstrap_retain
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound r w write i n : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hnextPeriod : r + 1 < c.period)
    (hn2 : 2 ≤ n) (hnBoot : n ≤ bootBound)
    (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hzero : s.regs rZero = 0)
    (hcell : machineCell c s i = rootCellFold boot n) :
    RootTableInv c (arun idx s c.coreBody) boot bootBound ∧
      machineCell c (arun idx s c.coreBody) i = ⟨0, 0⟩ ∧
      (∀ j, j < c.segLen → j ≠ i →
        machineCell c (arun idx s c.coreBody) j = machineCell c s j) ∧
      (arun idx s c.coreBody).regs rR = r + 1 ∧
      (arun idx s c.coreBody).regs rW = w ∧
      (arun idx s c.coreBody).regs rZero = 0 := by
  let q := signalInput c idx s
  let prod := (rootCellFold boot n).prod
  have hqcell : machineCell c q i = rootCellFold boot n := by
    apply rootCellState_ext
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.1.trans (congrArg RootCellState.prod hcell)
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.2.trans (congrArg RootCellState.flag hcell)
  have hqprod : q.arr i = prod := by
    simpa [machineCell, prod] using congrArg RootCellState.prod hqcell
  have huInv := rootStoreInput_rootTableInv c idx s boot bootBound r w
    write i hInv hLen hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM
    hi hwM hA
  have hu := rootStoreInput_controls c idx s r w write i prod hR hW
    hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM hqprod
  have hmarked :
      ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy boot n :=
    not_unmarked_of_primeTableInv_le boot bootBound n hInv.primeTable hn2
      hnBoot
  have hz := rootCellFold_prod_eq_zero_iff_unmarked boot n
    hInv.primeTable.sound hInv.primeTable.ordered
    (by omega) (by rw [hn]; exact hwM)
  have hprodNe : prod ≠ 0 := by
    intro hp
    exact hmarked (hz.mp hp)
  have hbool : unmarkedBool boot n = false :=
    Bool.eq_false_iff.mpr (fun ht =>
      hmarked ((unmarkedBool_eq_true_iff boot n).mp ht))
  have hbit : (rootStoreInput c idx s).regs 67 = 0 := by
    rw [hu.2.2.2.2.2.2.2]
    simp [hprodNe]
  have hbit' : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool boot n then 1 else 0 := by
    simp [hbit, hbool]
  have hclear := rootStoreInput_clears c idx s r w write i hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hzero hA
  have hwriteEq : write = c.primeBase + boot.length := by
    rw [← hInv.cursor, hWrite]
  have hnextM : write + 1 < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    rw [hwriteEq]
    omega
  have hprogress := arun_coreBody_root_acc_nowrap c idx s boot n r w write
    i hR hW hWrite hT hiEq hn hroot hRM hTM hPM hidxM hspanM hidxNe hi
    hwM hn2 hnCap hcapM hnextPeriod hnextM hbit'
  rw [arun_coreBody_eq_rootStoreInput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · exact rootWriteSuffix_retain c idx (rootStoreInput c idx s) boot
        huInv.toMachineTableRep hLen hbit hA
    · exact huInv.primeTable
  · apply rootCellState_ext
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) boot n write i
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA
        hbit'
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.1
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) boot n write (i + c.segLen)
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA
        hbit'
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.2
  · intro j hj hjNe
    rw [← arun_coreBody_eq_rootStoreInput]
    apply rootCellState_ext
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s boot n r
        w write i j hR hW hWrite hT hiEq hn hroot hRM hTM hidxM
        hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit' hjNe
        (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s boot n r
        w write i (j + c.segLen) hR hW hWrite hT hiEq hn hroot hRM hTM
        hidxM hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit'
        (by omega) (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.1
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.2
  · rw [← arun_coreBody_eq_rootStoreInput]
    rw [arun_reg_frame idx rZero c.coreBody s (by rfl)]
    exact hzero

/-- Cursor-independent effects of a later sequential root candidate.  This
factorization is shared by interior, ordinary-wrap, and last-root-transition
endpoints; it exposes the exact finite candidate bit needed by the separate
cursor theorems. -/
theorem arun_coreBody_root_acc_next_table_cells
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bound r w write i n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hFit : ps.length < c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hn : n = w + i) (hnext : n = bound + 1)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hzero : s.regs rZero = 0)
    (hcell : machineCell c s i = rootCellFold boot n)
    (bootBound : Nat) (hBoot : PrimeTableInv boot bootBound)
    (hbootLt : bootBound < n)
    (hcover : n < (bootBound + 1) * (bootBound + 1)) :
    RootTableInv c (arun idx s c.coreBody) (rootTableStep ps n) n ∧
      machineCell c (arun idx s c.coreBody) i = ⟨0, 0⟩ ∧
      (∀ j, j < c.segLen → j ≠ i →
        machineCell c (arun idx s c.coreBody) j = machineCell c s j) ∧
      (rootStoreInput c idx s).regs 67 =
        (if unmarkedBool ps n then 1 else 0) ∧
      (arun idx s c.coreBody).regs rZero = 0 := by
  let q := signalInput c idx s
  let prod := (rootCellFold boot n).prod
  have hqcell : machineCell c q i = rootCellFold boot n := by
    apply rootCellState_ext
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.1.trans (congrArg RootCellState.prod hcell)
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.2.trans (congrArg RootCellState.flag hcell)
  have hqprod : q.arr i = prod := by
    simpa [machineCell, prod] using congrArg RootCellState.prod hqcell
  have huInv := rootStoreInput_rootTableInv c idx s ps bound r w write i
    hInv (Nat.le_of_lt hFit) hR hW hWrite hT hiEq hroot hRM hTM hidxM
    hspanM hi hwM hA
  have hu := rootStoreInput_controls c idx s r w write i prod hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hqprod
  have hz := rootCellFold_prod_eq_zero_iff_unmarked boot n hBoot.sound
    hBoot.ordered (by omega) (by rw [hn]; exact hwM)
  have hscan := unmarkedBool_boot_eq_current_next boot ps bootBound bound n
    hBoot hInv.primeTable hnext hn2 hbootLt hcover
  have hboot :
      (if prod = 0 then 1 else 0) =
        (if unmarkedBool boot n then 1 else 0) := by
    have hb := unmarkedBool_eq_true_iff boot n
    by_cases hp : prod = 0
    · have hum : LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy
          boot n := hz.mp hp
      have hbool : unmarkedBool boot n = true := hb.mpr hum
      simp [hp, hbool]
    · have hnot : ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy
          boot n := by
        intro hum
        exact hp (hz.mpr hum)
      have hbool : unmarkedBool boot n = false :=
        Bool.eq_false_iff.mpr (fun ht => hnot (hb.mp ht))
      simp [hp, hbool]
  have hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0 := by
    rw [hu.2.2.2.2.2.2.2, hboot, hscan]
  have hclear := rootStoreInput_clears c idx s r w write i hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hzero hA
  have hwriteEq : write = c.primeBase + ps.length := by
    rw [← hInv.cursor, hWrite]
  have hnextM : write + 1 < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    rw [hwriteEq]
    omega
  rw [arun_coreBody_eq_rootStoreInput]
  refine ⟨?_, ?_, ?_, hbit, ?_⟩
  · exact rootWriteSuffix_next_eq_rootTableStep c idx
      (rootStoreInput c idx s) ps bound n huInv hFit hnext
      (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1 hn2 hnCap
      (by rw [hn]; exact hwM) hcapM hA hbit
  · apply rootCellState_ext
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) ps n write i
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA hbit
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.1
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) ps n write (i + c.segLen)
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA hbit
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.2
  · intro j hj hjNe
    rw [← arun_coreBody_eq_rootStoreInput]
    apply rootCellState_ext
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s ps n r
        w write i j hR hW hWrite hT hiEq hn hroot hRM hTM hidxM
        hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit hjNe
        (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s ps n r
        w write i (j + c.segLen) hR hW hWrite hT hiEq hn hroot hRM hTM
        hidxM hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit
        (by omega) (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
  · rw [← arun_coreBody_eq_rootStoreInput]
    rw [arun_reg_frame idx rZero c.coreBody s (by rfl)]
    exact hzero

/-- A later sequential candidate at an ordinary root-window endpoint performs
the same finite table/cell step and the production wrap to the next root
base. -/
theorem arun_coreBody_root_acc_next_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bound r w write i n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hFit : ps.length < c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hn : n = w + i) (hnext : n = bound + 1)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwrap : r + 1 = c.period) (hwNextM : w + c.segLen < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hzero : s.regs rZero = 0)
    (hcell : machineCell c s i = rootCellFold boot n)
    (bootBound : Nat) (hBoot : PrimeTableInv boot bootBound)
    (hbootLt : bootBound < n)
    (hcover : n < (bootBound + 1) * (bootBound + 1)) :
    RootTableInv c (arun idx s c.coreBody) (rootTableStep ps n) n ∧
      machineCell c (arun idx s c.coreBody) i = ⟨0, 0⟩ ∧
      (∀ j, j < c.segLen → j ≠ i →
        machineCell c (arun idx s c.coreBody) j = machineCell c s j) ∧
      (arun idx s c.coreBody).regs rR = 0 ∧
      (arun idx s c.coreBody).regs rW = w + c.segLen ∧
      (arun idx s c.coreBody).regs rZero = 0 := by
  have hc := arun_coreBody_root_acc_next_table_cells c idx s boot ps bound
    r w write i n hInv hFit hR hW hWrite hT hiEq hn hnext hroot hRM hTM
    hidxM hspanM hi hwM hn2 hnCap hcapM hA hzero hcell bootBound hBoot
    hbootLt hcover
  have hwriteEq : write = c.primeBase + ps.length := by
    rw [← hInv.cursor, hWrite]
  have hwriteNextM : write + 1 < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    rw [hwriteEq]
    omega
  have hp := arun_coreBody_root_acc_wrap c idx s ps n r w write i hR hW
    hWrite hT hiEq hn hroot hRM hTM hPM hidxM hspanM hidxNe hi hwM
    hn2 hnCap hcapM hwrap hwriteNextM hwNextM hc.2.2.2.1
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hp.2.1, hp.2.2, hc.2.2.2.2⟩

/-- A complete production root-accumulation iteration performs one runnable
finite prime-table step.  The explicit strict-square premise is the
paper-faithful bootstrap coverage condition. -/
theorem arun_coreBody_root_acc_next_eq_rootTableStep
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bound r w write i n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hFit : ps.length < c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hn : n = w + i) (hnext : n = bound + 1)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hnextPeriod : r + 1 < c.period)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hzero : s.regs rZero = 0)
    (hcell : machineCell c s i = rootCellFold boot n)
    (bootBound : Nat) (hBoot : PrimeTableInv boot bootBound)
    (hbootLt : bootBound < n)
    (hcover : n < (bootBound + 1) * (bootBound + 1)) :
    RootTableInv c (arun idx s c.coreBody) (rootTableStep ps n) n ∧
      machineCell c (arun idx s c.coreBody) i = ⟨0, 0⟩ ∧
      (∀ j, j < c.segLen → j ≠ i →
        machineCell c (arun idx s c.coreBody) j = machineCell c s j) ∧
      (arun idx s c.coreBody).regs rR = r + 1 ∧
      (arun idx s c.coreBody).regs rW = w ∧
      (arun idx s c.coreBody).regs rZero = 0 := by
  let q := signalInput c idx s
  let prod := (rootCellFold boot n).prod
  have hqcell : machineCell c q i = rootCellFold boot n := by
    apply rootCellState_ext
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.1.trans (congrArg RootCellState.prod hcell)
    · have hcells := signalInput_main_cells c idx s hT hTM hA i hi
      exact hcells.2.trans (congrArg RootCellState.flag hcell)
  have hqprod : q.arr i = prod := by
    simpa [machineCell, prod] using congrArg RootCellState.prod hqcell
  have huInv := rootStoreInput_rootTableInv c idx s ps bound r w write i
    hInv (Nat.le_of_lt hFit) hR hW hWrite hT hiEq hroot hRM hTM hidxM
    hspanM hi hwM hA
  have hu := rootStoreInput_controls c idx s r w write i prod hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hqprod
  have hz := rootCellFold_prod_eq_zero_iff_unmarked boot n hBoot.sound
    hBoot.ordered
    (by omega) (by rw [hn]; exact hwM)
  have hscan := unmarkedBool_boot_eq_current_next boot ps bootBound bound n
    hBoot hInv.primeTable hnext hn2 hbootLt hcover
  have hboot :
      (if prod = 0 then 1 else 0) =
        (if unmarkedBool boot n then 1 else 0) := by
    have hb := unmarkedBool_eq_true_iff boot n
    by_cases hp : prod = 0
    · have hum : LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy
          boot n := hz.mp hp
      have hbool : unmarkedBool boot n = true := hb.mpr hum
      simp [hp, hbool]
    · have hnot : ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy
          boot n := by
        intro hum
        exact hp (hz.mpr hum)
      have hbool : unmarkedBool boot n = false :=
        Bool.eq_false_iff.mpr (fun ht => hnot (hb.mp ht))
      simp [hp, hbool]
  have hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0 := by
    rw [hu.2.2.2.2.2.2.2, hboot, hscan]
  have hclear := rootStoreInput_clears c idx s r w write i hR hW hWrite
    hT hiEq hroot hRM hTM hidxM hspanM hi hwM hzero hA
  have hwriteEq : write = c.primeBase + ps.length := by
    rw [← hInv.cursor, hWrite]
  have hnextM : write + 1 < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    rw [hwriteEq]
    omega
  have hprogress := arun_coreBody_root_acc_nowrap c idx s ps n r w write i
    hR hW hWrite hT hiEq hn hroot hRM hTM hPM hidxM hspanM hidxNe hi
    hwM hn2 hnCap hcapM hnextPeriod hnextM hbit
  rw [arun_coreBody_eq_rootStoreInput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootWriteSuffix_next_eq_rootTableStep c idx
      (rootStoreInput c idx s) ps bound n huInv hFit hnext
      (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1 hn2 hnCap
      (by rw [hn]; exact hwM) hcapM hA hbit
  · apply rootCellState_ext
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) ps n write i
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA hbit
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.1
    · exact (rootWriteSuffix_frame_of_rootTableStep c idx
        (rootStoreInput c idx s) ps n write (i + c.segLen)
        (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1
        hu.2.2.1 hn2 hnCap (by rw [hn]; exact hwM) hcapM hnextM hA hbit
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)).trans hclear.2
  · intro j hj hjNe
    rw [← arun_coreBody_eq_rootStoreInput]
    apply rootCellState_ext
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s ps n r
        w write i j hR hW hWrite hT hiEq hn hroot hRM hTM hidxM
        hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit hjNe
        (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
    · exact arun_coreBody_root_acc_frame_of_rootTableStep c idx s ps n r
        w write i (j + c.segLen) hR hW hWrite hT hiEq hn hroot hRM hTM
        hidxM hspanM hi hwM hn2 hnCap hcapM hnextM hA hbit
        (by omega) (by omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by simp only [Cfg.sinkProd]; omega)
        (by rw [hwriteEq]; simp only [Cfg.primeBase]; omega)
        (by simp only [Cfg.primeSink, Cfg.resultBase]; omega)
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.1
  · rw [← arun_coreBody_eq_rootStoreInput]
    exact hprogress.2.2
  · rw [← arun_coreBody_eq_rootStoreInput]
    rw [arun_reg_frame idx rZero c.coreBody s (by rfl)]
    exact hzero

/-- For a cell produced by the finite bootstrap-prime fold, the compiled
candidate bit is exactly the runnable `UnmarkedBy` predicate. -/
theorem signalBlock_root_candidate_unmarked (c : Cfg) (idx : Nat)
    (s : AState) (r w i : Nat) (boot : List Nat)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (h9 : s.regs 9 = 1)
    (hi : r - c.markSteps = i)
    (hT : c.markSteps ≤ r)
    (hRM : r < M)
    (hTM : c.markSteps < M)
    (hiL : i < c.segLen)
    (hwM : w + i < M)
    (hcell : machineCell c s i = rootCellFold boot (w + i))
    (hprime : ∀ p, p ∈ boot → LeanCompCert.Verified.PackedSieve.IsPrime p)
    (hordered : boot.Pairwise (· < ·))
    (hnPos : 0 < w + i) :
    let q := arun idx s (signalBlock c)
    (q.regs 67 = 1 ↔
      LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy boot
        (w + i)) := by
  have hc := signalBlock_root_candidate c idx s r w i
    (rootCellFold boot (w + i)).prod hR hW h9 hi hT hRM hTM hiL hwM
    (by simpa [machineCell] using congrArg RootCellState.prod hcell)
  dsimp only
  rw [hc.2]
  have hz := rootCellFold_prod_eq_zero_iff_unmarked boot (w + i)
    hprime hordered hnPos hwM
  by_cases hp : (rootCellFold boot (w + i)).prod = 0
  · simp [hp, hz.mp hp]
  · have hu : ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy
        boot (w + i) := by
      intro hu
      exact hp (hz.mpr hu)
    simp [hp, hu]

end LeanCompCert.Ports.ArraySegMobiusRootAccumulation
