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
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hn2 : 2 ≤ n) (hnCap : n ≤ c.rootCap)
    (hcapM : c.rootCap < M) (hA : c.arrayLen < M)
    (hcell : machineCell c s i = rootCellFold boot n)
    (bootBound : Nat) (hBoot : PrimeTableInv boot bootBound)
    (hbootLt : bootBound < n)
    (hcover : n < (bootBound + 1) * (bootBound + 1)) :
    RootTableInv c (arun idx s c.coreBody) (rootTableStep ps n) n := by
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
  rw [arun_coreBody_eq_rootStoreInput]
  exact rootWriteSuffix_next_eq_rootTableStep c idx
    (rootStoreInput c idx s) ps bound n huInv hFit hnext
    (by rw [hu.2.2.2.2.2.2.1, ← hn]) hu.2.2.2.2.1 hn2 hnCap
    (by rw [hn]; exact hwM) hcapM hA hbit

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
