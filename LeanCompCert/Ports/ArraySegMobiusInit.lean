import LeanCompCert.Ports.ArraySegMobiusPrimeTableRep

/-!
# Initial terminal guard for the segmented Möbius prime table

The marking cursor deliberately loads the table entry at its selected limit
before installing the out-of-window terminal offset.  This file isolates the
last five instructions of the production initializer and proves that entry is
the positive configured sentinel.  The schedule induction can therefore keep
division-by-zero behavior out of its invariant.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve

/-- Bootstrap-prime literal stores preceding the fixed terminal guard. -/
def bootInitFrom (c : Cfg) (xs : List Nat) (n : Nat) : List AInstr :=
  xs.zipIdx n |>.flatMap fun (v, t) =>
    [ AInstr.scalar (.mov 90 (.lit (c.primeBase + t)))
    , AInstr.scalar (.mov 91 (.lit v))
    , AInstr.store 90 91 ]

def bootInit (c : Cfg) : List AInstr :=
  bootInitFrom c c.bootTable 0

theorem bootInitFrom_cons (c : Cfg) (v : Nat) (xs : List Nat) (n : Nat) :
    bootInitFrom c (v :: xs) n =
      [ AInstr.scalar (.mov 90 (.lit (c.primeBase + n)))
      , AInstr.scalar (.mov 91 (.lit v))
      , AInstr.store 90 91 ] ++ bootInitFrom c xs (n + 1) := by
  simp [bootInitFrom, List.zipIdx_cons]

/-- One literal initializer triple writes its selected cell and frames every
other cell. -/
theorem arun_initTriple (c : Cfg) (idx : Nat) (s : AState) (n v : Nat)
    (haddrM : c.primeBase + n < M) (hvM : v < M) :
    let out := arun idx s
      [ AInstr.scalar (.mov 90 (.lit (c.primeBase + n)))
      , AInstr.scalar (.mov 91 (.lit v))
      , AInstr.store 90 91 ]
    out.arr (c.primeBase + n) = v ∧
      ∀ x, x ≠ c.primeBase + n → out.arr x = s.arr x := by
  have haddrMod : (c.primeBase + n) % M = c.primeBase + n :=
    Nat.mod_eq_of_lt haddrM
  have hvMod : v % M = v := Nat.mod_eq_of_lt hvM
  constructor
  · simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, AState.writeReg,
      AState.writeArr_arr_self, haddrMod, hvMod]
  · intro x hx
    simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, AState.writeReg,
      AState.writeArr_arr_ne, haddrMod, hvMod, hx]

/-- The recursive literal-store block represents its source list exactly and
frames every array cell outside the written interval. -/
theorem arun_bootInitFrom_tablePrefix (c : Cfg) (idx : Nat) (s : AState)
    (xs : List Nat) (n : Nat)
    (hendM : c.primeBase + n + xs.length < M)
    (hvalsM : ∀ v, v ∈ xs → v < M) :
    let out := arun idx s (bootInitFrom c xs n)
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix out.arr
        (c.primeBase + n) xs ∧
      ∀ x, x < c.primeBase + n ∨
          c.primeBase + n + xs.length ≤ x → out.arr x = s.arr x := by
  induction xs generalizing n s with
  | nil => simp [bootInitFrom, arun,
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix]
  | cons v xs ih =>
      let t := arun idx s
        [ AInstr.scalar (.mov 90 (.lit (c.primeBase + n)))
        , AInstr.scalar (.mov 91 (.lit v))
        , AInstr.store 90 91 ]
      have haddrM : c.primeBase + n < M := by omega
      have hvM : v < M := hvalsM v (by simp)
      have ht := arun_initTriple c idx s n v haddrM hvM
      have htailM : c.primeBase + (n + 1) + xs.length < M := by
        simp only [List.length_cons] at hendM
        omega
      have htailVals : ∀ q, q ∈ xs → q < M := by
        intro q hq
        exact hvalsM q (by simp [hq])
      have htail := ih t (n + 1) htailM htailVals
      rw [bootInitFrom_cons, arun_append]
      constructor
      · change (arun idx t (bootInitFrom c xs (n + 1))).arr
            (c.primeBase + n) = v ∧
          LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix
            (arun idx t (bootInitFrom c xs (n + 1))).arr
            (c.primeBase + n + 1) xs
        constructor
        · exact (htail.2 (c.primeBase + n) (by left; omega)).trans ht.1
        · simpa [Nat.add_assoc] using htail.1
      · intro x hx
        have houtT : (arun idx t (bootInitFrom c xs (n + 1))).arr x =
            t.arr x := by
          apply htail.2
          rcases hx with hx | hx
          · left; omega
          · right
            simp only [List.length_cons] at hx
            omega
        rw [houtT]
        apply ht.2 x
        rcases hx with hx | hx
        · omega
        · simp only [List.length_cons] at hx
          omega

/-- The fixed tail of `Cfg.coreInit`. -/
def initTail (c : Cfg) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.primeBase + c.tableLen)))
  , .scalar (.mov 91 (.lit c.sentinel))
  , .store 90 91
  , .scalar (.mov rW (.lit 1))
  , .scalar (.mov rWrite (.lit (c.primeBase + c.bootCount))) ]

theorem coreInit_eq_boot_tail (c : Cfg) :
    c.coreInit = bootInit c ++ initTail c := by
  rfl

/-- The production initializer writes a positive guard at the exact selected
main-table limit and opens both persistent cursors at their intended values. -/
theorem arun_coreInit_terminal_guard (c : Cfg) (idx : Nat) (s : AState)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hA : c.arrayLen < M) :
    let out := arun idx s c.coreInit
    out.arr (c.primeBase + c.tableLen) = c.sentinel ∧
      out.regs rW = 1 ∧
      out.regs rWrite = c.primeBase + c.bootCount := by
  let q := arun idx s (bootInit c)
  have hendM : c.primeBase + c.tableLen < M := by
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
      Cfg.tableLen] at hA ⊢
    omega
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwriteM : c.primeBase + c.bootCount < M := by
    omega
  have hendMod : (c.primeBase + c.tableLen) % M =
      c.primeBase + c.tableLen := Nat.mod_eq_of_lt hendM
  have hsentMod : c.sentinel % M = c.sentinel :=
    Nat.mod_eq_of_lt hsentM
  have hwriteMod : (c.primeBase + c.bootCount) % M =
      c.primeBase + c.bootCount := Nat.mod_eq_of_lt hwriteM
  have honeMod : (1 : Nat) % M = 1 := by decide
  rw [coreInit_eq_boot_tail, arun_append]
  simp [initTail, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, AState.writeReg, AState.writeArr_arr_self,
    hendMod, hsentMod, hwriteMod, honeMod, rW, rWrite]

/-- The fixed initializer tail frames every non-guard array cell. -/
theorem arun_initTail_frame (c : Cfg) (idx : Nat) (s : AState)
    (x : Nat)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hA : c.arrayLen < M)
    (hx : x ≠ c.primeBase + c.tableLen) :
    (arun idx s (initTail c)).arr x = s.arr x := by
  have hendM : c.primeBase + c.tableLen < M := by
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwriteM : c.primeBase + c.bootCount < M := by
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hendMod : (c.primeBase + c.tableLen) % M =
      c.primeBase + c.tableLen := Nat.mod_eq_of_lt hendM
  have hsentMod : c.sentinel % M = c.sentinel := Nat.mod_eq_of_lt hsentM
  have hwriteMod : (c.primeBase + c.bootCount) % M =
      c.primeBase + c.bootCount := Nat.mod_eq_of_lt hwriteM
  have honeMod : (1 : Nat) % M = 1 := by decide
  simp [initTail, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, AState.writeReg,
    AState.writeArr_arr_ne, hendMod, hsentMod, hwriteMod, honeMod, hx,
    rW, rWrite]

/-- The complete production initializer establishes the exact bootstrap
prime-table representation, including its positive main-limit guard. -/
theorem arun_coreInit_tableRep (c : Cfg) (idx : Nat) (s : AState)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hbootM : ∀ p, p ∈ c.bootPrimes → p < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (arun idx s c.coreInit) c.bootPrimes := by
  let q := arun idx s (bootInit c)
  have hbootLen : c.bootPrimes.length ≤ c.tableLen := by
    simpa only [Cfg.bootCount] using hbootLe
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hendM : c.primeBase + 0 + c.bootTable.length < M := by
    simp only [Cfg.bootTable, List.length_append, List.length_singleton]
    have htableEnd : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    omega
  have hvalsM : ∀ v, v ∈ c.bootTable → v < M := by
    intro v hv
    simp only [Cfg.bootTable, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hbootM v hv
    · exact hsentM
  have hboot := arun_bootInitFrom_tablePrefix c idx s c.bootTable 0
    hendM hvalsM
  have hprefixQ :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix q.arr
        c.primeBase c.bootPrimes := by
    apply LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.of_append_left
      (qs := [c.sentinel])
    simpa [q, bootInit, Cfg.bootTable] using hboot.1
  have hguard := arun_coreInit_terminal_guard c idx s hbootLe hA
  have hdecomp : arun idx s c.coreInit = arun idx q (initTail c) := by
    rw [coreInit_eq_boot_tail, arun_append]
  constructor
  · rw [hdecomp]
    apply LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.frame_cells
      hprefixQ
    intro k hk
    apply arun_initTail_frame c idx q (c.primeBase + k) hbootLe hA
    omega
  · exact hguard.2.2
  · exact hguard.1

theorem coreInit_terminal_guard_pos (c : Cfg) : 0 < c.sentinel := by
  simp [Cfg.sentinel]

end LeanCompCert.Ports.ArraySegMobiusMark
