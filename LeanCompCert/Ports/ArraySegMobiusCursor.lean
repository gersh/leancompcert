import LeanCompCert.Ports.ArraySegMobiusMarkStart

/-!
# Production segmented-Möbius cursor transition

The marking stores are followed by 26 scalar/load instructions.  We slice
that block along its semantic phases so cursor proofs do not ask the
simplifier to normalize the complete production body at once.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Decide whether the cursor advances: instructions 39--40. -/
def cursorGate (c : Cfg) : List AInstr := (roundAfterFlag c).take 2

/-- Increment and clamp the prime-table cursor: instructions 41--`rPi`. -/
def cursorIndex (c : Cfg) : List AInstr := ((roundAfterFlag c).drop 2).take 6

/-- Form and load the selected prime-table address. -/
def cursorLoad (c : Cfg) : List AInstr := ((roundAfterFlag c).drop 8).take 2

/-- Select the old or newly loaded prime. -/
def cursorPrime (c : Cfg) : List AInstr := ((roundAfterFlag c).drop 10).take 5

/-- Compute the first multiple of the selected prime in this window. -/
def cursorOffset (c : Cfg) : List AInstr := ((roundAfterFlag c).drop 15).take 3

/-- Select the next multiple or the table-exhausted sentinel. -/
def cursorFinish (c : Cfg) : List AInstr := (roundAfterFlag c).drop 18

theorem roundAfterFlag_eq_cursorSlices (c : Cfg) :
    roundAfterFlag c = cursorGate c ++ cursorIndex c ++ cursorLoad c ++
      cursorPrime c ++ cursorOffset c ++ cursorFinish c := by
  rfl

/-- A live mark does not advance the prime cursor. -/
theorem cursorGate_marked (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1) (hinR : s.regs 21 = 1) :
    let q := arun idx s (cursorGate c)
    q.regs 40 = 0 ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rJ = s.regs rJ ∧
      q.regs rW = s.regs rW ∧ q.regs rLimit = s.regs rLimit := by
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  simp [cursorGate, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hgate, hinR, hOne]

/-- Once the current multiple has left the window, a marking iteration asks
the cursor to advance by one. -/
theorem cursorGate_exhausted (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1) (hinR : s.regs 21 = 0) :
    let q := arun idx s (cursorGate c)
    q.regs 40 = 1 ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rJ = s.regs rJ ∧
      q.regs rW = s.regs rW ∧ q.regs rLimit = s.regs rLimit := by
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [cursorGate, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hgate, hinR, h1mod]

/-- With advance zero, the clamped table index is unchanged. -/
theorem cursorIndex_hold (c : Cfg) (idx : Nat) (s : AState)
    (hadvance : s.regs 40 = 0)
    (hpiLe : s.regs rPi ≤ s.regs rLimit)
    (hlimitM : s.regs rLimit < M) :
    let q := arun idx s (cursorIndex c)
    q.regs rPi = s.regs rPi ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hpiM : s.regs rPi < M := by omega
  have hpiMod : s.regs rPi % M = s.regs rPi := Nat.mod_eq_of_lt hpiM
  have hpiMod2 : s.regs 2 % M = s.regs 2 := by simpa [rPi] using hpiMod
  have hle2 : s.regs 2 ≤ s.regs 128 := by
    simpa [rPi, rLimit] using hpiLe
  have hnotRaw2 : ¬s.regs 128 < s.regs 2 := by omega
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [cursorIndex, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance,
    hnotRaw2, hpiMod2, h1mod]

/-- With advance one and a nonterminal cursor, the production clamp selects
the following table entry exactly. -/
theorem cursorIndex_advance (c : Cfg) (idx : Nat) (s : AState)
    (hadvance : s.regs 40 = 1)
    (hpiLt : s.regs rPi < s.regs rLimit)
    (hlimitM : s.regs rLimit < M) :
    let q := arun idx s (cursorIndex c)
    q.regs rPi = s.regs rPi + 1 ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hnextLe : s.regs rPi + 1 ≤ s.regs rLimit := by omega
  have hnextM : s.regs rPi + 1 < M := by omega
  have hnextMod : (s.regs rPi + 1) % M = s.regs rPi + 1 :=
    Nat.mod_eq_of_lt hnextM
  have hnextMod2 : (s.regs 2 + 1) % M = s.regs 2 + 1 := by
    simpa [rPi] using hnextMod
  have hnextLe2 : s.regs 2 + 1 ≤ s.regs 128 := by
    simpa [rPi, rLimit] using hnextLe
  have hnotRaw2 : ¬s.regs 128 < s.regs 2 + 1 := by omega
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [cursorIndex, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance,
    hnotRaw2, hnextMod2, h1mod]

/-- The selected cursor is translated to the exact prime-table address and
loaded from the production array. -/
theorem cursorLoad_table (c : Cfg) (idx : Nat) (s : AState) (pi : Nat)
    (hpi : s.regs rPi = pi)
    (hpiLe : pi ≤ c.tableLen)
    (hA : c.arrayLen < M) :
    let q := arun idx s (cursorLoad c)
    q.regs 47 = s.arr (c.primeBase + pi) ∧
      q.regs rPi = pi ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit ∧ q.regs 40 = s.regs 40 := by
  have hbaseM : c.primeBase < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    rw [Cfg.primeBase]
    omega
  have haddrM : c.primeBase + pi < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    rw [Cfg.primeBase]
    omega
  have hbaseMod : c.primeBase % M = c.primeBase := Nat.mod_eq_of_lt hbaseM
  have haddrMod : (pi + c.primeBase) % M = c.primeBase + pi := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  have hpi2 : s.regs 2 = pi := by simpa [rPi] using hpi
  simp [cursorLoad, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hpi2, hbaseMod,
    haddrMod]

/-- With advance zero, prime selection keeps the old prime and records its
next multiple. -/
theorem cursorPrime_hold (c : Cfg) (idx : Nat) (s : AState) (p j : Nat)
    (hadvance : s.regs 40 = 0)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hpM : p < M)
    (hnextM : j + p < M) :
    let q := arun idx s (cursorPrime c)
    q.regs rP = p ∧ q.regs 49 = j + p ∧ q.regs 48 = 1 ∧
      q.regs rPi = s.regs rPi ∧ q.regs rJ = j ∧
      q.regs rW = s.regs rW ∧ q.regs rLimit = s.regs rLimit := by
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hnextMod : (j + p) % M = j + p := Nat.mod_eq_of_lt hnextM
  have hp3 : s.regs 3 = p := by simpa [rP] using hp
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [cursorPrime, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance, hp3, hj4,
    hpMod, hnextMod, h1mod]

/-- With advance one, prime selection installs the table value just loaded.
The old-prime next-multiple scratch is intentionally not exposed. -/
theorem cursorPrime_advance (c : Cfg) (idx : Nat) (s : AState) (p : Nat)
    (hadvance : s.regs 40 = 1)
    (hload : s.regs 47 = p)
    (hpM : p < M) :
    let q := arun idx s (cursorPrime c)
    q.regs rP = p ∧ q.regs 48 = 0 ∧
      q.regs rPi = s.regs rPi ∧ q.regs rJ = s.regs rJ ∧
      q.regs rW = s.regs rW ∧ q.regs rLimit = s.regs rLimit ∧
      q.regs 40 = 1 := by
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  simp [cursorPrime, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance, hload, hpMod,
    hOne]

/-- The three production remainder instructions compute the paper-standard
first multiple `(p - w % p) % p`. -/
theorem cursorOffset_first (c : Cfg) (idx : Nat) (s : AState) (w p : Nat)
    (hw : s.regs rW = w)
    (hp : s.regs rP = p)
    (hpPos : 0 < p)
    (hpM : p < M) :
    let q := arun idx s (cursorOffset c)
    q.regs 54 = firstOffset w p ∧ q.regs rP = p ∧
      q.regs rPi = s.regs rPi ∧ q.regs rJ = s.regs rJ ∧
      q.regs rW = w ∧ q.regs rLimit = s.regs rLimit ∧
      q.regs 40 = s.regs 40 ∧ q.regs 48 = s.regs 48 ∧
      q.regs 49 = s.regs 49 := by
  have hpNe : p ≠ 0 := Nat.ne_of_gt hpPos
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hremLt : w % p < p := Nat.mod_lt _ hpPos
  have hremM : (w % p) % M = w % p := Nat.mod_eq_of_lt (by omega)
  have hsubRaw : (p + (M - w % p)) % M = p - w % p := by
    have hsplit : p + (M - w % p) = M + (p - w % p) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hoffM : ((p - w % p) % p) % M = (p - w % p) % p := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpPos) (Nat.le_of_lt hpM)
  have hp3 : s.regs 3 = p := by simpa [rP] using hp
  have hw6 : s.regs 6 = w := by simpa [rW] using hw
  simp [cursorOffset, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, firstOffset, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hp3, hw6, hpNe,
    hremM, hsubRaw, hoffM]

/-- Without cursor advance, the final selector uses the old-prime next
multiple regardless of whether the cursor index equals its limit. -/
theorem cursorFinish_hold (c : Cfg) (idx : Nat) (s : AState) (next : Nat)
    (hadvance : s.regs 40 = 0)
    (hkeep : s.regs 48 = 1)
    (hnext : s.regs 49 = next)
    (hnextM : next < M) :
    let q := arun idx s (cursorFinish c)
    q.regs rJ = next ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hnextMod : next % M = next := Nat.mod_eq_of_lt hnextM
  simp [cursorFinish, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance, hkeep,
    hnext, hnextMod]

/-- Advancing to a nonterminal table entry selects its first window offset. -/
theorem cursorFinish_advance (c : Cfg) (idx : Nat) (s : AState) (off : Nat)
    (hadvance : s.regs 40 = 1)
    (hdrop : s.regs 48 = 0)
    (hoff : s.regs 54 = off)
    (hne : s.regs rPi ≠ s.regs rLimit)
    (hoffM : off < M) :
    let q := arun idx s (cursorFinish c)
    q.regs rJ = off ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hoffMod : off % M = off := Nat.mod_eq_of_lt hoffM
  have hpiNe : s.regs 2 ≠ s.regs 128 := by simpa [rPi, rLimit] using hne
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [cursorFinish, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance, hdrop, hoff,
    hpiNe, hoffMod, h1mod]

/-- Advancing to the cursor limit installs the explicit out-of-window
sentinel `segLen + 1`. -/
theorem cursorFinish_terminal (c : Cfg) (idx : Nat) (s : AState)
    (hadvance : s.regs 40 = 1)
    (hdrop : s.regs 48 = 0)
    (hterminal : s.regs rPi = s.regs rLimit)
    (hLM : c.segLen + 1 < M) :
    let q := arun idx s (cursorFinish c)
    q.regs rJ = c.segLen + 1 ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hLmod : (c.segLen + 1) % M = c.segLen + 1 :=
    Nat.mod_eq_of_lt hLM
  have hpiEq : s.regs 2 = s.regs 128 := by
    simpa [rPi, rLimit] using hterminal
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  simp [cursorFinish, roundAfterFlag, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rW, rLimit, hadvance, hdrop,
    hpiEq, hLmod, hOne]

end LeanCompCert.Ports.ArraySegMobiusMark
