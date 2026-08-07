import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Ports.MobiusResidueModel
import LeanCompCert.Ports.MobiusResidueWindow
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Isolated signal decoder of the segmented Möbius sieve

The production segmented loop is long because it marks cells, advances a
prime cursor, decodes a cell, clears it, and bootstraps the prime table in one
branchless block.  The residue only consumes four registers.  This file
extracts, rather than retranscribes, the twenty-instruction slice that writes
those registers and proves its exact ordinary-arithmetic meaning.

The remaining number-theoretic refinement can now target the two marked cells
`prod` and `flag`: once they satisfy `CellRepresents`, the emitted registers
are exactly `muSig`.  No compiler or instruction semantics remain in that
obligation.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSignal

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Instructions 66 through 85 of `coreBody`, obtained by list slicing. -/
def signalBlock (c : Cfg) : List AInstr :=
  (c.coreBody.drop 66).take 20

def preSignal (c : Cfg) : List AInstr := c.coreBody.take 66

def postSignal (c : Cfg) : List AInstr := c.coreBody.drop 86

def signalInput (c : Cfg) (idx : Nat) (s : AState) : AState :=
  arun idx s (preSignal c)

theorem signalBlock_length (c : Cfg) : (signalBlock c).length = 20 := by
  rfl

theorem coreBody_eq_signalSlices (c : Cfg) :
    c.coreBody = preSignal c ++ signalBlock c ++ postSignal c := by
  rfl

/-- Register-frame predicate for an array instruction. -/
def avoidsReg (r : Nat) : AInstr → Bool
  | .scalar (.mov d _) => d != r
  | .scalar (.binop d _ _ _) => d != r
  | .load d _ => d != r
  | .store _ _ => true

theorem arun_reg_frame (k r : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all (avoidsReg r) = true → (arun k s l).regs r = s.regs r := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr =>
          cases instr with
          | mov d src =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg, Ne.symm h.1]
          | binop d op lhs rhs =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg, Ne.symm h.1]
      | load d a =>
          simp only [avoidsReg, bne_iff_ne] at h
          simp [astep, AState.writeReg, Ne.symm h.1]
      | store a v => rfl

/-- The tail clears cells, bootstraps primes, and advances cursors, but does
not overwrite any of the four registers observed by a Möbius residue. -/
theorem readSig_arun_postSignal (c : Cfg) (idx : Nat) (s : AState) :
    readSig (arun idx s (postSignal c)) = readSig s := by
  have h65 := arun_reg_frame idx 65 (postSignal c) s (by rfl)
  have h79 := arun_reg_frame idx 79 (postSignal c) s (by rfl)
  have h80 := arun_reg_frame idx 80 (postSignal c) s (by rfl)
  have h133 := arun_reg_frame idx 133 (postSignal c) s (by rfl)
  simp only [readSig, h65, h79, h80, h133]

/-- Transparent decoding of the product/parity cells read by the extracted
block.  The `% M` operations are exactly the word reductions performed by the
machine instructions; they are deliberately visible to the subsequent pure
cell-refinement proof. -/
def decodeCell (n prod flag : Nat) : Sig :=
  let prod1 := (prod + if prod = 0 then 1 else 0) % M
  let sq := ((flag >>> 1) % M &&& 1) % M
  let parity := ((flag &&& 1) % M ^^^
    (if prod1 = n then 0 else 1)) % M
  let squarefree := (1 + (M - sq)) % M
  ⟨n,
    (squarefree * ((1 + (M - parity)) % M)) % M,
    (squarefree * parity) % M,
    1⟩

/-- The pure cell property the segmented-sieve mathematics must establish. -/
def CellRepresents (mu : Nat → Int) (n prod flag : Nat) : Prop :=
  decodeCell n prod flag = muSig mu n

/-- The extracted block's two loads are in bounds in the production two-bank
layout.  Scalar instructions in this slice contain no partial division or
remainder operations, so these are its complete definedness conditions. -/
theorem signalBlock_defined (arrayLen : Nat) (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hmain : s.regs 9 = 1)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (harray : c.segLen + c.segLen ≤ arrayLen) :
    AllDefined arrayLen idx s (signalBlock c) := by
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M = s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hiLM : s.regs rR - c.markSteps + c.segLen < M := by omega
  have hiA : s.regs rR - c.markSteps < arrayLen := by omega
  have hiLA : s.regs rR - c.markSteps + c.segLen < arrayLen := by omega
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub' :
      (s.regs 5 + (M - c.markSteps)) % M = s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hiM' : s.regs 5 - c.markSteps < M := by simpa [rR] using hiM
  have hiLM' : s.regs 5 - c.markSteps + c.segLen < M := by
    simpa [rR] using hiLM
  have hiA' : s.regs 5 - c.markSteps < arrayLen := by simpa [rR] using hiA
  have hiLA' : s.regs 5 - c.markSteps + c.segLen < arrayLen := by
    simpa [rR] using hiLA
  set_option maxRecDepth 10000 in
  simp [signalBlock, Cfg.coreBody, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, hmain, hTmod, hsub', Nat.mod_eq_of_lt hiM',
    Nat.mod_eq_of_lt hiLM', hiA', hiLA']

/-- Partial array-machine denotation of the extracted decoder block. -/
theorem denote_signalBlock (arrayLen : Nat) (c : Cfg) (idx : Nat) (s : AState)
    (hdef : AllDefined arrayLen idx s (signalBlock c)) :
    denoteAInstrs arrayLen idx s (signalBlock c) =
      some (arun idx s (signalBlock c)) :=
  denoteAInstrs_eq_arun arrayLen idx (signalBlock c) s hdef

/-- Exact meaning of the extracted twenty instructions during a main-phase
accumulation iteration. -/
theorem readSig_arun_signalBlock (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    readSig (arun idx s (signalBlock c)) =
      decodeCell (s.regs rW + (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps + c.segLen)) := by
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M = s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hiLM : s.regs rR - c.markSteps + c.segLen < M := by
    omega
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hLmod : c.segLen % M = c.segLen := by
    apply Nat.mod_eq_of_lt
    omega
  have hWmod : s.regs rW % M = s.regs rW := by
    apply Nat.mod_eq_of_lt
    omega
  have hidxL :
      (s.regs rR + (M - c.markSteps) + c.segLen) % M =
        s.regs rR - c.markSteps + c.segLen := by
    rw [Nat.add_mod, hsub, hLmod, Nat.mod_eq_of_lt hiLM]
  have hn :
      (s.regs rR + (M - c.markSteps) + s.regs rW) % M =
        s.regs rW + (s.regs rR - c.markSteps) := by
    rw [Nat.add_mod, hsub, hWmod]
    rw [Nat.add_comm, Nat.mod_eq_of_lt hWM]
  have hsub' :
      (s.regs 5 + (M - c.markSteps)) % M = s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hidxL' :
      (s.regs 5 + (M - c.markSteps) + c.segLen) % M =
        s.regs 5 - c.markSteps + c.segLen := by
    simpa [rR] using hidxL
  have hn' :
      (s.regs 5 + (M - c.markSteps) + s.regs 6) % M =
        s.regs 6 + (s.regs 5 - c.markSteps) := by
    simpa [rR, rW] using hn
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hiM' : s.regs 5 - c.markSteps < M := by simpa [rR] using hiM
  have hiLM' : s.regs 5 - c.markSteps + c.segLen < M := by
    simpa [rR] using hiLM
  have hWM' : s.regs 6 + (s.regs 5 - c.markSteps) < M := by
    simpa [rR, rW] using hWM
  have hni :
      (s.regs 5 - c.markSteps + s.regs 6) % M =
        s.regs 6 + (s.regs 5 - c.markSteps) := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hWM']
  have hmod2 (n : Nat) : n % 2 % M = n % 2 := by
    apply Nat.mod_eq_of_lt
    have : n % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  set_option maxRecDepth 10000 in
  simp [signalBlock, Cfg.coreBody, decodeCell, readSig, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, hmain, hTmod, hsub', Nat.mod_eq_of_lt hiM',
    Nat.mod_eq_of_lt hiLM', hni, hmod2, h1mod, hgate]
  constructor <;> rfl

/-- Once the two cells have their mathematical Möbius meaning, the extracted
machine block emits the canonical signal consumed by every verified residue. -/
theorem readSig_eq_muSig_of_cell (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hcell : CellRepresents mu
      (s.regs rW + (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps + c.segLen))) :
    readSig (arun idx s (signalBlock c)) =
      muSig mu (s.regs rW + (s.regs rR - c.markSteps)) := by
  rw [readSig_arun_signalBlock c idx s hT hi hgate hmain hRM hTM h2LM hWM]
  exact hcell

/-- End-to-end partial denotation of the extracted block, including both load
bounds and its exact observable result. -/
theorem denote_signalBlock_readSig (arrayLen : Nat) (c : Cfg)
    (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (harray : c.segLen + c.segLen ≤ arrayLen)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    (denoteAInstrs arrayLen idx s (signalBlock c)).map readSig =
      some (decodeCell (s.regs rW + (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps + c.segLen))) := by
  rw [denote_signalBlock arrayLen c idx s
    (signalBlock_defined arrayLen c idx s hT hi hmain hRM hTM h2LM harray)]
  simp only [Option.map_some]
  rw [readSig_arun_signalBlock c idx s hT hi hgate hmain hRM hTM h2LM hWM]

/-- Observable meaning of the complete 111-instruction core, factored through
the state immediately before its decoder slice.  The sole remaining
algorithmic obligation is to establish the hypotheses (and ultimately
`CellRepresents`) for `signalInput`. -/
theorem readSig_arun_coreBody (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ (signalInput c idx s).regs rR)
    (hi : (signalInput c idx s).regs rR - c.markSteps < c.segLen)
    (hgate : (signalInput c idx s).regs 133 = 1)
    (hmain : (signalInput c idx s).regs 9 = 1)
    (hRM : (signalInput c idx s).regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : (signalInput c idx s).regs rW +
      ((signalInput c idx s).regs rR - c.markSteps) < M) :
    readSig (arun idx s c.coreBody) =
      decodeCell
        ((signalInput c idx s).regs rW +
          ((signalInput c idx s).regs rR - c.markSteps))
        ((signalInput c idx s).arr
          ((signalInput c idx s).regs rR - c.markSteps))
        ((signalInput c idx s).arr
          ((signalInput c idx s).regs rR - c.markSteps + c.segLen)) := by
  rw [coreBody_eq_signalSlices, arun_append, arun_append,
    readSig_arun_postSignal]
  exact readSig_arun_signalBlock c idx (signalInput c idx s)
    hT hi hgate hmain hRM hTM h2LM hWM

end LeanCompCert.Ports.ArraySegMobiusSignal
