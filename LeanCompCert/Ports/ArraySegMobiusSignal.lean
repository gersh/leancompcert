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

theorem signalBlock_length (c : Cfg) : (signalBlock c).length = 20 := by
  rfl

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

end LeanCompCert.Ports.ArraySegMobiusSignal
