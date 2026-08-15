import LeanCompCert.Ports.Prop1224Cell
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Exact semantics of the Proposition 12.2.4 margin comparison

This file proves the source meaning of the literal mixed array/scalar block
that loads the accumulated `G_q` word and records a failed margin.  It is
symbolic in every word and executes no production cell.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

set_option maxRecDepth 10000
set_option maxHeartbeats 300000

/-- The source failure bit represented by the emitted strict comparison. -/
def marginFailure (pos g env : Nat) : Nat :=
  if pos < g + env then 1 else 0

/-- The literal window/final-round gate used by the emitted comparison. -/
def marginGate (c : CellCfg) (cell last : Nat) : Nat :=
  (if c.kLo ≤ cell then 1 else 0) *
    (if cell < c.kHi then 1 else 0) * last

/-- The exact failure increment of the emitted block, including its gate. -/
def gatedMarginFailure (c : CellCfg)
    (cell last pos g env : Nat) : Nat :=
  marginFailure pos g env * marginGate c cell last

theorem marginFailure_eq_zero_iff (pos g env : Nat) :
    marginFailure pos g env = 0 ↔ g + env ≤ pos := by
  simp [marginFailure, Nat.not_lt]

/-- Exact denotation for every loop body.  Inactive rounds and cells contribute
zero through `marginGate`; active final-round cells reduce to
`marginFailure`. -/
theorem marginCheckBlock_run_gated (c : CellCfg) (index : Nat) (s : AState)
    (i cell last pos g env v vm cells : Nat)
    (hi : s.regs rCi = i)
    (hcell : s.regs 122 = cell)
    (hlast : s.regs 161 = last)
    (hpos : s.regs 212 = pos)
    (henv : s.regs 217 = env)
    (hg : s.arr (i + 3 * c.segLen) = g)
    (hlast01 : last ≤ 1)
    (hv : s.regs rViol = v)
    (hvm : s.regs rVMargin = vm)
    (hcells : s.regs rCells = cells)
    (haddrM : i + 3 * c.segLen < M)
    (hkloM : c.kLo < M) (hkhiM : c.kHi < M)
    (hgeM : g + env < M)
    (hvM : v + gatedMarginFailure c cell last pos g env < M)
    (hvmM : vm + gatedMarginFailure c cell last pos g env < M)
    (hcellsM : cells + marginGate c cell last < M) :
    let out := arun index s c.marginCheckBlock
    out.regs rViol = v + gatedMarginFailure c cell last pos g env ∧
      out.regs rVMargin = vm + gatedMarginFailure c cell last pos g env ∧
      out.regs rCells = cells + marginGate c cell last := by
  have hi' : s.regs 194 = i := by simpa [rCi] using hi
  have hv' : s.regs 190 = v := by simpa [rViol] using hv
  have hvm' : s.regs 250 = vm := by simpa [rVMargin] using hvm
  have hcells' : s.regs 183 = cells := by simpa [rCells] using hcells
  have haddrMod : (i + 3 * c.segLen) % M = i + 3 * c.segLen :=
    Nat.mod_eq_of_lt haddrM
  have hkloMod : c.kLo % M = c.kLo := Nat.mod_eq_of_lt hkloM
  have hkhiMod : c.kHi % M = c.kHi := Nat.mod_eq_of_lt hkhiM
  have hgeMod : (g + env) % M = g + env := Nat.mod_eq_of_lt hgeM
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hlast01) with rfl | rfl
  · simp [gatedMarginFailure, marginGate] at hvM hvmM hcellsM
    simp [CellCfg.marginCheckBlock, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      Option.getD_some, rCi, rViol, rVMargin, rCells, hi', hcell, hlast,
      hpos, henv, hg, hv', hvm', hcells', haddrMod, hkloMod, hkhiMod,
      hgeMod, marginGate, gatedMarginFailure, marginFailure,
      Nat.mod_eq_of_lt hvM, Nat.mod_eq_of_lt hvmM,
      Nat.mod_eq_of_lt hcellsM]
  · by_cases hlo : c.kLo ≤ cell <;>
      by_cases hhi : cell < c.kHi <;>
      by_cases hfail : pos < g + env <;>
      simp [gatedMarginFailure, marginGate, marginFailure, hlo, hhi, hfail]
        at hvM hvmM hcellsM <;>
      simp [CellCfg.marginCheckBlock, arun, astep, AState.writeReg,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, rCi, rViol, rVMargin, rCells, hi', hcell, hlast,
        hpos, henv, hg, hv', hvm', hcells', haddrMod, hkloMod, hkhiMod,
        hgeMod, marginGate, gatedMarginFailure, marginFailure, hlo, hhi,
        hfail, Nat.mod_eq_of_lt hvM, Nat.mod_eq_of_lt hvmM,
        Nat.mod_eq_of_lt hcellsM]

/-- Exact denotation of `CellCfg.marginCheckBlock` on an active final-round
cell.  The hypotheses are precisely the address, literal, sum, and counter
no-wrap obligations used by these twelve instructions. -/
theorem marginCheckBlock_run (c : CellCfg) (index : Nat) (s : AState)
    (i cell pos g env v vm cells : Nat)
    (hi : s.regs rCi = i)
    (hcell : s.regs 122 = cell)
    (hlast : s.regs 161 = 1)
    (hpos : s.regs 212 = pos)
    (henv : s.regs 217 = env)
    (hg : s.arr (i + 3 * c.segLen) = g)
    (hlo : c.kLo ≤ cell) (hhi : cell < c.kHi)
    (hv : s.regs rViol = v)
    (hvm : s.regs rVMargin = vm)
    (hcells : s.regs rCells = cells)
    (haddrM : i + 3 * c.segLen < M)
    (hkloM : c.kLo < M) (hkhiM : c.kHi < M)
    (hgeM : g + env < M)
    (hvM : v + marginFailure pos g env < M)
    (hvmM : vm + marginFailure pos g env < M)
    (hcellsM : cells + 1 < M) :
    let out := arun index s c.marginCheckBlock
    out.regs rViol = v + marginFailure pos g env ∧
      out.regs rVMargin = vm + marginFailure pos g env ∧
      out.regs rCells = cells + 1 := by
  have hi' : s.regs 194 = i := by simpa [rCi] using hi
  have hv' : s.regs 190 = v := by simpa [rViol] using hv
  have hvm' : s.regs 250 = vm := by simpa [rVMargin] using hvm
  have hcells' : s.regs 183 = cells := by simpa [rCells] using hcells
  have haddrMod : (i + 3 * c.segLen) % M = i + 3 * c.segLen :=
    Nat.mod_eq_of_lt haddrM
  have hkloMod : c.kLo % M = c.kLo := Nat.mod_eq_of_lt hkloM
  have hkhiMod : c.kHi % M = c.kHi := Nat.mod_eq_of_lt hkhiM
  have hgeMod : (g + env) % M = g + env := Nat.mod_eq_of_lt hgeM
  by_cases hfail : pos < g + env
  · have hf : marginFailure pos g env = 1 := by
      simp [marginFailure, hfail]
    have hv1 : v + 1 < M := by simpa [hf] using hvM
    have hvm1 : vm + 1 < M := by simpa [hf] using hvmM
    simp [CellCfg.marginCheckBlock, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      Option.getD_some, rCi, rViol, rVMargin, rCells, hi', hcell, hlast,
      hpos, henv, hg, hlo, hhi, hv', hvm', hcells', haddrMod, hkloMod,
      hkhiMod, hgeMod, hfail, hf, hv1, hvm1, hcellsM,
      Nat.mod_eq_of_lt]
  · have hf : marginFailure pos g env = 0 := by
      simp [marginFailure, hfail]
    have hv0 : v < M := by simpa [hf] using hvM
    have hvm0 : vm < M := by simpa [hf] using hvmM
    simp [CellCfg.marginCheckBlock, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      Option.getD_some, rCi, rViol, rVMargin, rCells, hi', hcell, hlast,
      hpos, henv, hg, hlo, hhi, hv', hvm', hcells', haddrMod, hkloMod,
      hkhiMod, hgeMod, hfail, hf, hv0, hvm0, hcellsM,
      Nat.mod_eq_of_lt]

/-- If the actual emitted block leaves the aggregate failure count unchanged,
then its loaded margin words satisfy the source Boolean comparison. -/
theorem marginOK_of_marginCheckBlock_unchanged
    (c : CellCfg) (index : Nat) (s : AState)
    (i cell pos g env v vm cells : Nat)
    (hi : s.regs rCi = i)
    (hcell : s.regs 122 = cell)
    (hlast : s.regs 161 = 1)
    (hpos : s.regs 212 = pos)
    (henv : s.regs 217 = env)
    (hg : s.arr (i + 3 * c.segLen) = g)
    (hlo : c.kLo ≤ cell) (hhi : cell < c.kHi)
    (hv : s.regs rViol = v)
    (hvm : s.regs rVMargin = vm)
    (hcells : s.regs rCells = cells)
    (haddrM : i + 3 * c.segLen < M)
    (hkloM : c.kLo < M) (hkhiM : c.kHi < M)
    (hgeM : g + env < M)
    (hvM : v + marginFailure pos g env < M)
    (hvmM : vm + marginFailure pos g env < M)
    (hcellsM : cells + 1 < M)
    (hunchanged : (arun index s c.marginCheckBlock).regs rViol = v) :
    LeanCompCert.Verified.Prop1224Margin.marginOK pos g env = true := by
  have hrun := marginCheckBlock_run c index s i cell pos g env v vm cells
    hi hcell hlast hpos henv hg hlo hhi hv hvm hcells haddrM hkloM hkhiM
    hgeM hvM hvmM hcellsM
  have hzero : marginFailure pos g env = 0 := by
    omega
  simpa [LeanCompCert.Verified.Prop1224Margin.marginOK] using
    decide_eq_true ((marginFailure_eq_zero_iff pos g env).1 hzero)

#print axioms marginCheckBlock_run
#print axioms marginCheckBlock_run_gated
#print axioms marginOK_of_marginCheckBlock_unchanged

end LeanCompCert.Ports.Prop1224Cell
