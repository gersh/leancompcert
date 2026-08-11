import LeanCompCert.Ports.R2SegMarkingAdvanceValue

/-! # Next-multiple offset for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markAdvanceOffsetInstrs (c : R2Cfg) : List Instr :=
  let L := c.segLen
  let K := c.tableLen
  [ .binop 75 .urem (.reg rW) (.reg rQ)
  , .binop 76 .sub (.reg rQ) (.reg 75)
  , .binop 77 .urem (.reg 76) (.reg rQ)
  , .binop 78 .eq (.reg rPi) (.lit K)
  , .binop 79 .sub (.lit 1) (.reg 78)
  , .binop 80 .mul (.reg 78) (.lit (L + 1))
  , .binop 81 .mul (.reg 79) (.reg 77)
  , .binop 82 .add (.reg 80) (.reg 81)
  , .binop 83 .mul (.reg 52) (.reg 82)
  , .binop 84 .mul (.reg 64) (.reg 65)
  , .binop rJ .add (.reg 83) (.reg 84) ]

def markAdvanceOffsetBody (c : R2Cfg) : List AInstr :=
  lift (markAdvanceOffsetInstrs c)

theorem markAdvanceOffsetBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 85).take (markAdvanceOffsetBody c).length =
      markAdvanceOffsetBody c := by
  rfl

def startOffset (windowBase power : Nat) : Nat :=
  (power - windowBase % power) % power

def R2Cfg.selectedOffset (c : R2Cfg)
    (pi windowBase power : Nat) : Nat :=
  if pi = c.tableLen then c.segLen + 1 else startOffset windowBase power

def nextOffset (active selected fallback : Nat) : Nat :=
  active * selected + (1 - active) * fallback

def eqBitR2 (a b : Nat) : Nat := if a = b then 1 else 0

/-- Compute the first in-window multiple of a newly selected power, the
sentinel offset when the table is exhausted, or the already computed next
multiple when the cursor stays on its current power.  Positivity of `rQ` is
explicit for both remainder instructions. -/
theorem markAdvanceOffsetBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hactive : s.regs 52 ≤ 1) (hnot : s.regs 64 = 1 - s.regs 52)
    (hq0 : s.regs rQ ≠ 0) (hq : s.regs rQ < M)
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M)
    (hfallback : s.regs 65 < M) :
    let selected := c.selectedOffset (s.regs rPi) (s.regs rW)
      (s.regs rQ)
    let value := nextOffset (s.regs 52) selected (s.regs 65)
    let out := arun k s (markAdvanceOffsetBody c)
    out.regs 75 = s.regs rW % s.regs rQ ∧
      out.regs 77 = startOffset (s.regs rW) (s.regs rQ) ∧
      out.regs 78 = eqBitR2 (s.regs rPi) c.tableLen ∧
      out.regs 82 = selected ∧ out.regs rJ = value ∧
      out.regs rPi = s.regs rPi ∧ out.regs rQ = s.regs rQ ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  have hq3 : s.regs 3 ≠ 0 := by simpa [rQ] using hq0
  have hq3M : s.regs 3 < M := by simpa [rQ] using hq
  have hrem : s.regs 6 % s.regs 3 < s.regs 3 :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hq3)
  have hremM : s.regs 6 % s.regs 3 < M := Nat.lt_trans hrem hq3M
  have hremMod : (s.regs 6 % s.regs 3) % M =
      s.regs 6 % s.regs 3 := Nat.mod_eq_of_lt hremM
  have hsubM : s.regs 3 - s.regs 6 % s.regs 3 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq3M
  have hsubWord :
      (s.regs 3 + (M - s.regs 6 % s.regs 3)) % M =
        s.regs 3 - s.regs 6 % s.regs 3 := by
    have hrew : s.regs 3 + (M - s.regs 6 % s.regs 3) =
        M + (s.regs 3 - s.regs 6 % s.regs 3) := by omega
    rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt hsubM]
  have hoff : (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 < M :=
    Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hq3)) hq3M
  have hoffMod :
      ((s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3) % M =
        (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 :=
    Nat.mod_eq_of_lt hoff
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have hL1Mod : (c.segLen + 1) % M = c.segLen + 1 :=
    Nat.mod_eq_of_lt hL1
  have hfMod : s.regs 65 % M = s.regs 65 :=
    Nat.mod_eq_of_lt hfallback
  have h1M : (1 : Nat) < M := by decide
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt h1M
  have hsubOne : 1 + (M - 1) = M := by omega
  simp only [markAdvanceOffsetBody, arun_lift]
  by_cases ha : s.regs 52 = 0
  · have h64 : s.regs 64 = 1 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp' : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [markAdvanceOffsetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.selectedOffset, startOffset,
        nextOffset, eqBitR2, ha, h64, hp', hq3, hremMod, hsubWord,
        hoffMod, hKMod, hL1Mod, hfMod, honeMod, hsubOne,
        rPi, rQ, rW, rJ]
    · have hp' : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [markAdvanceOffsetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.selectedOffset, startOffset,
        nextOffset, eqBitR2, ha, h64, hp', hq3, hremMod, hsubWord,
        hoffMod, hKMod, hfMod, honeMod, rPi, rQ, rW, rJ]
  · have ha1 : s.regs 52 = 1 := by omega
    have h64 : s.regs 64 = 0 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp' : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [markAdvanceOffsetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.selectedOffset, startOffset,
        nextOffset, eqBitR2, ha1, h64, hp', hq3, hremMod, hsubWord,
        hoffMod, hKMod, hL1Mod, honeMod, hsubOne,
        rPi, rQ, rW, rJ]
    · have hp' : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [markAdvanceOffsetInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, R2Cfg.selectedOffset, startOffset,
        nextOffset, eqBitR2, ha1, h64, hp', hq3, hremMod, hsubWord,
        hoffMod, hKMod, honeMod, rPi, rQ, rW, rJ]

#print axioms markAdvanceOffsetBody_run

end LeanCompCert.Ports.R2SegSieve
