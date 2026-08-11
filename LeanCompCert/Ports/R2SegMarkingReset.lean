import LeanCompCert.Ports.R2SegMarkingPhase

/-! # Window-start cursor mux for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markResetInstrs (c : R2Cfg) : List Instr :=
  let q0 := c.q0
  let w0 := c.w0
  [ .binop 10 .eq (.reg rR) (.lit 0)
  , .binop 11 .sub (.lit 1) (.reg 10)
  , .binop 12 .urem (.reg rW) (.lit q0)
  , .binop 13 .sub (.lit q0) (.reg 12)
  , .binop 16 .urem (.reg 13) (.lit q0)
  , .binop rPi .mul (.reg 11) (.reg rPi)
  , .binop 17 .mul (.reg 10) (.lit q0)
  , .binop 18 .mul (.reg 11) (.reg rQ)
  , .binop rQ .add (.reg 17) (.reg 18)
  , .binop 19 .mul (.reg 11) (.reg rBp)
  , .binop rBp .add (.reg 17) (.reg 19)
  , .binop 20 .mul (.reg 10) (.lit w0)
  , .binop 21 .mul (.reg 11) (.reg rWt)
  , .binop rWt .add (.reg 20) (.reg 21)
  , .binop 22 .mul (.reg 11) (.reg rFs)
  , .binop rFs .add (.reg 10) (.reg 22)
  , .binop 23 .mul (.reg 10) (.reg 16)
  , .binop 24 .mul (.reg 11) (.reg rJ)
  , .binop rJ .add (.reg 23) (.reg 24) ]

def markResetBody (c : R2Cfg) : List AInstr := lift (markResetInstrs c)

theorem markResetBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 4).take (markResetBody c).length = markResetBody c := by
  rfl

/-- Away from a window boundary, the reset mux preserves the complete
prime-power cursor.  The explicit positive `q0` guard rules out relying on
remainder-by-zero behavior even though the reset candidates are gated off. -/
theorem markResetBody_nonstart_run (c : R2Cfg) (k : Nat) (s : AState)
    (r : Nat) (hr : s.regs rR = r) (hr0 : r ≠ 0)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQ < M)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M) (hjM : s.regs rJ < M) :
    let out := arun k s (markResetBody c)
    out.regs rPi = s.regs rPi ∧ out.regs rQ = s.regs rQ ∧
      out.regs rBp = s.regs rBp ∧ out.regs rWt = s.regs rWt ∧
      out.regs rFs = s.regs rFs ∧ out.regs rJ = s.regs rJ ∧
      out.arr = s.arr := by
  have hr5 : s.regs 5 = r := by simpa [rR] using hr
  have hpi2M : s.regs 2 < M := by simpa [rPi] using hpiM
  have hq3M : s.regs 3 < M := by simpa [rQ] using hqM
  have hj4M : s.regs 4 < M := by simpa [rJ] using hjM
  have hbp170M : s.regs 170 < M := by simpa [rBp] using hbpM
  have hwt171M : s.regs 171 < M := by simpa [rWt] using hwtM
  have hfs172M : s.regs 172 < M := by simpa [rFs] using hfsM
  have hq0nz : c.q0 ≠ 0 := Nat.ne_of_gt hq0
  have h1M : (1 : Nat) < M := by decide
  simp only [markResetBody, arun_lift]
  simp [markResetInstrs, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, hr5, hr0, rPi, rQ, rJ, rR, rW, rBp, rWt, rFs,
    hq0nz, Nat.mod_eq_of_lt hq0M,
    Nat.mod_eq_of_lt hpi2M, Nat.mod_eq_of_lt hq3M,
    Nat.mod_eq_of_lt hbp170M, Nat.mod_eq_of_lt hwt171M,
    Nat.mod_eq_of_lt hfs172M, Nat.mod_eq_of_lt hj4M,
    Nat.mod_eq_of_lt h1M]

def resetOffset (q w : Nat) : Nat := (q - w % q) % q

/-- At a window boundary, the mux installs the first table entry and computes
the first cell congruent to zero modulo that prime. -/
theorem markResetBody_start_run (c : R2Cfg) (k : Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M) :
    let out := arun k s (markResetBody c)
    out.regs rPi = 0 ∧ out.regs rQ = c.q0 ∧
      out.regs rBp = c.q0 ∧ out.regs rWt = c.w0 ∧
      out.regs rFs = 1 ∧ out.regs rJ = resetOffset c.q0 w ∧
      out.arr = s.arr := by
  have hr5 : s.regs 5 = 0 := by simpa [rR] using hr
  have hw6 : s.regs 6 = w := by simpa [rW] using hw
  have hq0nz : c.q0 ≠ 0 := Nat.ne_of_gt hq0
  have hrem : w % c.q0 < c.q0 := Nat.mod_lt w hq0
  have hremM : w % c.q0 < M := by omega
  have hoffQ : (c.q0 - w % c.q0) % c.q0 < c.q0 :=
    Nat.mod_lt _ hq0
  have hoffM : (c.q0 - w % c.q0) % c.q0 < M := by omega
  have hsubM :
      (c.q0 + (M - w % c.q0)) % M = c.q0 - w % c.q0 := by
    by_cases hz : w % c.q0 = 0
    · simp [hz, Nat.mod_eq_of_lt hq0M]
    · have hdelta : c.q0 - w % c.q0 < M := by omega
      have heq : c.q0 + (M - w % c.q0) =
          M + (c.q0 - w % c.q0) := by omega
      rw [heq, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hdelta]
  have h1M : (1 : Nat) < M := by decide
  have hMpos : 0 < M := by decide
  have hsubOne : 1 + (M - 1) = M := by omega
  simp only [markResetBody, arun_lift]
  simp [markResetInstrs, resetOffset, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hr5, hw6, rPi, rQ, rJ, rR, rW, rBp, rWt,
    rFs, hq0nz, hsubM, hsubOne, Nat.mod_eq_of_lt hremM,
    Nat.mod_eq_of_lt hoffM,
    Nat.mod_eq_of_lt hq0M,
    Nat.mod_eq_of_lt hw0M, Nat.mod_eq_of_lt h1M]

#print axioms markResetBody_nonstart_run
#print axioms markResetBody_start_run

end LeanCompCert.Ports.R2SegSieve
