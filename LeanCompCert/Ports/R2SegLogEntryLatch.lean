import LeanCompCert.Ports.R2SegLogEntryGate
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined

/-!
# Stream-entry latch immediately after the `R₂*` live gate

The next seven instructions load the new test point and packed payload on a
first round, or preserve the already-latched pair on continuation rounds.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def logEntryLatchInstrs : List Instr :=
  [ .binop 209 .sub (.lit 1) (.reg 208)
  , .binop 210 .mul (.reg 208) (.reg 202)
  , .binop 211 .mul (.reg 209) (.reg rNe)
  , .binop rNe .add (.reg 210) (.reg 211)
  , .binop 212 .mul (.reg 208) (.reg 204)
  , .binop 213 .mul (.reg 209) (.reg rPl)
  , .binop rPl .add (.reg 212) (.reg 213) ]

def logEntryLatchBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logEntryLatchInstrs

theorem logEntryLatchBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 9).take 7 = logEntryLatchBody := by
  rfl

private theorem sub_one_one : (1 + (M - 1)) % M = 0 := by
  have h := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
    (a := 1) (b := 1) (by decide) (by decide)
  exact Option.some.inj h

theorem logEntryLatchInstrs_start_run (k : Nat) (s : RegState)
    (n payload : Nat) (h208 : s 208 = 1)
    (h202 : s 202 = n) (h204 : s 204 = payload)
    (hnM : n < M) (hpM : payload < M) :
    let out := srun k s logEntryLatchInstrs
    out 209 = 0 ∧ out rNe = n ∧ out rPl = payload := by
  simp [logEntryLatchInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h208, h202, h204, sub_one_one,
    Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hpM, rNe, rPl]

theorem logEntryLatchInstrs_continue_run (k : Nat) (s : RegState)
    (n payload : Nat) (h208 : s 208 = 0)
    (hne : s rNe = n) (hpl : s rPl = payload)
    (hnM : n < M) (hpM : payload < M) :
    let out := srun k s logEntryLatchInstrs
    out 209 = 1 ∧ out rNe = n ∧ out rPl = payload := by
  have hne' : s 194 = n := by simpa only [rNe] using hne
  have hpl' : s 195 = payload := by simpa only [rPl] using hpl
  have h1 : (1 : Nat) % M = 1 := by decide
  simp [logEntryLatchInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h208, hne', hpl', h1,
    Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hpM, rNe, rPl]

theorem logEntryLatchBody_start_run (k : Nat) (s : AState)
    (n payload : Nat) (h208 : s.regs 208 = 1)
    (h202 : s.regs 202 = n) (h204 : s.regs 204 = payload)
    (hnM : n < M) (hpM : payload < M) :
    let out := arun k s logEntryLatchBody
    out.regs 209 = 0 ∧ out.regs rNe = n ∧
      out.regs rPl = payload ∧ out.arr = s.arr := by
  rw [logEntryLatchBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logEntryLatchInstrs_start_run k s.regs n payload
    h208 h202 h204 hnM hpM
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

theorem logEntryLatchBody_continue_run (k : Nat) (s : AState)
    (n payload : Nat) (h208 : s.regs 208 = 0)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hnM : n < M) (hpM : payload < M) :
    let out := arun k s logEntryLatchBody
    out.regs 209 = 1 ∧ out.regs rNe = n ∧
      out.regs rPl = payload ∧ out.arr = s.arr := by
  rw [logEntryLatchBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logEntryLatchInstrs_continue_run k s.regs n payload
    h208 hne hpl hnM hpM
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

#print axioms logEntryLatchBody_eq_slice
#print axioms logEntryLatchBody_start_run
#print axioms logEntryLatchBody_continue_run

end LeanCompCert.Ports.R2SegSieve
