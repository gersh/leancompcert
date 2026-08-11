import LeanCompCert.Ports.R2SegMarkingInstrCell
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Production address stage for the `R₂*` marking loop

This is the eight-instruction scalar stage immediately before the verified
marking-cell slice.  On an active in-window hit it selects the three live
plane addresses rather than the sinks.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def markAddressInstrs (c : R2Cfg) : List Instr :=
  let L := c.segLen
  let SNK := c.sink
  [ .binop 25 .lt (.reg rJ) (.lit L)
  , .binop 26 .mul (.reg 25) (.reg 8)
  , .binop 27 .sub (.lit 1) (.reg 26)
  , .binop 28 .mul (.reg 26) (.reg rJ)
  , .binop 29 .mul (.reg 27) (.lit SNK)
  , .binop 30 .add (.reg 28) (.reg 29)
  , .binop 31 .add (.reg 30) (.lit L)
  , .binop 32 .add (.reg 30) (.lit (2 * L)) ]

def markAddressBody (c : R2Cfg) : List AInstr :=
  lift (markAddressInstrs c)

/-- The helper is definitionally the production address stage. -/
theorem markAddressBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 23).take (markAddressBody c).length =
      markAddressBody c := by
  rfl

/-- An active hit at cell `j < L` selects `j`, `j+L`, and `j+2L`.
The upper bound states exactly that the last address is representable. -/
theorem markAddressBody_run (c : R2Cfg) (k : Nat) (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M) :
    let out := arun k s (markAddressBody c)
    out.regs 30 = j ∧ out.regs 31 = j + c.segLen ∧
      out.regs 32 = j + 2 * c.segLen ∧ out.arr = s.arr := by
  have hjM : j < M := by omega
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have hjLM : j + c.segLen < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  have hMpos : 0 < M := by decide
  have hsub : 1 + (M - 1) = M := by omega
  simp only [markAddressBody, arun_lift]
  simp [markAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ, hjL, hsub,
    Nat.mod_eq_of_lt hjM, Nat.mod_eq_of_lt hLM,
    Nat.mod_eq_of_lt h2LM, Nat.mod_eq_of_lt hjLM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

/-- Once the current multiple lies past the window, the same active address
stage selects only the three scratch sinks at `3L`, `4L`, and `5L`. -/
theorem markAddressBody_past_run (c : R2Cfg) (k : Nat) (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : c.segLen ≤ j) (haddr : 5 * c.segLen < M) :
    let out := arun k s (markAddressBody c)
    out.regs 30 = 3 * c.segLen ∧ out.regs 31 = 4 * c.segLen ∧
      out.regs 32 = 5 * c.segLen ∧ out.arr = s.arr := by
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have h3LM : 3 * c.segLen < M := by omega
  have h4LM : 4 * c.segLen < M := by omega
  have h3add : 3 * c.segLen + c.segLen = 4 * c.segLen := by omega
  have h3add2 : 3 * c.segLen + 2 * c.segLen = 5 * c.segLen := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  simp only [markAddressBody, arun_lift]
  simp [markAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ, show ¬j < c.segLen by omega,
    R2Cfg.sink, h3add, h3add2, Nat.mod_eq_of_lt hLM,
    Nat.mod_eq_of_lt h2LM,
    Nat.mod_eq_of_lt h3LM, Nat.mod_eq_of_lt h4LM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

/-- The resident address branch leaves the production `pastWindow` bit
cleared. -/
theorem markAddressBody_resident_pastBit (c : R2Cfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 8 = 1) (hjL : j < c.segLen)
    (haddr : j + 2 * c.segLen < M) :
    (arun k s (markAddressBody c)).regs 27 = 0 := by
  have hjM : j < M := by omega
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have hjLM : j + c.segLen < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  have hsub : 1 + (M - 1) = M := by omega
  simp only [markAddressBody, arun_lift]
  simp [markAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ, hjL, hsub,
    Nat.mod_eq_of_lt hjM, Nat.mod_eq_of_lt hLM,
    Nat.mod_eq_of_lt h2LM, Nat.mod_eq_of_lt hjLM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

/-- The out-of-window address branch sets the production `pastWindow` bit. -/
theorem markAddressBody_past_pastBit (c : R2Cfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 8 = 1) (hjL : c.segLen ≤ j)
    (haddr : 5 * c.segLen < M) :
    (arun k s (markAddressBody c)).regs 27 = 1 := by
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have h3LM : 3 * c.segLen < M := by omega
  have h4LM : 4 * c.segLen < M := by omega
  have h3add : 3 * c.segLen + c.segLen = 4 * c.segLen := by omega
  have h3add2 : 3 * c.segLen + 2 * c.segLen = 5 * c.segLen := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  simp only [markAddressBody, arun_lift]
  simp [markAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ, show ¬j < c.segLen by omega,
    R2Cfg.sink, h3add, h3add2, Nat.mod_eq_of_lt hLM,
    Nat.mod_eq_of_lt h2LM, Nat.mod_eq_of_lt h3LM,
    Nat.mod_eq_of_lt h4LM, Nat.mod_eq_of_lt haddr,
    Nat.mod_eq_of_lt h1M]

#print axioms markAddressBody_run
#print axioms markAddressBody_past_run
#print axioms markAddressBody_resident_pastBit
#print axioms markAddressBody_past_pastBit

end LeanCompCert.Ports.R2SegSieve
