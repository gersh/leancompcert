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

#print axioms markAddressBody_run

end LeanCompCert.Ports.R2SegSieve
