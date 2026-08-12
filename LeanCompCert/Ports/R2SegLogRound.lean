import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Ports.LogFixRoundSemantics
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.InstrRename

/-!
# Exact fixed-log round inside the `R₂*` production program

Instructions 224--241 are the `LogFixPort` round with an injective global
register allocation.  The relocation theorem transfers the already-proved
arithmetic semantics to this literal slice of `R2Cfg.logBody`.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Verified.InstrRename

/-- Relocate the standalone round's inputs `0,1` to the persistent R₂
registers and its scratch registers `2,…,19` to `224,…,241`. -/
def logRoundReg : Nat → Nat
  | 0 => rXm
  | 1 => rAa
  | n + 2 => n + 224

theorem logRoundReg_injective : Function.Injective logRoundReg := by
  intro a b h
  rcases a with (_ | _ | a) <;> rcases b with (_ | _ | b) <;>
    simp [logRoundReg, rXm, rAa] at h ⊢ <;> omega

def logRoundInstrs : List Instr :=
  LeanCompCert.Ports.LogFixPort.logRoundBody.map (renameInstr logRoundReg)

def logRoundBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logRoundInstrs

theorem logRoundBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 32).take 20 = logRoundBody := by
  rfl

/-- The register-renamed scalar block has the exact fixed-log recurrence. -/
theorem logRoundInstrs_srun_of_range (k : Nat) (s : RegState) (x a : Nat)
    (hx : s rXm = x) (ha : s rAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := srun k s logRoundInstrs
    out rXm = logMant x ∧ out rAa = (a <<< 1) + logBit x := by
  let base : RegState := fun r => s (logRoundReg r)
  have hbase := LeanCompCert.Ports.LogFixPort.logRoundBody_srun_of_range
    k base x a (by
      simpa [base, logRoundReg, LeanCompCert.Ports.LogFixPort.rX] using hx)
      (by
        simpa [base, logRoundReg, LeanCompCert.Ports.LogFixPort.rA] using ha)
      hxlo hxhi haBound
  have hrename := srun_rename k logRoundReg logRoundReg_injective
    LeanCompCert.Ports.LogFixPort.logRoundBody base s (by
      intro r
      rfl)
  constructor
  · rw [show rXm = logRoundReg LeanCompCert.Ports.LogFixPort.rX by rfl]
    rw [show logRoundInstrs =
      LeanCompCert.Ports.LogFixPort.logRoundBody.map
        (renameInstr logRoundReg) by rfl]
    exact (hrename LeanCompCert.Ports.LogFixPort.rX).trans hbase.1
  · rw [show rAa = logRoundReg LeanCompCert.Ports.LogFixPort.rA by rfl]
    rw [show logRoundInstrs =
      LeanCompCert.Ports.LogFixPort.logRoundBody.map
        (renameInstr logRoundReg) by rfl]
    exact (hrename LeanCompCert.Ports.LogFixPort.rA).trans hbase.2

/-- Array-machine form used by the production body.  The scalar round also
leaves the sieve array byte-for-byte unchanged. -/
theorem logRoundBody_arun_of_range (k : Nat) (s : AState) (x a : Nat)
    (hx : s.regs rXm = x) (ha : s.regs rAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := arun k s logRoundBody
    out.regs rXm = logMant x ∧
      out.regs rAa = (a <<< 1) + logBit x ∧ out.arr = s.arr := by
  rw [logRoundBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logRoundInstrs_srun_of_range k s.regs x a
    hx ha hxlo hxhi haBound
  exact ⟨h.1, h.2, rfl⟩

#print axioms logRoundReg_injective
#print axioms logRoundBody_eq_slice
#print axioms logRoundInstrs_srun_of_range
#print axioms logRoundBody_arun_of_range

end LeanCompCert.Ports.R2SegSieve
