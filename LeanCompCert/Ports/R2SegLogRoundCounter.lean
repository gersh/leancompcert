import LeanCompCert.Ports.R2SegLogRoundInit
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Counter/finalization island after the `R₂*` fixed-log round

For logarithmic payload modes (`0` or `1`), instructions 242--249 and the
write to `rK` increment the round count and finish exactly when it reaches
the configured scale.  This is the scheduling fact needed to place the
24-round finite telescope inside the full production loop.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def logRoundCounterInstrs (S : Nat) : List Instr :=
  [ .binop 242 .lshr (.reg rPl) (.lit 57)
  , .binop 243 .ge (.reg 242) (.lit 2)
  , .binop 244 .add (.reg rK) (.lit 1)
  , .binop 245 .eq (.reg 244) (.lit S)
  , .binop 246 .add (.reg 245) (.reg 243)
  , .binop 247 .mul (.reg 246) (.reg 206)
  , .binop 248 .sub (.lit 1) (.reg 246)
  , .binop 249 .mul (.reg 244) (.reg 248)
  , .binop rK .mul (.reg 249) (.reg 206) ]

def logRoundCounterBody (S : Nat) : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift (logRoundCounterInstrs S)

theorem logRoundCounterBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 52).take 9 = logRoundCounterBody c.sc := by
  rfl

/-- In a live logarithmic entry, the counter advances or resets on the exact
final round; register 247 is the corresponding finish bit. -/
theorem logRoundCounterInstrs_run (S k : Nat) (s : RegState)
    (payload mode j : Nat)
    (hpl : s rPl = payload) (hmode : payload >>> 57 = mode)
    (hmodeLt : mode < 2) (hk : s rK = j) (hlive : s 206 = 1)
    (hj : j < S) (hSM : S < M) :
    let out := srun k s (logRoundCounterInstrs S)
    out 242 = mode ∧ out 243 = 0 ∧ out 244 = j + 1 ∧
      out 247 = (if j + 1 = S then 1 else 0) ∧
      out rK = (if j + 1 = S then 0 else j + 1) := by
  have h57 : (57 : Nat) % M = 57 := by decide
  have h2 : (2 : Nat) % M = 2 := by decide
  have h1 : (1 : Nat) % M = 1 := by decide
  have hmodeM : mode < M := Nat.lt_trans hmodeLt (by decide)
  have hj1M : j + 1 < M := Nat.lt_of_le_of_lt (by omega) hSM
  have hSMmod : S % M = S := Nat.mod_eq_of_lt hSM
  have hpl' : s 195 = payload := by simpa only [rPl] using hpl
  have hk' : s 193 = j := by simpa only [rK] using hk
  have hno : ¬2 ≤ mode := by omega
  have hsub1 : (1 + (M - 1)) % M = 0 := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 1) (b := 1) (by decide) (by decide)
    exact Option.some.inj hs
  by_cases hlast : j + 1 = S
  · simp [logRoundCounterInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hpl', hk', hlive, h57, h2, h1, hmode,
      hno, hsub1, hlast, hSMmod, Nat.mod_eq_of_lt hmodeM, rPl, rK]
  · simp [logRoundCounterInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hpl', hk', hlive, h57, h2, h1, hmode,
      hno, hlast, hSMmod, Nat.mod_eq_of_lt hmodeM,
      Nat.mod_eq_of_lt hj1M, rPl, rK]

theorem logRoundCounterBody_run (S k : Nat) (s : AState)
    (payload mode j : Nat)
    (hpl : s.regs rPl = payload) (hmode : payload >>> 57 = mode)
    (hmodeLt : mode < 2) (hk : s.regs rK = j) (hlive : s.regs 206 = 1)
    (hj : j < S) (hSM : S < M) :
    let out := arun k s (logRoundCounterBody S)
    out.regs 242 = mode ∧ out.regs 243 = 0 ∧
      out.regs 244 = j + 1 ∧
      out.regs 247 = (if j + 1 = S then 1 else 0) ∧
      out.regs rK = (if j + 1 = S then 0 else j + 1) ∧
      out.arr = s.arr := by
  rw [logRoundCounterBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logRoundCounterInstrs_run S k s.regs payload mode j
    hpl hmode hmodeLt hk hlive hj hSM
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, rfl⟩

#print axioms logRoundCounterBody_eq_slice
#print axioms logRoundCounterInstrs_run
#print axioms logRoundCounterBody_run

end LeanCompCert.Ports.R2SegSieve
