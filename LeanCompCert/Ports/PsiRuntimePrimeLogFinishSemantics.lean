import LeanCompCert.Ports.PsiRuntimePrimeLogConversionSemantics

/-!
# Final fixed-log assembly in the compiled psi prime-weight program

After the symbolic fixed-log rounds, the emitted body combines the integer
and fractional logarithm fields and converts them to the natural-log fixed
point value.  These proofs operate on the literal instruction suffix and do
not run a production loop.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.LogFixed

/-- Scalar view of instructions 37 and 38 in `psiPrimeLogBody`. -/
def psiPrimeLogAssemblyScalar (S : Nat) : List Instr :=
  [ .binop 43 .shl (.reg 18) (.lit S)
  , .binop 44 .add (.reg 43) (.reg primeAa) ]

def psiPrimeLogAssembly (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 37).take 2

def psiPrimeLogFinish (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 37).take 13

theorem psiPrimeLogAssembly_eq_lift (m : PsiRuntimeMeta) :
    psiPrimeLogAssembly m = lift (psiPrimeLogAssemblyScalar m.cfg.sc) := by
  rfl

theorem psiPrimeLogFinish_eq_stages (m : PsiRuntimeMeta) :
    psiPrimeLogFinish m =
      psiPrimeLogAssembly m ++ psiPrimeLogConversion m := by
  rfl

theorem psiPrimeLogAssemblyScalar_run
    (index : Nat) (s : RegState) (S e a : Nat)
    (he : s 18 = e) (ha : s primeAa = a)
    (hSM : S < M)
    (heM : e * 2 ^ S < M)
    (hsumM : e * 2 ^ S + a < M) :
    (srun index s (psiPrimeLogAssemblyScalar S)) 44 = e * 2 ^ S + a := by
  have hSmod : S % M = S := Nat.mod_eq_of_lt hSM
  change ((((s 18 <<< (S % M)) % M) + s primeAa) % M) =
    e * 2 ^ S + a
  rw [he, ha, hSmod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt heM,
    Nat.mod_eq_of_lt hsumM]

theorem psiPrimeLogAssembly_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (e a : Nat)
    (he : s.regs 18 = e) (ha : s.regs primeAa = a)
    (hSM : m.cfg.sc < M)
    (heM : e * 2 ^ m.cfg.sc < M)
    (hsumM : e * 2 ^ m.cfg.sc + a < M) :
    let out := arun index s (psiPrimeLogAssembly m)
    out.regs 44 = e * 2 ^ m.cfg.sc + a ∧ out.arr = s.arr := by
  rw [psiPrimeLogAssembly_eq_lift, arun_lift]
  exact ⟨psiPrimeLogAssemblyScalar_run index s.regs m.cfg.sc e a
    he ha hSM heM hsumM, rfl⟩

/-- The literal 13-instruction finish computes `lnFix` from the mathematical
integer and fractional fixed-log fields. -/
theorem psiPrimeLogFinish_logFix_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (n : Nat)
    (he : s.regs 18 = Nat.log2 n)
    (ha : s.regs primeAa =
      logFrac m.cfg.sc (n <<< (62 - Nat.log2 n)))
    (hSM : m.cfg.sc < M)
    (hfix : logFix m.cfg.sc n < 2 ^ 30) :
    let out := arun index s (psiPrimeLogFinish m)
    out.regs 55 = lnFix m.cfg.sc n ∧ out.arr = s.arr := by
  have hfixM : logFix m.cfg.sc n < M := Nat.lt_trans hfix (by decide)
  have heM : Nat.log2 n * 2 ^ m.cfg.sc < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by
      simpa only [logFix] using hfixM)
  let mid := arun index s (psiPrimeLogAssembly m)
  have hp := psiPrimeLogAssembly_run m index s (Nat.log2 n)
    (logFrac m.cfg.sc (n <<< (62 - Nat.log2 n))) he ha hSM heM (by
      simpa only [logFix] using hfixM)
  have hmid : mid.regs 44 = logFix m.cfg.sc n := by
    simpa only [mid, logFix] using hp.1
  have hc := psiPrimeLogConversion_run m index mid m.cfg.sc n hfix hmid
  rw [psiPrimeLogFinish_eq_stages, arun_append]
  exact ⟨hc.1, hc.2.trans hp.2⟩

#print axioms psiPrimeLogAssemblyScalar_run
#print axioms psiPrimeLogAssembly_run
#print axioms psiPrimeLogFinish_logFix_run

end LeanCompCert.Ports.PsiSegSieve
