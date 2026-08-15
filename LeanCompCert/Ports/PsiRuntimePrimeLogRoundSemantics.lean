import LeanCompCert.Ports.PsiRuntimeHead
import LeanCompCert.Ports.LogFixRoundSemantics
import LeanCompCert.Verified.InstrRename
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.LogFixedBounds

/-!
# Fixed-log rounds in the compiled psi prime-weight program

The production prime-log body contains the already verified 21-instruction
`LogFixPort` round under a global register allocation.  This module proves the
relocation and telescopes an arbitrary symbolic list of rounds.  It never
enumerates the production prime table or executes a production fold in Lean.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.InstrRename
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.LogFixed

/-- Scalar view of instructions 17 through 36 in `psiPrimeLogBody`. -/
def psiPrimeLogRoundScalar : List Instr :=
  [ .binop 25 .lshr (.reg primeXm) (.lit 32)
  , .binop 26 .band (.reg primeXm) (.lit 4294967295)
  , .binop 27 .mul (.reg 25) (.reg 25)
  , .binop 28 .mul (.reg 25) (.reg 26)
  , .binop 29 .mul (.reg 26) (.reg 26)
  , .binop 30 .lshr (.reg 28) (.lit 29)
  , .binop 31 .band (.reg 28) (.lit 536870911)
  , .binop 32 .lshr (.reg 29) (.lit 62)
  , .binop 33 .band (.reg 29) (.lit 4611686018427387903)
  , .binop 34 .shl (.reg 31) (.lit 33)
  , .binop 35 .add (.reg 34) (.reg 33)
  , .binop 36 .ge (.reg 35) (.lit 4611686018427387904)
  , .binop 37 .shl (.reg 27) (.lit 2)
  , .binop 38 .add (.reg 37) (.reg 30)
  , .binop 39 .add (.reg 38) (.reg 32)
  , .binop 40 .add (.reg 39) (.reg 36)
  , .binop 41 .ge (.reg 40) (.lit 9223372036854775808)
  , .binop primeXm .lshr (.reg 40) (.reg 41)
  , .binop 42 .shl (.reg primeAa) (.lit 1)
  , .binop primeAa .add (.reg 42) (.reg 41) ]

/-- The literal slice of the emitted mixed array/register body. -/
def psiPrimeLogRound (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 17).take 20

theorem psiPrimeLogRound_eq_lift (m : PsiRuntimeMeta) :
    psiPrimeLogRound m = lift psiPrimeLogRoundScalar := by rfl

/-- Relocate `LogFixPort` inputs `0,1` to the persistent psi registers and
its scratch registers `2,...,19` to `25,...,42`. -/
def psiPrimeLogReg : Nat → Nat
  | n =>
      if n = 0 then primeXm
      else if n = 1 then primeAa
      else if n < 20 then n + 23
      else if 25 ≤ n ∧ n < 43 then n - 23
      else if n = primeXm then 0
      else if n = primeAa then 1
      else n

theorem psiPrimeLogReg_injective : Function.Injective psiPrimeLogReg := by
  intro a b h
  simp only [psiPrimeLogReg] at h
  rw [show primeXm = 362 by rfl, show primeAa = 363 by rfl] at h
  repeat' first | split at h
  all_goals omega

theorem psiPrimeLogRoundScalar_eq_rename :
    psiPrimeLogRoundScalar =
      LeanCompCert.Ports.LogFixPort.logRoundBody.map
        (renameInstr psiPrimeLogReg) := by
  rfl

/-- One literal psi round is exactly the verified fixed-log recurrence. -/
theorem psiPrimeLogRoundScalar_run_of_range
    (index : Nat) (s : RegState) (x a : Nat)
    (hx : s primeXm = x) (ha : s primeAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := srun index s psiPrimeLogRoundScalar
    out primeXm = logMant x ∧
      out primeAa = (a <<< 1) + logBit x := by
  let base : RegState := fun r => s (psiPrimeLogReg r)
  have hbase := LeanCompCert.Ports.LogFixPort.logRoundBody_srun_of_range
    index base x a (by
      simpa [base, psiPrimeLogReg, LeanCompCert.Ports.LogFixPort.rX] using hx)
      (by
        simpa [base, psiPrimeLogReg, LeanCompCert.Ports.LogFixPort.rA] using ha)
      hxlo hxhi haBound
  have hrename := srun_rename index psiPrimeLogReg
    psiPrimeLogReg_injective LeanCompCert.Ports.LogFixPort.logRoundBody
    base s (by intro r; rfl)
  constructor
  · rw [show primeXm =
        psiPrimeLogReg LeanCompCert.Ports.LogFixPort.rX by rfl]
    rw [psiPrimeLogRoundScalar_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rX).trans hbase.1
  · rw [show primeAa =
        psiPrimeLogReg LeanCompCert.Ports.LogFixPort.rA by rfl]
    rw [psiPrimeLogRoundScalar_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rA).trans hbase.2

theorem psiPrimeLogRound_run_of_range
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (x a : Nat)
    (hx : s.regs primeXm = x) (ha : s.regs primeAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := arun index s (psiPrimeLogRound m)
    out.regs primeXm = logMant x ∧
      out.regs primeAa = (a <<< 1) + logBit x ∧ out.arr = s.arr := by
  rw [psiPrimeLogRound_eq_lift, arun_lift]
  have h := psiPrimeLogRoundScalar_run_of_range index s.regs x a
    hx ha hxlo hxhi haBound
  exact ⟨h.1, h.2, rfl⟩

theorem psiPrimeLog_logIter_fst_range (x0 : Nat)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) : ∀ rounds : Nat,
    B62 ≤ (logIter x0 rounds).1 ∧ (logIter x0 rounds).1 < B63 := by
  intro rounds
  induction rounds with
  | zero => exact ⟨hxlo, hxhi⟩
  | succ rounds ih =>
      simpa only [logIter, logStep] using logMant_range ih.1 ih.2

/-- Symbolic telescope for any suffix of fixed-log rounds.  Only the list
length is inspected; its indices and all production table values stay opaque. -/
theorem psiPrimeLog_foldl_round_from_iter
    (m : PsiRuntimeMeta) (indices : List Nat) (s : AState)
    (x0 j : Nat)
    (hx : s.regs primeXm = (logIter x0 j).1)
    (ha : s.regs primeAa = (logIter x0 j).2)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hcount : j + indices.length ≤ 62) :
    let out := indices.foldl
      (fun st index => arun index st (psiPrimeLogRound m)) s
    out.regs primeXm = (logIter x0 (j + indices.length)).1 ∧
      out.regs primeAa = (logIter x0 (j + indices.length)).2 ∧
      out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [List.foldl, List.length_nil, Nat.add_zero]
      exact ⟨hx, ha, trivial⟩
  | cons index rest ih =>
      have hj : j < 62 := by
        simp only [List.length_cons] at hcount
        omega
      have haLt := logIter_snd_lt_two_pow x0 j
      have haBound : (logIter x0 j).2 < B62 := by
        have hjPow : 2 ^ j ≤ 2 ^ 61 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hpow : (2 : Nat) ^ 61 < B62 := by decide
        omega
      have hrange := psiPrimeLog_logIter_fst_range x0 hxlo hxhi j
      let next := arun index s (psiPrimeLogRound m)
      have hstep := psiPrimeLogRound_run_of_range m index s
        (logIter x0 j).1 (logIter x0 j).2 hx ha
        hrange.1 hrange.2 haBound
      dsimp only at hstep
      have hxNext : next.regs primeXm = (logIter x0 (j + 1)).1 := by
        simpa only [next, logIter, logStep] using hstep.1
      have haNext : next.regs primeAa = (logIter x0 (j + 1)).2 := by
        simpa only [next, logIter, logStep, Nat.shiftLeft_eq,
          Nat.pow_one, Nat.mul_comm] using hstep.2.1
      have hrest : j + 1 + rest.length ≤ 62 := by
        simp only [List.length_cons] at hcount
        omega
      have hout := ih next (j + 1) hxNext haNext hrest
      dsimp only at hout
      simp only [List.foldl, List.length_cons]
      have hindex : j + 1 + rest.length = j + (rest.length + 1) := by omega
      exact ⟨hout.1.trans (congrArg (fun z => (logIter x0 z).1) hindex),
        hout.2.1.trans (congrArg (fun z => (logIter x0 z).2) hindex),
        hout.2.2.trans hstep.2.2⟩

#print axioms psiPrimeLogRoundScalar_run_of_range
#print axioms psiPrimeLogRound_run_of_range
#print axioms psiPrimeLog_foldl_round_from_iter

end LeanCompCert.Ports.PsiSegSieve
