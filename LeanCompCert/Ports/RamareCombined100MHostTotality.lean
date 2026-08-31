import LeanCompCert.Ports.RamareCombined100MLambdaPsiSweep

/-!
# Symbolic totality of the unchanged Ramaré host body

This module reduces partial-semantics obligations for
`LambdaPsiSweep.body` without executing a sweep.  It is deliberately kept
separate from the V3 receipt/candidate-checker modules.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.RamareCombined100M

def HostNoPartial : AInstr → Bool
  | .scalar (.mov _ _) => true
  | .scalar (.binop _ op _ _) => op != .udiv && op != .urem
  | .load _ _ => false
  | .store _ _ => false

theorem allDefined_of_all_hostNoPartial (len k : Nat) :
    ∀ (xs : List AInstr) (s : AState), xs.all HostNoPartial = true →
      AllDefined len k s xs := by
  intro xs
  induction xs with
  | nil => intro s _; trivial
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, ih _ h.2⟩
      cases i with
      | load d r => simp [HostNoPartial] at h
      | store r v => simp [HostNoPartial] at h
      | scalar instr =>
          cases instr with
          | mov d src => trivial
          | binop d op l r =>
              simp only [HostNoPartial, Bool.and_eq_true, bne_iff_ne] at h
              show (denoteOp op (denoteOperand k s.regs l)
                (denoteOperand k s.regs r)).isSome = true
              cases op <;> simp_all [denoteOp]

/-- A single scalar quotient is defined exactly when its evaluated divisor is
nonzero.  Keeping this one-instruction lemma opaque avoids normalising a
whole host block merely to expose one guard. -/
theorem scalarUdiv_defined (len k : Nat) (s : AState) (d : Nat)
    (l r : Operand)
    (hden : denoteOperand k s.regs r ≠ 0) :
    AllDefined len k s [.scalar (.binop d .udiv l r)] := by
  refine ⟨?_, trivial⟩
  simpa [ADefined, denoteOp] using hden

/-- A scalar block whose only divisions/remainders use one register is
defined when that register is nonzero and the block does not overwrite it. -/
theorem sAllDefined_of_divReg (k r : Nat) : ∀ (xs : List Instr),
    (∀ i ∈ xs, sdest i ≠ r) →
    (∀ i ∈ xs, NoDivI i = true ∨
      ∃ d op a, i = .binop d op a (.reg r) ∧
        (op = Op.udiv ∨ op = Op.urem)) →
    ∀ regs : RegState, regs r ≠ 0 → SAllDefined k regs xs := by
  intro xs
  induction xs with
  | nil => intro _ _ regs _; trivial
  | cons i rest ih =>
      intro hdest hshape regs hr
      have hhead : SDefined k regs i := by
        rcases hshape i (by simp) with hnd | ⟨d, op, a, rfl, hop⟩
        · exact SDefined_of_noDiv k regs i hnd
        · show (denoteOp op (denoteOperand k regs a)
            (denoteOperand k regs (.reg r))).isSome = true
          rcases hop with rfl | rfl <;> simp [denoteOp, hr]
      refine ⟨hhead, ih (fun j hj => hdest j (by simp [hj]))
        (fun j hj => hshape j (by simp [hj])) _ ?_⟩
      have hkeep : sdest i ≠ r := hdest i (by simp)
      have hkeep' : r ≠ sdest i := Ne.symm hkeep
      simp [RegState.set, hkeep', hr]

theorem allDefined_lift_of_divReg (len k r : Nat) (xs : List Instr)
    (s : AState)
    (hdest : ∀ i ∈ xs, sdest i ≠ r)
    (hshape : ∀ i ∈ xs, NoDivI i = true ∨
      ∃ d op a, i = .binop d op a (.reg r) ∧
        (op = Op.udiv ∨ op = Op.urem))
    (hr : s.regs r ≠ 0) : AllDefined len k s (lift xs) := by
  rw [allDefined_lift]
  exact sAllDefined_of_divReg k r xs hdest hshape s.regs hr

/-- Decidable syntactic check used for long fixed scalar blocks. -/
def DivRegI (r : Nat) : Instr → Bool
  | .mov _ _ => true
  | .binop _ op _ rhs =>
      if op = .udiv ∨ op = .urem then rhs == .reg r else true

theorem divRegI_shape (r : Nat) (i : Instr) (h : DivRegI r i = true) :
    NoDivI i = true ∨
      ∃ d op a, i = .binop d op a (.reg r) ∧
        (op = Op.udiv ∨ op = Op.urem) := by
  cases i with
  | mov d src => left; rfl
  | binop d op a rhs =>
      by_cases hop : op = .udiv ∨ op = .urem
      · simp only [DivRegI, if_pos hop, beq_iff_eq] at h
        subst rhs
        exact ⟨d, op, a, rfl, hop⟩ |> Or.inr
      · left
        rcases not_or.mp hop with ⟨hu, hr⟩
        simp [NoDivI, hu, hr]

theorem allDefined_lift_of_divRegCheck (len k r : Nat) (xs : List Instr)
    (s : AState)
    (hdest : xs.all (fun i => decide (sdest i ≠ r)) = true)
    (hshape : xs.all (DivRegI r) = true) (hr : s.regs r ≠ 0) :
    AllDefined len k s (lift xs) := by
  apply allDefined_lift_of_divReg len k r xs s
  · intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp hdest) i hi)
  · intro i hi
    exact divRegI_shape r i ((List.all_eq_true.mp hshape) i hi)
  · exact hr

/-- The lower log numerator's only partial instruction divides by the live
candidate, which is nonzero in the source-shaped arithmetic precondition. -/
theorem LogSweep.lowerNumeratorBody_defined (len k : Nat) (s : AState)
    (hn : 2 ≤ s.regs 132) :
    AllDefined len k s (lift LogSweep.lowerNumeratorBody) := by
  apply allDefined_lift_of_divReg len k 132 LogSweep.lowerNumeratorBody s
  · intro i hi
    simp [LogSweep.lowerNumeratorBody] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [sdest, LogSweep.rA, LogSweep.rB]
  · intro i hi
    simp [LogSweep.lowerNumeratorBody] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · left; rfl
    · left; rfl
    · right; exact ⟨LogSweep.rB, .udiv, .lit (RS62.fpD - 1), rfl, Or.inl rfl⟩
    · left; rfl
  · omega

/-- The denominator-producing prefix is separated from the only quotient in
the lower correction. -/
theorem LogSweep.lowerCorrectionBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.lowerCorrectionBody) := by
  let d := arun k s (lift LogSweep.lowerDenominatorBody)
  have h2n : s.regs 132 * 2 < M := by
    have : 2 ^ 51 < M := by decide
    omega
  have hdenom : AllDefined len k s (lift LogSweep.lowerDenominatorBody) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have hd := LogSweep.lowerDenominatorBody_run k s h2n
  change d.regs LogSweep.rB = s.regs 132 * 2 ∧ _ at hd
  have htail : AllDefined len k d
      (lift (LogSweep.lowerDivideBody ++ LogSweep.lowerSubtractBody)) := by
    apply allDefined_lift_of_divReg len k LogSweep.rB _ d
    · intro i hi
      simp [LogSweep.lowerDivideBody, LogSweep.lowerSubtractBody] at hi
      rcases hi with rfl | rfl <;>
        simp [sdest, LogSweep.rA, LogSweep.rB]
    · intro i hi
      simp [LogSweep.lowerDivideBody, LogSweep.lowerSubtractBody] at hi
      rcases hi with rfl | rfl
      · right
        exact ⟨LogSweep.rA, .udiv, .reg LogSweep.rA, rfl, Or.inl rfl⟩
      · left; rfl
    · rw [hd.1]
      omega
  have hall : AllDefined len k s
      (lift LogSweep.lowerDenominatorBody ++
        lift (LogSweep.lowerDivideBody ++ LogSweep.lowerSubtractBody)) :=
    (AllDefined_append len k _ _ s).mpr (by simpa only [d] using ⟨hdenom, htail⟩)
  simpa [LogSweep.lowerCorrectionBody, lift_append, List.append_assoc]
    using hall

/-- The final lower quotient divides by the preceding, explicitly-computed
`n-1`. -/
theorem LogSweep.lowerFinalizeBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.lowerFinalizeBody) := by
  let d := arun k s (lift LogSweep.lowerNMinusOneBody)
  have hprefix : AllDefined len k s (lift LogSweep.lowerNMinusOneBody) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have hd := LogSweep.lowerNMinusOneBody_run k s hn2 hn40
  change d.regs LogSweep.rB = s.regs 132 - 1 ∧ _ at hd
  have hquot : AllDefined len k d (lift LogSweep.lowerQuotientBody) := by
    apply allDefined_lift_of_divReg len k LogSweep.rB _ d
    · intro i hi
      simp [LogSweep.lowerQuotientBody] at hi
      subst i
      simp [sdest, LogSweep.rIL, LogSweep.rB]
    · intro i hi
      simp [LogSweep.lowerQuotientBody] at hi
      subst i
      right
      exact ⟨LogSweep.rIL, .udiv, .reg LogSweep.rA, rfl, Or.inl rfl⟩
    · rw [hd.1]
      omega
  rw [LogSweep.lowerFinalizeBody, lift_append, AllDefined_append]
  simpa only [d] using ⟨hprefix, hquot⟩

/-- Totality of the complete lower RS62 increment, proved stagewise. -/
theorem LogSweep.lowerScalarBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.lowerScalarBody) := by
  let numbered := arun k s (lift LogSweep.lowerNumeratorBody)
  let corrected := arun k numbered (lift LogSweep.lowerCorrectionBody)
  have hnfull := LogSweep.lowerNumeratorBody_run k s hn2 hn40
  have hn : numbered.regs 132 = s.regs 132 := hnfull.2.2.1
  have hcfull := LogSweep.lowerCorrectionBody_run k numbered
    (by rw [hn]; exact hn2) (by rw [hn]; exact hn40)
    (by
      rw [hnfull.1, hn])
  have hc : corrected.regs 132 = numbered.regs 132 := hcfull.2.2.1
  have hnum := LogSweep.lowerNumeratorBody_defined len k s hn2
  have hcorr := LogSweep.lowerCorrectionBody_defined len k numbered
    (by rw [hn]; exact hn2) (by rw [hn]; exact hn40)
  have hfinal := LogSweep.lowerFinalizeBody_defined len k corrected
    (by rw [hc, hn]; exact hn2)
    (by rw [hc, hn]; exact hn40)
  rw [LogSweep.lowerScalarBody, lift_append, lift_append,
    AllDefined_append, AllDefined_append]
  simpa only [arun_append, numbered, corrected] using
    ⟨⟨hnum, hcorr⟩, hfinal⟩

/-- The upper numerator divides only by the stable candidate register. -/
theorem LogSweep.upperNumeratorBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) :
    AllDefined len k s (lift LogSweep.upperNumeratorBody) := by
  apply allDefined_lift_of_divReg len k 132 LogSweep.upperNumeratorBody s
  · intro i hi
    simp [LogSweep.upperNumeratorBody, LogSweep.upperInitialBody,
      LogSweep.upperRecipNumeratorBody, LogSweep.upperRecipAddBody,
      LogSweep.upperRecipSubtractOneBody, LogSweep.upperRecipDivideBody,
      LogSweep.upperNumeratorSubtractBody] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sdest, LogSweep.rA, LogSweep.rB]
  · intro i hi
    simp [LogSweep.upperNumeratorBody, LogSweep.upperInitialBody,
      LogSweep.upperRecipNumeratorBody, LogSweep.upperRecipAddBody,
      LogSweep.upperRecipSubtractOneBody, LogSweep.upperRecipDivideBody,
      LogSweep.upperNumeratorSubtractBody] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · left; rfl
    · left; rfl
    · left; rfl
    · left; rfl
    · right
      exact ⟨LogSweep.rB, .udiv, .reg LogSweep.rB, rfl, Or.inl rfl⟩
    · left; rfl
  · omega

/-- The upper correction's denominator prefix computes the same nonzero
`2n` used by the lower correction. -/
theorem LogSweep.upperCorrectionBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.upperCorrectionBody) := by
  let d := arun k s (lift LogSweep.lowerDenominatorBody)
  have h2n : s.regs 132 * 2 < M := by
    have : 2 ^ 51 < M := by decide
    omega
  have hdenom : AllDefined len k s (lift LogSweep.lowerDenominatorBody) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have hd := LogSweep.lowerDenominatorBody_run k s h2n
  change d.regs LogSweep.rB = s.regs 132 * 2 ∧ _ at hd
  have hdiv : AllDefined len k d (lift LogSweep.lowerDivideBody) := by
    apply allDefined_lift_of_divReg len k LogSweep.rB _ d
    · intro i hi
      simp [LogSweep.lowerDivideBody] at hi
      subst i
      simp [sdest, LogSweep.rA, LogSweep.rB]
    · intro i hi
      simp [LogSweep.lowerDivideBody] at hi
      subst i
      right
      exact ⟨LogSweep.rA, .udiv, .reg LogSweep.rA, rfl, Or.inl rfl⟩
    · rw [hd.1]
      omega
  rw [LogSweep.upperCorrectionBody, lift_append, AllDefined_append]
  simpa only [d] using ⟨hdenom, hdiv⟩

/-- The upper final quotient divides by the explicitly-computed `n-1`. -/
theorem LogSweep.upperFinalizeBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.upperFinalizeBody) := by
  let d := arun k s (lift LogSweep.lowerNMinusOneBody)
  have hprefix : AllDefined len k s (lift LogSweep.lowerNMinusOneBody) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have hd := LogSweep.lowerNMinusOneBody_run k s hn2 hn40
  change d.regs LogSweep.rB = s.regs 132 - 1 ∧ _ at hd
  have hquot : AllDefined len k d (lift LogSweep.upperQuotientBody) := by
    apply allDefined_lift_of_divReg len k LogSweep.rB _ d
    · intro i hi
      simp [LogSweep.upperQuotientBody] at hi
      subst i
      simp [sdest, LogSweep.rIU, LogSweep.rB]
    · intro i hi
      simp [LogSweep.upperQuotientBody] at hi
      subst i
      right
      exact ⟨LogSweep.rIU, .udiv, .reg LogSweep.rA, rfl, Or.inl rfl⟩
    · rw [hd.1]
      omega
  rw [LogSweep.upperFinalizeBody, lift_append, AllDefined_append]
  simpa only [d] using ⟨hprefix, hquot⟩

/-- Totality of the complete upper RS62 increment, proved stagewise. -/
theorem LogSweep.upperScalarBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s (lift LogSweep.upperScalarBody) := by
  let numbered := arun k s (lift LogSweep.upperNumeratorBody)
  let corrected := arun k numbered (lift LogSweep.upperCorrectionBody)
  let based := arun k corrected (lift LogSweep.upperBaseBody)
  have hnfull := LogSweep.upperNumeratorBody_run k s hn2 hn40
  have hn : numbered.regs 132 = s.regs 132 := hnfull.2.2.1
  have hcfull := LogSweep.upperCorrectionBody_run k numbered
    (by rw [hn]; exact hn2) (by rw [hn]; exact hn40)
    (by rw [hnfull.1, hn])
  have hc : corrected.regs 132 = numbered.regs 132 := hcfull.2.2.1
  have hbfull := LogSweep.upperBaseBody_run k corrected
    (by rw [hc, hn]; exact hn2) (by rw [hc, hn]; exact hn40)
    (by rw [hcfull.1, hc, hn])
  have hb : based.regs 132 = corrected.regs 132 := hbfull.2.2.1
  have hnum := LogSweep.upperNumeratorBody_defined len k s hn2
  have hcorr := LogSweep.upperCorrectionBody_defined len k numbered
    (by rw [hn]; exact hn2) (by rw [hn]; exact hn40)
  have hbase : AllDefined len k corrected (lift LogSweep.upperBaseBody) :=
    allDefined_lift_of_noDiv len k _ corrected (by rfl)
  have hfinal := LogSweep.upperFinalizeBody_defined len k based
    (by rw [hb, hc, hn]; exact hn2)
    (by rw [hb, hc, hn]; exact hn40)
  rw [LogSweep.upperScalarBody, lift_append, lift_append, lift_append,
    AllDefined_append, AllDefined_append, AllDefined_append]
  simpa only [arun_append, numbered, corrected, based] using
    ⟨⟨⟨hnum, hcorr⟩, hbase⟩, hfinal⟩

/-- The complete log-candidate block is total under the exact candidate range
already present in `LambdaPsiSweep.ArithmeticPre`. -/
theorem LogSweep.candidateBody_defined (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    AllDefined len k s LogSweep.candidateBody := by
  let lowered := arun k s (lift LogSweep.lowerScalarBody)
  let uppered := arun k lowered (lift LogSweep.upperScalarBody)
  have hlrun := LogSweep.lowerScalarBody_run k s hn2 hn40
  have hln : lowered.regs 132 = s.regs 132 := hlrun.2.1
  have hl := LogSweep.lowerScalarBody_defined len k s hn2 hn40
  have hu := LogSweep.upperScalarBody_defined len k lowered
    (by rw [hln]; exact hn2) (by rw [hln]; exact hn40)
  have hcommit : AllDefined len k uppered (lift LogSweep.commitScalarBody) :=
    allDefined_lift_of_noDiv len k _ uppered (by rfl)
  rw [LogSweep.candidateBody, AllDefined_append, AllDefined_append]
  simpa only [arun_append, lowered, uppered] using ⟨⟨hl, hu⟩, hcommit⟩

/-! ## Lambda/psi arithmetic suffix -/

def endpointAdvancePrefix (lam : Nat) : List Instr :=
  [ .binop 222 .add (.reg 221) (.reg lam)
  , .binop 223 .add (.reg 132) (.lit 1) ]

def endpointAdvanceTail : List Instr :=
  [ .binop 224 .le (.reg 220) (.reg 222)
  , .binop 225 .sub (.reg 222) (.reg 220)
  , .binop 226 .udiv (.reg 225) (.reg 223)
  , .binop 227 .urem (.reg 225) (.reg 223)
  , .binop 228 .sub (.reg 220) (.reg 222)
  , .binop 229 .udiv (.reg 228) (.reg 223)
  , .binop 230 .urem (.reg 228) (.reg 223)
  , .binop 231 .ne (.reg 230) (.lit 0)
  , .binop 232 .add (.reg 220) (.reg 226)
  , .binop 233 .sub (.reg 220) (.reg 229)
  , .binop 233 .sub (.reg 233) (.reg 231)
  , .binop 234 .sub (.reg 223) (.reg 230)
  , .binop 234 .mul (.reg 234) (.reg 231)
  , .binop 235 .sub (.lit 1) (.reg 224)
  , .binop 236 .mul (.reg 232) (.reg 224)
  , .binop 237 .mul (.reg 233) (.reg 235)
  , .binop 220 .add (.reg 236) (.reg 237)
  , .binop 236 .mul (.reg 227) (.reg 224)
  , .binop 237 .mul (.reg 234) (.reg 235)
  , .binop 221 .add (.reg 236) (.reg 237) ]

theorem endpointAdvance_eq (lam : Nat) :
    LambdaPsiSweep.advanceScalarBody 220 221 lam 132 222 =
      endpointAdvancePrefix lam ++ endpointAdvanceTail := rfl

/-- Both endpoint instances divide only by the prefix's `n+1` register. -/
theorem LambdaPsiSweep.endpointAdvance_defined (lam len k : Nat) (s : AState)
    (hn : s.regs 132 + 1 < M) :
    AllDefined len k s (LambdaPsiSweep.advanceBody 220 221 lam 132 222) := by
  let t := arun k s (lift (endpointAdvancePrefix lam))
  have hpref : AllDefined len k s (lift (endpointAdvancePrefix lam)) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have ht223 : t.regs 223 = s.regs 132 + 1 := by
    rw [arun_lift_regs]
    simp [endpointAdvancePrefix, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Nat.mod_eq_of_lt hn]
  have htail : AllDefined len k t (lift endpointAdvanceTail) := by
    apply allDefined_lift_of_divRegCheck len k 223 endpointAdvanceTail t
    · rfl
    · rfl
    · rw [ht223]
      omega
  have hall : AllDefined len k s
      (lift (endpointAdvancePrefix lam) ++ lift endpointAdvanceTail) :=
    (AllDefined_append len k _ _ s).mpr (by simpa only [t] using ⟨hpref, htail⟩)
  simpa [LambdaPsiSweep.advanceBody, endpointAdvance_eq, lift_append]
    using hall

/-- The lower endpoint shell is total once the live candidate fits below the
word modulus. -/
theorem LambdaPsiSweep.lowerEndpointBody_defined (len k : Nat) (s : AState)
    (hn : s.regs 132 + 1 < M) :
    AllDefined len k s LambdaPsiSweep.lowerEndpointBody := by
  let copied := arun k s
    (LambdaPsiSweep.copyEndpointBody LambdaPsiSweep.rPsiLQ
      LambdaPsiSweep.rPsiLR)
  let advanced := arun k copied
    (LambdaPsiSweep.advanceBody 220 221 LambdaPsiSweep.rLamL 132 222)
  have hcopy : AllDefined len k s
      (LambdaPsiSweep.copyEndpointBody LambdaPsiSweep.rPsiLQ
        LambdaPsiSweep.rPsiLR) := by
    apply allDefined_lift_of_noDiv
    rfl
  have hcopyN : copied.regs 132 = s.regs 132 :=
    LambdaPsiSweep.arun_reg_frame k 132 _ s (by decide)
  have hadv := LambdaPsiSweep.endpointAdvance_defined
    LambdaPsiSweep.rLamL len k copied (by simpa [hcopyN] using hn)
  have hcommit : AllDefined len k advanced
      (LambdaPsiSweep.commitEndpointBody LambdaPsiSweep.rPsiLQ
        LambdaPsiSweep.rPsiLR) := by
    apply allDefined_lift_of_noDiv
    rfl
  rw [LambdaPsiSweep.lowerEndpointBody, AllDefined_append,
    AllDefined_append]
  simpa only [arun_append, copied, advanced] using ⟨⟨hcopy, hadv⟩, hcommit⟩

/-- The upper endpoint shell has the identical totality argument. -/
theorem LambdaPsiSweep.upperEndpointBody_defined (len k : Nat) (s : AState)
    (hn : s.regs 132 + 1 < M) :
    AllDefined len k s LambdaPsiSweep.upperEndpointBody := by
  let copied := arun k s
    (LambdaPsiSweep.copyEndpointBody LambdaPsiSweep.rPsiUQ
      LambdaPsiSweep.rPsiUR)
  let advanced := arun k copied
    (LambdaPsiSweep.advanceBody 220 221 LambdaPsiSweep.rLamU 132 222)
  have hcopy : AllDefined len k s
      (LambdaPsiSweep.copyEndpointBody LambdaPsiSweep.rPsiUQ
        LambdaPsiSweep.rPsiUR) := by
    apply allDefined_lift_of_noDiv
    rfl
  have hcopyN : copied.regs 132 = s.regs 132 :=
    LambdaPsiSweep.arun_reg_frame k 132 _ s (by decide)
  have hadv := LambdaPsiSweep.endpointAdvance_defined
    LambdaPsiSweep.rLamU len k copied (by simpa [hcopyN] using hn)
  have hcommit : AllDefined len k advanced
      (LambdaPsiSweep.commitEndpointBody LambdaPsiSweep.rPsiUQ
        LambdaPsiSweep.rPsiUR) := by
    apply allDefined_lift_of_noDiv
    rfl
  rw [LambdaPsiSweep.upperEndpointBody, AllDefined_append,
    AllDefined_append]
  simpa only [arun_append, copied, advanced] using ⟨⟨hcopy, hadv⟩, hcommit⟩

/-- The floor/ceiling sum block divides and takes remainder only by the stable
candidate register. -/
theorem LambdaPsiSweep.sumBody_defined (len k : Nat) (s : AState)
    (hn : 0 < s.regs 132) :
    AllDefined len k s LambdaPsiSweep.sumBody := by
  rw [LambdaPsiSweep.sumBody]
  apply allDefined_lift_of_divRegCheck len k 132 _ s
  · rfl
  · rfl
  · omega

def selectionLoPrefix (c : LambdaPsiSweep.Cfg) : List AInstr :=
  [ .scalar (.binop LambdaPsiSweep.rT0 .mul (.reg 11) (.reg LambdaPsiSweep.lRIL))
  , .scalar (.binop LambdaPsiSweep.rOldL .sub (.reg LambdaPsiSweep.lRLogL)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT0 .mul (.reg 11) (.reg LambdaPsiSweep.lRIU))
  , .scalar (.binop LambdaPsiSweep.rOldU .sub (.reg LambdaPsiSweep.lRLogU)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT0 .lt (.reg LambdaPsiSweep.sRP)
      (.lit c.logLen))
  , .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.sRP)
      (.lit c.logLoBase))
  , .scalar (.binop LambdaPsiSweep.rT1 .mul (.reg LambdaPsiSweep.rT0)
      (.reg LambdaPsiSweep.rT1))
  , .scalar (.binop LambdaPsiSweep.rT2 .sub (.lit 1)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT2 .mul (.reg LambdaPsiSweep.rT2)
      (.lit c.logSink))
  , .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.rT1)
      (.reg LambdaPsiSweep.rT2)) ]

def selectionHiPrefix (c : LambdaPsiSweep.Cfg) : List AInstr :=
  [ .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.sRP)
      (.lit c.logHiBase))
  , .scalar (.binop LambdaPsiSweep.rT1 .mul (.reg LambdaPsiSweep.rT0)
      (.reg LambdaPsiSweep.rT1))
  , .scalar (.binop LambdaPsiSweep.rT2 .sub (.lit 1)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT2 .mul (.reg LambdaPsiSweep.rT2)
      (.lit c.logSink))
  , .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.rT1)
      (.reg LambdaPsiSweep.rT2)) ]

def selectionPost : List AInstr :=
  [ .scalar (.binop LambdaPsiSweep.rT0 .eq (.reg LambdaPsiSweep.sRRest) (.lit 1))
  , .scalar (.binop LambdaPsiSweep.rT0 .mul (.reg LambdaPsiSweep.rT0) (.reg 11))
  , .scalar (.binop LambdaPsiSweep.rT1 .eq (.reg LambdaPsiSweep.sRP) (.reg 132))
  , .scalar (.binop LambdaPsiSweep.rT2 .sub (.lit 1) (.reg LambdaPsiSweep.rT1))
  , .scalar (.binop LambdaPsiSweep.rLamL .mul (.reg LambdaPsiSweep.rT1)
      (.reg LambdaPsiSweep.rOldL))
  , .scalar (.binop LambdaPsiSweep.rT2 .mul (.reg LambdaPsiSweep.rT2)
      (.reg LambdaPsiSweep.rTabL))
  , .scalar (.binop LambdaPsiSweep.rLamL .add (.reg LambdaPsiSweep.rLamL)
      (.reg LambdaPsiSweep.rT2))
  , .scalar (.binop LambdaPsiSweep.rLamL .mul (.reg LambdaPsiSweep.rLamL)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT2 .sub (.lit 1) (.reg LambdaPsiSweep.rT1))
  , .scalar (.binop LambdaPsiSweep.rLamU .mul (.reg LambdaPsiSweep.rT1)
      (.reg LambdaPsiSweep.rOldU))
  , .scalar (.binop LambdaPsiSweep.rT2 .mul (.reg LambdaPsiSweep.rT2)
      (.reg LambdaPsiSweep.rTabU))
  , .scalar (.binop LambdaPsiSweep.rLamU .add (.reg LambdaPsiSweep.rLamU)
      (.reg LambdaPsiSweep.rT2))
  , .scalar (.binop LambdaPsiSweep.rLamU .mul (.reg LambdaPsiSweep.rLamU)
      (.reg LambdaPsiSweep.rT0)) ]

theorem selectionBody_eq (c : LambdaPsiSweep.Cfg) :
    LambdaPsiSweep.selectionBody c =
      (((selectionLoPrefix c ++
          [.load LambdaPsiSweep.rTabL LambdaPsiSweep.rT1]) ++
        selectionHiPrefix c) ++
          [.load LambdaPsiSweep.rTabU LambdaPsiSweep.rT1]) ++ selectionPost := rfl

def LambdaPsiSweep.SelectionLoadGuards (c : LambdaPsiSweep.Cfg) (len k : Nat)
    (s : AState) : Prop :=
  let lo := arun k s (selectionLoPrefix c)
  let lowerLoaded := astep k lo (.load LambdaPsiSweep.rTabL LambdaPsiSweep.rT1)
  let hi := arun k lowerLoaded (selectionHiPrefix c)
  lo.regs LambdaPsiSweep.rT1 < len ∧ hi.regs LambdaPsiSweep.rT1 < len

theorem load_defined (len k : Nat) (s : AState) (d r : Nat)
    (h : s.regs r < len) : AllDefined len k s [.load d r] := by
  refine ⟨?_, trivial⟩
  simpa [ADefined] using h

/-- Exact structural reduction of the selection block to its two array-load
addresses; all surrounding scalar instructions are division-free. -/
theorem LambdaPsiSweep.selectionBody_defined_of_loadGuards
    (c : LambdaPsiSweep.Cfg) (len k : Nat) (s : AState)
    (h : LambdaPsiSweep.SelectionLoadGuards c len k s) :
    AllDefined len k s (LambdaPsiSweep.selectionBody c) := by
  let lo := arun k s (selectionLoPrefix c)
  let lowerLoaded := astep k lo
    (.load LambdaPsiSweep.rTabL LambdaPsiSweep.rT1)
  let hi := arun k lowerLoaded (selectionHiPrefix c)
  let upperLoaded := astep k hi
    (.load LambdaPsiSweep.rTabU LambdaPsiSweep.rT1)
  have hlo : AllDefined len k s (selectionLoPrefix c) :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hloadL : AllDefined len k lo
      [.load LambdaPsiSweep.rTabL LambdaPsiSweep.rT1] :=
    load_defined len k lo _ _ h.1
  have hhi : AllDefined len k lowerLoaded (selectionHiPrefix c) :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hloadU : AllDefined len k hi
      [.load LambdaPsiSweep.rTabU LambdaPsiSweep.rT1] :=
    load_defined len k hi _ _ h.2
  have hpost : AllDefined len k upperLoaded selectionPost :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  rw [selectionBody_eq, AllDefined_append, AllDefined_append,
    AllDefined_append, AllDefined_append]
  simpa only [arun_append, arun_cons, arun, lo, lowerLoaded, hi, upperLoaded]
    using ⟨⟨⟨⟨hlo, hloadL⟩, hhi⟩, hloadU⟩, hpost⟩

/-- The complete lambda/psi candidate suffix has no residual partiality beyond
its two selection loads. -/
theorem LambdaPsiSweep.candidateBody_defined_of_loadGuards
    (c : LambdaPsiSweep.Cfg) (len k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hloads : LambdaPsiSweep.SelectionLoadGuards c len k s) :
    AllDefined len k s (LambdaPsiSweep.candidateBody c) := by
  let selected := arun k s (LambdaPsiSweep.selectionBody c)
  let summed := arun k selected LambdaPsiSweep.sumBody
  let lowered := arun k summed LambdaPsiSweep.lowerEndpointBody
  have hsN : selected.regs 132 = s.regs 132 :=
    LambdaPsiSweep.arun_reg_frame k 132 _ s (by rfl)
  have hmN : summed.regs 132 = selected.regs 132 :=
    LambdaPsiSweep.arun_reg_frame k 132 _ selected (by decide)
  have hlN : lowered.regs 132 = summed.regs 132 :=
    LambdaPsiSweep.arun_reg_frame k 132 _ summed (by decide)
  have hnM : s.regs 132 + 1 < M := by
    have : 2 ^ 40 + 1 < M := by decide
    omega
  have hsel := LambdaPsiSweep.selectionBody_defined_of_loadGuards
    c len k s hloads
  have hsum := LambdaPsiSweep.sumBody_defined len k selected
    (by rw [hsN]; omega)
  have hlower := LambdaPsiSweep.lowerEndpointBody_defined len k summed
    (by rw [hmN, hsN]; exact hnM)
  have hupper := LambdaPsiSweep.upperEndpointBody_defined len k lowered
    (by rw [hlN, hmN, hsN]; exact hnM)
  rw [LambdaPsiSweep.candidateBody, AllDefined_append, AllDefined_append,
    AllDefined_append]
  simpa only [arun_append, selected, summed, lowered] using
    ⟨⟨⟨hsel, hsum⟩, hlower⟩, hupper⟩

def LambdaPsiSweep.ArithmeticLoadGuards (c : LambdaPsiSweep.Cfg)
    (len k : Nat) (s : AState) : Prop :=
  LambdaPsiSweep.SelectionLoadGuards c len k
    (LambdaPsiSweep.afterLogCandidate k s)

/-- `ArithmeticPre` discharges every scalar divisor in the host arithmetic
suffix.  The only remaining facts are the two physical selection addresses. -/
theorem LambdaPsiSweep.arithmeticBody_defined_of_pre_and_loadGuards
    (c : LambdaPsiSweep.Cfg) (len k : Nat) (s : AState)
    (hpre : LambdaPsiSweep.ArithmeticPre c k s)
    (hloads : LambdaPsiSweep.ArithmeticLoadGuards c len k s) :
    AllDefined len k s (LambdaPsiSweep.arithmeticBody c) := by
  let logged := LambdaPsiSweep.afterLogCandidate k s
  have hlog := LogSweep.candidateBody_defined len k s hpre.n2 hpre.n40
  have hlogrun := LogSweep.candidateBody_run k s hpre.n2 hpre.n40
    hpre.lowerMul hpre.lowerAdd hpre.upperMul hpre.upperAdd
  have hn : logged.regs 132 = s.regs 132 := hlogrun.2.2.2.2.1
  have hcand := LambdaPsiSweep.candidateBody_defined_of_loadGuards
    c len k logged (by rw [hn]; exact hpre.n2)
      (by rw [hn]; exact hpre.n40) hloads
  rw [LambdaPsiSweep.arithmeticBody, AllDefined_append]
  simpa only [LambdaPsiSweep.afterLogCandidate, logged] using ⟨hlog, hcand⟩

theorem LambdaPsiSweep.body_eq_shape_arithmetic (c : LambdaPsiSweep.Cfg) :
    LambdaPsiSweep.body c = c.shape.body ++ LambdaPsiSweep.arithmeticBody c := by
  simp [LambdaPsiSweep.body, LogSweep.body, LambdaPsiSweep.arithmeticBody,
    List.append_assoc]

/-- Reusable exact host guard: shape-sieve access/divisor guards, the existing
source-shaped arithmetic invariant, and the two lambda-table load addresses. -/
structure LambdaPsiSweep.HostBodyGuards (c : LambdaPsiSweep.Cfg)
    (len k : Nat) (s : AState) : Prop where
  shape : AllDefined len k s c.shape.body
  arithmeticPre : LambdaPsiSweep.ArithmeticPre c k
    (arun k s c.shape.body)
  arithmeticLoads : LambdaPsiSweep.ArithmeticLoadGuards c len k
    (arun k s c.shape.body)

/-- Exact replacement for the former monolithic `LambdaPsiSweep.body`
`AllDefined` premise. -/
theorem LambdaPsiSweep.body_defined_of_hostGuards
    (c : LambdaPsiSweep.Cfg) (len k : Nat) (s : AState)
    (h : LambdaPsiSweep.HostBodyGuards c len k s) :
    AllDefined len k s (LambdaPsiSweep.body c) := by
  rw [LambdaPsiSweep.body_eq_shape_arithmetic, AllDefined_append]
  exact ⟨h.shape,
    LambdaPsiSweep.arithmeticBody_defined_of_pre_and_loadGuards c len k _
      h.arithmeticPre h.arithmeticLoads⟩

/-! ## Static discharge of the two lambda-table addresses -/

def selectionRecoveredLogs : List AInstr :=
  [ .scalar (.binop LambdaPsiSweep.rT0 .mul (.reg 11) (.reg LambdaPsiSweep.lRIL))
  , .scalar (.binop LambdaPsiSweep.rOldL .sub (.reg LambdaPsiSweep.lRLogL)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT0 .mul (.reg 11) (.reg LambdaPsiSweep.lRIU))
  , .scalar (.binop LambdaPsiSweep.rOldU .sub (.reg LambdaPsiSweep.lRLogU)
      (.reg LambdaPsiSweep.rT0)) ]

def selectionLoAddress (c : LambdaPsiSweep.Cfg) : List AInstr :=
  [ .scalar (.binop LambdaPsiSweep.rT0 .lt (.reg LambdaPsiSweep.sRP)
      (.lit c.logLen))
  , .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.sRP)
      (.lit c.logLoBase))
  , .scalar (.binop LambdaPsiSweep.rT1 .mul (.reg LambdaPsiSweep.rT0)
      (.reg LambdaPsiSweep.rT1))
  , .scalar (.binop LambdaPsiSweep.rT2 .sub (.lit 1)
      (.reg LambdaPsiSweep.rT0))
  , .scalar (.binop LambdaPsiSweep.rT2 .mul (.reg LambdaPsiSweep.rT2)
      (.lit c.logSink))
  , .scalar (.binop LambdaPsiSweep.rT1 .add (.reg LambdaPsiSweep.rT1)
      (.reg LambdaPsiSweep.rT2)) ]

theorem selectionLoPrefix_eq (c : LambdaPsiSweep.Cfg) :
    selectionLoPrefix c = selectionRecoveredLogs ++ selectionLoAddress c := rfl

theorem selectionLoAddress_index (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hpM : s.regs LambdaPsiSweep.sRP < M)
    (hlen : c.logLen < M)
    (haddr : s.regs LambdaPsiSweep.sRP + c.logLoBase < M)
    (hsink : c.logSink < M) :
    (arun k s (selectionLoAddress c)).regs LambdaPsiSweep.rT1 =
      LambdaPsiSweep.selectedLoIndex c (s.regs LambdaPsiSweep.sRP) := by
  have hpmod := Nat.mod_eq_of_lt hpM
  have hlenmod := Nat.mod_eq_of_lt hlen
  have haddmod := Nat.mod_eq_of_lt haddr
  have hsinkmod := Nat.mod_eq_of_lt hsink
  have h1mod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hpmod' : s.regs 100 % M = s.regs 100 := by
    simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using hpmod
  have hbase : c.logLoBase < M := by omega
  have hbasemod := Nat.mod_eq_of_lt hbase
  have haddmod' : (s.regs 100 + c.logLoBase) % M =
      s.regs 100 + c.logLoBase := by
    simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using haddmod
  have hMsub : 1 + (M - 1) = M := by
    have := one_lt_M
    omega
  by_cases hp : s.regs LambdaPsiSweep.sRP < c.logLen
  · have hp' : s.regs 100 < c.logLen := by
      simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using hp
    simp [selectionLoAddress, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      LambdaPsiSweep.selectedLoIndex, LambdaPsiSweep.rT0,
      LambdaPsiSweep.rT1, LambdaPsiSweep.rT2, LambdaPsiSweep.sRP,
      ShapeSieve.rShapeP, hp', hpmod', hlenmod, hbasemod, haddmod',
      hsinkmod, h1mod, hMsub]
  · have hp' : ¬s.regs 100 < c.logLen := by
      simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using hp
    simp [selectionLoAddress, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      LambdaPsiSweep.selectedLoIndex, LambdaPsiSweep.rT0,
      LambdaPsiSweep.rT1, LambdaPsiSweep.rT2, LambdaPsiSweep.sRP,
      ShapeSieve.rShapeP, hp', hpmod', hlenmod, hbasemod, haddmod',
      hsinkmod, h1mod, hMsub]

theorem selectionLoPrefix_index (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hpM : s.regs LambdaPsiSweep.sRP < M)
    (hlen : c.logLen < M)
    (haddr : s.regs LambdaPsiSweep.sRP + c.logLoBase < M)
    (hsink : c.logSink < M) :
    (arun k s (selectionLoPrefix c)).regs LambdaPsiSweep.rT1 =
      LambdaPsiSweep.selectedLoIndex c (s.regs LambdaPsiSweep.sRP) := by
  let recovered := arun k s selectionRecoveredLogs
  have hp : recovered.regs LambdaPsiSweep.sRP =
      s.regs LambdaPsiSweep.sRP :=
    LambdaPsiSweep.arun_reg_frame k _ _ s (by decide)
  rw [selectionLoPrefix_eq, arun_append]
  simpa only [hp] using selectionLoAddress_index c k recovered
    (by rw [hp]; exact hpM) hlen (by rw [hp]; exact haddr) hsink

theorem selectionLoAddress_gate (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hpM : s.regs LambdaPsiSweep.sRP < M)
    (hlen : c.logLen < M) :
    (arun k s (selectionLoAddress c)).regs LambdaPsiSweep.rT0 =
      if s.regs LambdaPsiSweep.sRP < c.logLen then 1 else 0 := by
  have hpmod := Nat.mod_eq_of_lt hpM
  have hlenmod := Nat.mod_eq_of_lt hlen
  simp [selectionLoAddress, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    LambdaPsiSweep.rT0, LambdaPsiSweep.rT1, LambdaPsiSweep.rT2,
    LambdaPsiSweep.sRP, ShapeSieve.rShapeP, hpmod, hlenmod]

theorem selectionLoPrefix_gate (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hpM : s.regs LambdaPsiSweep.sRP < M)
    (hlen : c.logLen < M) :
    (arun k s (selectionLoPrefix c)).regs LambdaPsiSweep.rT0 =
      if s.regs LambdaPsiSweep.sRP < c.logLen then 1 else 0 := by
  let recovered := arun k s selectionRecoveredLogs
  have hp : recovered.regs LambdaPsiSweep.sRP =
      s.regs LambdaPsiSweep.sRP :=
    LambdaPsiSweep.arun_reg_frame k _ _ s (by decide)
  rw [selectionLoPrefix_eq, arun_append]
  simpa only [hp] using selectionLoAddress_gate c k recovered
    (by rw [hp]; exact hpM) hlen

theorem selectionHiPrefix_index (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hpM : s.regs LambdaPsiSweep.sRP < M)
    (hgate : s.regs LambdaPsiSweep.rT0 =
      if s.regs LambdaPsiSweep.sRP < c.logLen then 1 else 0)
    (haddr : s.regs LambdaPsiSweep.sRP + c.logHiBase < M)
    (hsink : c.logSink < M) :
    (arun k s (selectionHiPrefix c)).regs LambdaPsiSweep.rT1 =
      LambdaPsiSweep.selectedHiIndex c (s.regs LambdaPsiSweep.sRP) := by
  have haddmod := Nat.mod_eq_of_lt haddr
  have hbase : c.logHiBase < M := by omega
  have hbasemod := Nat.mod_eq_of_lt hbase
  have hsinkmod := Nat.mod_eq_of_lt hsink
  have h1mod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hMsub : 1 + (M - 1) = M := by
    have := one_lt_M
    omega
  change s.regs 212 = if s.regs 100 < c.logLen then 1 else 0 at hgate
  have hgate' : s.regs 212 =
      if s.regs 100 < c.logLen then 1 else 0 := hgate
  have haddmod' : (s.regs 100 + c.logHiBase) % M =
      s.regs 100 + c.logHiBase := by
    simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using haddmod
  by_cases hp : s.regs LambdaPsiSweep.sRP < c.logLen
  · have hp' : s.regs 100 < c.logLen := by
      simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using hp
    simp [selectionHiPrefix, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      LambdaPsiSweep.selectedHiIndex, LambdaPsiSweep.rT0,
      LambdaPsiSweep.rT1, LambdaPsiSweep.rT2, LambdaPsiSweep.sRP,
      ShapeSieve.rShapeP, hgate', hp', hbasemod, haddmod', hsinkmod,
      h1mod, hMsub]
  · have hp' : ¬s.regs 100 < c.logLen := by
      simpa [LambdaPsiSweep.sRP, ShapeSieve.rShapeP] using hp
    simp [selectionHiPrefix, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      LambdaPsiSweep.selectedHiIndex, LambdaPsiSweep.rT0,
      LambdaPsiSweep.rT1, LambdaPsiSweep.rT2, LambdaPsiSweep.sRP,
      ShapeSieve.rShapeP, hgate', hp', hbasemod, haddmod', hsinkmod,
      h1mod, hMsub]

theorem LambdaPsiSweep.selectedLoIndex_lt_arrayLen
    (c : LambdaPsiSweep.Cfg) (p : Nat) :
    LambdaPsiSweep.selectedLoIndex c p < c.arrayLen + 1 := by
  by_cases hp : p < c.logLen
  · simp [LambdaPsiSweep.selectedLoIndex, hp]
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
      LambdaPsiSweep.Cfg.logSink LambdaPsiSweep.Cfg.logHiBase
    omega
  · simp [LambdaPsiSweep.selectedLoIndex, hp]
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
    omega

theorem LambdaPsiSweep.selectedHiIndex_lt_arrayLen
    (c : LambdaPsiSweep.Cfg) (p : Nat) :
    LambdaPsiSweep.selectedHiIndex c p < c.arrayLen + 1 := by
  by_cases hp : p < c.logLen
  · simp [LambdaPsiSweep.selectedHiIndex, hp]
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
      LambdaPsiSweep.Cfg.logSink
    omega
  · simp [LambdaPsiSweep.selectedHiIndex, hp]
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
    omega

/-- At the actual host allocation, `ArithmeticPre` statically discharges both
selection loads; no runtime/receipt-supplied address axiom remains. -/
theorem LambdaPsiSweep.arithmeticLoadGuards_of_pre
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState)
    (hpre : LambdaPsiSweep.ArithmeticPre c k s) :
    LambdaPsiSweep.ArithmeticLoadGuards c (c.arrayLen + 1) k s := by
  let logged := LambdaPsiSweep.afterLogCandidate k s
  let lo := arun k logged (selectionLoPrefix c)
  let lowerLoaded := astep k lo
    (.load LambdaPsiSweep.rTabL LambdaPsiSweep.rT1)
  let hi := arun k lowerLoaded (selectionHiPrefix c)
  have hw := arun_word k LogSweep.candidateBody s hpre.regs hpre.arr
  have hpM : logged.regs LambdaPsiSweep.sRP < M := hw.1 _
  have hloIndex : lo.regs LambdaPsiSweep.rT1 =
      LambdaPsiSweep.selectedLoIndex c
        (logged.regs LambdaPsiSweep.sRP) :=
    selectionLoPrefix_index c k logged hpM hpre.logLen hpre.addrL hpre.sink
  have hloP : lo.regs LambdaPsiSweep.sRP =
      logged.regs LambdaPsiSweep.sRP :=
    LambdaPsiSweep.arun_reg_frame k _ _ logged (by rfl)
  have hloGate : lo.regs LambdaPsiSweep.rT0 =
      if logged.regs LambdaPsiSweep.sRP < c.logLen then 1 else 0 :=
    selectionLoPrefix_gate c k logged hpM hpre.logLen
  change lo.regs 100 = logged.regs 100 at hloP
  change lo.regs 212 =
    (if logged.regs 100 < c.logLen then 1 else 0) at hloGate
  have hloadedP : lowerLoaded.regs LambdaPsiSweep.sRP =
      logged.regs LambdaPsiSweep.sRP := by
    change lowerLoaded.regs 100 = logged.regs 100
    simp [lowerLoaded, astep, AState.writeReg, hloP,
      LambdaPsiSweep.rTabL, LambdaPsiSweep.rT1, LambdaPsiSweep.sRP,
      ShapeSieve.rShapeP]
  have hloadedGate : lowerLoaded.regs LambdaPsiSweep.rT0 =
      if lowerLoaded.regs LambdaPsiSweep.sRP < c.logLen then 1 else 0 := by
    change lowerLoaded.regs 212 =
      (if lowerLoaded.regs 100 < c.logLen then 1 else 0)
    simp [lowerLoaded, astep, AState.writeReg, hloGate, hloP,
      LambdaPsiSweep.rTabL, LambdaPsiSweep.rT1, LambdaPsiSweep.rT0,
      LambdaPsiSweep.sRP, ShapeSieve.rShapeP]
  have hhiIndex : hi.regs LambdaPsiSweep.rT1 =
      LambdaPsiSweep.selectedHiIndex c
        (logged.regs LambdaPsiSweep.sRP) := by
    have hraw := selectionHiPrefix_index c k lowerLoaded
      (by rw [hloadedP]; exact hpM) hloadedGate
      (by rw [hloadedP]; exact hpre.addrU) hpre.sink
    simpa only [hloadedP] using hraw
  change lo.regs LambdaPsiSweep.rT1 < c.arrayLen + 1 ∧
    hi.regs LambdaPsiSweep.rT1 < c.arrayLen + 1
  exact ⟨by rw [hloIndex]; exact LambdaPsiSweep.selectedLoIndex_lt_arrayLen c _,
    by rw [hhiIndex]; exact LambdaPsiSweep.selectedHiIndex_lt_arrayLen c _⟩

/-- Consequently the arithmetic suffix is fully total from `ArithmeticPre`
alone at the actual allocation size. -/
theorem LambdaPsiSweep.arithmeticBody_defined_of_pre
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState)
    (hpre : LambdaPsiSweep.ArithmeticPre c k s) :
    AllDefined (c.arrayLen + 1) k s (LambdaPsiSweep.arithmeticBody c) :=
  LambdaPsiSweep.arithmeticBody_defined_of_pre_and_loadGuards c
    (c.arrayLen + 1) k s hpre
    (LambdaPsiSweep.arithmeticLoadGuards_of_pre c k s hpre)

/-- Minimal host residual at the real allocation: shape-sieve totality plus
the already-existing source-shaped arithmetic invariant. -/
structure LambdaPsiSweep.HostInvariant (c : LambdaPsiSweep.Cfg)
    (k : Nat) (s : AState) : Prop where
  shape : AllDefined (c.arrayLen + 1) k s c.shape.body
  arithmeticPre : LambdaPsiSweep.ArithmeticPre c k
    (arun k s c.shape.body)

theorem LambdaPsiSweep.body_defined_of_hostInvariant
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState)
    (h : LambdaPsiSweep.HostInvariant c k s) :
    AllDefined (c.arrayLen + 1) k s (LambdaPsiSweep.body c) := by
  rw [LambdaPsiSweep.body_eq_shape_arithmetic, AllDefined_append]
  exact ⟨h.shape, LambdaPsiSweep.arithmeticBody_defined_of_pre c k _
    h.arithmeticPre⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock
