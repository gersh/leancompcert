import LeanCompCert.Ports.R2ClauseAuditSound
import LeanCompCert.Ports.R2SegClauseFailureTelescope
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Telescope for the compiled `R₂*` comparison-word audit

The terminal zero latch is propagated through the symbolic production fold.
No production iteration is evaluated by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ClauseAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayAudit

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

private theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a ≤ a ||| b := Nat.left_le_or
  have hb : b ≤ a ||| b := Nat.right_le_or
  omega

private theorem orCommit_mono (k : Nat) (s : AState) (rhs : Nat)
    (hs : WordState s) (hrhs : rhs < M) :
    s.regs auditReg ≤
      (astep k s (.scalar (.binop auditReg .bor
        (.reg auditReg) (.lit rhs)))).regs auditReg := by
  have hor := or_lt_M (hs.1 auditReg) hrhs
  simp [astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    auditReg, Nat.mod_eq_of_lt hor]
  exact Nat.left_le_or

theorem finGuardBody_audit_mono (k : Nat) (s : AState)
    (hs : WordState s) :
    s.regs auditReg ≤ (arun k s finGuardBody).regs auditReg := by
  let mid := astep k s
    (.scalar (.binop badReg .gt (.reg 247) (.lit 1)))
  have hmidWord : WordState mid := by
    change WordState (arun k s
      [.scalar (.binop badReg .gt (.reg 247) (.lit 1))])
    exact arun_word k _ s hs.1 hs.2
  have hframe : mid.regs auditReg = s.regs auditReg := by
    exact astep_frame k auditReg s _ (by decide)
  have hbad : mid.regs badReg < M := hmidWord.1 _
  have hmono := orCommit_mono k mid (mid.regs badReg) hmidWord hbad
  rw [hframe] at hmono
  simpa [finGuardBody, arun, mid, auditReg] using hmono

theorem gatedAddGuardBody_audit_mono (k : Nat) (s : AState)
    (dest : Nat) (lhs : Operand) (hs : WordState s) :
    s.regs auditReg ≤
      (arun k s (gatedAddGuardBody dest lhs)).regs auditReg := by
  let mid := arun k s (gatedAddGuardBody dest lhs).take 2
  have hmidWord : WordState mid := arun_word k _ s hs.1 hs.2
  have hframe : mid.regs auditReg = s.regs auditReg := by
    exact arun_frame k auditReg _ (by
      simp [gatedAddGuardBody, writes, instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, auditReg, badReg, gatedReg]) s
  have hor := or_lt_M (hmidWord.1 auditReg) (hmidWord.1 gatedReg)
  rw [show gatedAddGuardBody dest lhs =
      (gatedAddGuardBody dest lhs).take 2 ++
        [.scalar (.binop auditReg .bor (.reg auditReg) (.reg gatedReg))] by
    rfl, arun_append]
  simp [arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt hor, hframe]
  exact Nat.left_le_or

private theorem wf400_not_write_audit (i : AInstr) (hi : i.WF 400) :
    instrWrites auditReg i = false := by
  cases i with
  | scalar instr =>
      cases instr <;>
        simp only [AInstr.WF, Instr.WF, Operand.WF] at hi <;>
        simp [instrWrites, LeanCompCert.Verified.InstrBlock.sdest,
          auditReg] <;> omega
  | load dest idx =>
      simp only [AInstr.WF] at hi
      simp [instrWrites, auditReg]
      omega
  | store idx src => rfl

theorem auditInstr_audit_mono (S k : Nat) (s : AState) (i : AInstr)
    (hi : i.WF 400) (hs : WordState s) :
    s.regs auditReg ≤ (arun k s (auditInstr S i)).regs auditReg := by
  let stepped := astep k s i
  have hstepWord : WordState stepped := by
    change WordState (arun k s [i])
    exact arun_word k [i] s hs.1 hs.2
  have hstepFrame : stepped.regs auditReg = s.regs auditReg :=
    astep_frame k auditReg s i (wf400_not_write_audit i hi)
  let finExtra := if decide (i = finInstr) then finGuardBody else []
  let addExtra :=
    if decide (i = clauseAdd293) then gatedAddGuardBody 293 (.reg rD)
    else if decide (i = clauseAdd294) then gatedAddGuardBody 294 (.reg 293)
    else if decide (i = clauseAdd295 S) then
      gatedAddGuardBody 295 (.lit (biasOf S))
    else if decide (i = clauseAdd321) then gatedAddGuardBody 321 (.reg rD)
    else if decide (i = clauseAdd322 S) then
      gatedAddGuardBody 322 (.lit (biasOf S))
    else []
  let afterFin := arun k stepped finExtra
  have hfinWord : WordState afterFin := arun_word k finExtra stepped
    hstepWord.1 hstepWord.2
  have hfinMono : stepped.regs auditReg ≤ afterFin.regs auditReg := by
    by_cases hfin : decide (i = finInstr) = true
    · simpa only [finExtra, if_pos hfin] using
        finGuardBody_audit_mono k stepped hstepWord
    · simp [finExtra, hfin]
  have haddMono : afterFin.regs auditReg ≤
      (arun k afterFin addExtra).regs auditReg := by
    by_cases h293 : decide (i = clauseAdd293) = true
    · simpa only [addExtra, if_pos h293] using
        gatedAddGuardBody_audit_mono k afterFin 293 (.reg rD) hfinWord
    · by_cases h294 : decide (i = clauseAdd294) = true
      · simpa only [addExtra, if_neg h293, if_pos h294] using
          gatedAddGuardBody_audit_mono k afterFin 294 (.reg 293) hfinWord
      · by_cases h295 : decide (i = clauseAdd295 S) = true
        · simpa only [addExtra, if_neg h293, if_neg h294, if_pos h295] using
            gatedAddGuardBody_audit_mono k afterFin 295
              (.lit (biasOf S)) hfinWord
        · by_cases h321 : decide (i = clauseAdd321) = true
          · simpa only [addExtra, if_neg h293, if_neg h294, if_neg h295,
              if_pos h321] using
              gatedAddGuardBody_audit_mono k afterFin 321 (.reg rD) hfinWord
          · by_cases h322 : decide (i = clauseAdd322 S) = true
            · simpa only [addExtra, if_neg h293, if_neg h294, if_neg h295,
                if_neg h321, if_pos h322] using
                gatedAddGuardBody_audit_mono k afterFin 322
                  (.lit (biasOf S)) hfinWord
            · simp [addExtra, h293, h294, h295, h321, h322]
  rw [auditInstr]
  change s.regs auditReg ≤ (arun k afterFin addExtra).regs auditReg
  exact hstepFrame ▸ Nat.le_trans hfinMono haddMono

theorem auditBlock_audit_mono (S k : Nat) :
    ∀ (xs : List AInstr) (s : AState),
      (∀ i ∈ xs, i.WF 400) → WordState s →
      s.regs auditReg ≤ (arun k s (auditBlock S xs)).regs auditReg := by
  intro xs
  induction xs with
  | nil => intro s _ _; exact Nat.le_refl _
  | cons i rest ih =>
      intro s hwf hs
      have hi := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF 400 := by
        intro a ha; exact hwf a (by simp [ha])
      let mid := arun k s (auditInstr S i)
      have hfirst := auditInstr_audit_mono S k s i hi hs
      have hmidWord : WordState mid := arun_word k _ s hs.1 hs.2
      have htail := ih mid hrest hmidWord
      rw [auditBlock, List.flatMap_cons, arun_append]
      exact Nat.le_trans hfirst htail

theorem finGuardBody_sourceAgree (k : Nat) (s : AState) :
    SourceAgree 400 (arun k s finGuardBody) s := by
  constructor
  · simp [finGuardBody, arun, astep, AState.writeReg]
  · intro j hj
    apply arun_frame k j finGuardBody
    simp [finGuardBody, writes, instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, auditReg, badReg]
    omega

theorem gatedAddGuardBody_sourceAgree (k : Nat) (s : AState)
    (dest : Nat) (lhs : Operand) :
    SourceAgree 400 (arun k s (gatedAddGuardBody dest lhs)) s := by
  constructor
  · simp [gatedAddGuardBody, arun, astep, AState.writeReg]
  · intro j hj
    apply arun_frame k j (gatedAddGuardBody dest lhs)
    simp [gatedAddGuardBody, writes, instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, auditReg, badReg, gatedReg]
    omega

private theorem optionalExtras_sourceAgree (S k : Nat) (i : AInstr)
    (s : AState) :
    let finExtra := if decide (i = finInstr) then finGuardBody else []
    let addExtra :=
      if decide (i = clauseAdd293) then gatedAddGuardBody 293 (.reg rD)
      else if decide (i = clauseAdd294) then gatedAddGuardBody 294 (.reg 293)
      else if decide (i = clauseAdd295 S) then
        gatedAddGuardBody 295 (.lit (biasOf S))
      else if decide (i = clauseAdd321) then gatedAddGuardBody 321 (.reg rD)
      else if decide (i = clauseAdd322 S) then
        gatedAddGuardBody 322 (.lit (biasOf S))
      else []
    SourceAgree 400 (arun k (arun k s finExtra) addExtra) s := by
  dsimp only
  by_cases hfin : decide (i = finInstr) = true <;>
  by_cases h293 : decide (i = clauseAdd293) = true <;>
  by_cases h294 : decide (i = clauseAdd294) = true <;>
  by_cases h295 : decide (i = clauseAdd295 S) = true <;>
  by_cases h321 : decide (i = clauseAdd321) = true <;>
  by_cases h322 : decide (i = clauseAdd322 S) = true <;>
  simp only [hfin, h293, h294, h295, h321, h322, if_pos, if_neg, arun] <;>
  first
  | exact SourceAgree.trans
      (gatedAddGuardBody_sourceAgree k _ _ _)
      (finGuardBody_sourceAgree k s)
  | exact gatedAddGuardBody_sourceAgree k s _ _
  | exact finGuardBody_sourceAgree k s
  | exact SourceAgree.refl 400 s

theorem auditInstr_sourceAgree (S k : Nat) (audited source : AState)
    (i : AInstr) (hi : i.WF 400) (hagree : SourceAgree 400 audited source) :
    SourceAgree 400 (arun k audited (auditInstr S i))
      (astep k source i) := by
  have hstep := astep_sourceAgree (idx := k) hagree hi
  let stepped := astep k audited i
  have hextra := optionalExtras_sourceAgree S k i stepped
  exact SourceAgree.trans hextra hstep

theorem auditBlock_sourceAgree (S k : Nat) :
    ∀ (xs : List AInstr) (audited source : AState),
      (∀ i ∈ xs, i.WF 400) → SourceAgree 400 audited source →
      SourceAgree 400 (arun k audited (auditBlock S xs))
        (arun k source xs) := by
  intro xs
  induction xs with
  | nil => intro audited source _ hagree; exact hagree
  | cons i rest ih =>
      intro audited source hwf hagree
      have hi := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF 400 := by
        intro a ha; exact hwf a (by simp [ha])
      have hfirst := auditInstr_sourceAgree S k audited source i hi hagree
      have htail := ih (arun k audited (auditInstr S i))
        (astep k source i) hrest hfirst
      simpa only [auditBlock, List.flatMap_cons, arun_append, arun] using htail

private theorem fold_arun_word (body : List AInstr) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      WordState (indices.foldl (fun st k => arun k st body) s) := by
  intro indices
  induction indices with
  | nil => intro s hs; exact hs
  | cons k rest ih =>
      intro s hs
      exact ih _ (arun_word k body s hs.1 hs.2)

private theorem fold_step_mono (body : List AInstr) (r : Nat)
    (hmono : ∀ k s, WordState s →
      s.regs r ≤ (arun k s body).regs r) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      s.regs r ≤
        (indices.foldl (fun st k => arun k st body) s).regs r := by
  intro indices
  induction indices with
  | nil => intro s _; exact Nat.le_refl _
  | cons k rest ih =>
      intro s hs
      let mid := arun k s body
      exact Nat.le_trans (hmono k s hs)
        (ih mid (arun_word k body s hs.1 hs.2))

private theorem loop_zero_of_runFromArray (p : AProgram) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState) (r : Nat)
    (hrun : p.runFromArray arr = some out) (hout : out.regs r = 0)
    (loopOut : AState)
    (hloopOut : loopOut =
      (List.range p.loopCount).foldl
        (fun s index => arun index s p.body)
        (arun 0 (initialAStateWithArray arr) p.init))
    (hepiMono : ∀ s, WordState s →
      s.regs r ≤ (arun 0 s p.epilogue).regs r) :
    loopOut.regs r = 0 := by
  let entry := arun 0 (initialAStateWithArray arr) p.init
  have hzeroWord := initialAStateWithArray_word arr harr
  have hentryWord : WordState entry := arun_word 0 p.init
    (initialAStateWithArray arr) hzeroWord.1 hzeroWord.2
  have hloopWord : WordState loopOut :=
    hloopOut ▸ fold_arun_word p.body (List.range p.loopCount) entry hentryWord
  have houtEq := AProgram.eq_arun_of_runFromArray_eq_some p arr out hrun
  have hfinalZero : (arun 0 loopOut p.epilogue).regs r = 0 := by
    rw [hloopOut, ← houtEq]
    exact hout
  exact Nat.eq_zero_of_le_zero
    (Nat.le_trans (hepiMono loopOut hloopWord) (Nat.le_of_eq hfinalZero))

def runtimeClauseEntry (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) runtimeClauseSourceProgram.init

def runtimeClausePrefix (arr : Nat → Nat) (j : Nat) : AState :=
  (List.range j).foldl
    (fun s index => arun index s runtimeClauseSourceProgram.body)
    (runtimeClauseEntry arr)

def runtimeOriginalEntry (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr)
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init

def runtimeOriginalPrefix (arr : Nat → Nat) (j : Nat) : AState :=
  (List.range j).foldl
    (fun s index => arun index s runtimeProductionCfg.body)
    (runtimeOriginalEntry arr)

theorem runtimeClausePrefix_sourceAgree (arr : Nat → Nat) (j : Nat) :
    SourceAgree 400 (runtimeClausePrefix arr j)
      (runtimeOriginalPrefix arr j) := by
  have hp := r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed
  have hinit : SourceAgree 400 (runtimeClauseEntry arr)
      (runtimeOriginalEntry arr) := by
    rw [runtimeClauseEntry, runtimeOriginalEntry,
      runtimeClauseSourceProgram_init]
    exact auditBlock_sourceAgree runtimeProductionCfg.sc 0 _ _ _ hp.2.1
      (SourceAgree.refl 400 (initialAStateWithArray arr))
  induction j with
  | zero => exact hinit
  | succ j ih =>
      rw [runtimeClausePrefix, runtimeOriginalPrefix, List.range_succ,
        List.foldl_append, List.foldl_singleton,
        runtimeClauseSourceProgram_body]
      exact auditBlock_sourceAgree runtimeProductionCfg.sc j _ _ _ hp.2.2.1 ih

/-- A zero source latch exposes a zero latch before and after every dynamic
instrumented production body. -/
theorem runtime_every_body_latch_zero (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState)
    (hrun : runtimeClauseSourceProgram.runFromArray arr = some out)
    (houtZero : out.regs auditReg = 0) :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      (runtimeClausePrefix arr j).regs auditReg = 0 ∧
      (arun j (runtimeClausePrefix arr j)
        runtimeClauseSourceProgram.body).regs auditReg = 0 := by
  let p := runtimeClauseSourceProgram
  let N := p.loopCount
  let entry := runtimeClauseEntry arr
  let loopOut := (List.range N).foldl
    (fun s index => arun index s p.body) entry
  have hp := r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed
  have hzeroWord := initialAStateWithArray_word arr harr
  have hentryWord : WordState entry := arun_word 0 p.init
    (initialAStateWithArray arr) hzeroWord.1 hzeroWord.2
  have hstepMono : ∀ k s, WordState s →
      s.regs auditReg ≤ (arun k s p.body).regs auditReg := by
    intro k s hs
    rw [runtimeClauseSourceProgram_body]
    exact auditBlock_audit_mono runtimeProductionCfg.sc k _ _ hp.2.2.1 hs
  have hepiMono : ∀ s, WordState s →
      s.regs auditReg ≤ (arun 0 s p.epilogue).regs auditReg := by
    intro s hs
    rw [runtimeClauseSourceProgram_epilogue]
    exact auditBlock_audit_mono runtimeProductionCfg.sc 0 _ _ hp.2.2.2 hs
  have hloopZero : loopOut.regs auditReg = 0 := by
    apply loop_zero_of_runFromArray p arr harr out auditReg hrun houtZero
      loopOut
    · rfl
    · exact hepiMono
  intro j hj
  have hN : N = runtimeProductionCfg.period * runtimeProductionCfg.segCount :=
    runtimeClauseSourceProgram_loopCount
  rw [← hN] at hj
  let pre := runtimeClausePrefix arr j
  let after := arun j pre p.body
  have hpreWord : WordState pre :=
    fold_arun_word p.body (List.range j) entry hentryWord
  have hafterWord : WordState after := arun_word j p.body pre
    hpreWord.1 hpreWord.2
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by dsimp only [tailLen]; omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htailMono := fold_step_mono p.body auditReg hstepMono tail after
    hafterWord
  have hloopZero' :
      ((List.range N).foldl (fun s index => arun index s p.body)
        entry).regs auditReg = 0 := by simpa only [loopOut] using hloopZero
  rw [hrange, List.foldl_append] at hloopZero'
  change (tail.foldl (fun s index => arun index s p.body)
    after).regs auditReg = 0 at hloopZero'
  have hafterZero : after.regs auditReg = 0 := Nat.eq_zero_of_le_zero
    (Nat.le_trans htailMono (Nat.le_of_eq hloopZero'))
  have hpreZero : pre.regs auditReg = 0 := Nat.eq_zero_of_le_zero
    (Nat.le_trans (hstepMono j pre hpreWord) (Nat.le_of_eq hafterZero))
  exact ⟨hpreZero, hafterZero⟩

#print axioms auditBlock_audit_mono
#print axioms auditBlock_sourceAgree
#print axioms runtimeClausePrefix_sourceAgree
#print axioms runtime_every_body_latch_zero

end LeanCompCert.Ports.R2SegSieve.R2ClauseAudit
