import LeanCompCert.Ports.R2ProductAuditSound
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Telescope for the compiled R₂ exact-product audit

This file propagates a zero terminal product latch back to every dynamic
execution of the guarded multiplication.  The long production loop remains a
symbolic `List.foldl`; no production computation is evaluated by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ProductAudit

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

def productGuardPrefix : List AInstr := productGuardBody.take 5

def productGuardFinal : AInstr :=
  .scalar (.binop auditReg .bor (.reg auditReg) (.reg badReg))

theorem productGuardBody_eq_prefix :
    productGuardBody = productGuardPrefix ++ [productGuardFinal] := by
  rfl

theorem productGuardBody_audit_mono (k : Nat) (s : AState)
    (hword : WordState s) :
    s.regs auditReg ≤ (arun k s productGuardBody).regs auditReg := by
  let mid := arun k s productGuardPrefix
  have hmidWord : WordState mid :=
    arun_word k productGuardPrefix s hword.1 hword.2
  have hframe : mid.regs auditReg = s.regs auditReg := by
    exact arun_frame k auditReg productGuardPrefix (by decide) s
  have hor : mid.regs auditReg ||| mid.regs badReg < M :=
    or_lt_M (hmidWord.1 _) (hmidWord.1 _)
  rw [productGuardBody_eq_prefix, arun_append]
  change s.regs auditReg ≤
    (astep k mid productGuardFinal).regs auditReg
  simp only [productGuardFinal, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, AState.writeReg,
    denoteOperand, denoteOp]
  rw [Nat.mod_eq_of_lt hor, hframe]
  exact Nat.left_le_or

private theorem wf400_not_write_audit (i : AInstr) (hi : i.WF 400) :
    instrWrites auditReg i = false := by
  cases i with
  | scalar instr =>
      cases instr <;>
        simp only [AInstr.WF, Instr.WF, Operand.WF] at hi <;>
        simp [instrWrites, LeanCompCert.Verified.InstrBlock.sdest, auditReg] <;>
        omega
  | load dest idx =>
      simp only [AInstr.WF] at hi
      simp [instrWrites, auditReg]
      omega
  | store idx src => rfl

theorem auditInstr_audit_mono (k : Nat) (s : AState) (i : AInstr)
    (hi : i.WF 400) (hword : WordState s) :
    s.regs auditReg ≤ (arun k s (auditInstr i)).regs auditReg := by
  have hstepFrame : (astep k s i).regs auditReg = s.regs auditReg :=
    astep_frame k auditReg s i (wf400_not_write_audit i hi)
  by_cases hmul : isProductMul i
  · have hstepWord : WordState (astep k s i) := by
      change WordState (arun k s [i])
      exact arun_word k [i] s hword.1 hword.2
    rw [auditInstr, if_pos hmul, arun_append]
    change s.regs auditReg ≤
      (arun k (astep k s i) productGuardBody).regs auditReg
    rw [← hstepFrame]
    exact productGuardBody_audit_mono k (astep k s i) hstepWord
  · rw [auditInstr, if_neg hmul, List.append_nil]
    change s.regs auditReg ≤ (astep k s i).regs auditReg
    omega

theorem auditBlock_audit_mono (k : Nat) :
    ∀ (xs : List AInstr) (s : AState),
      (∀ i ∈ xs, i.WF 400) → WordState s →
      s.regs auditReg ≤ (arun k s (auditBlock xs)).regs auditReg := by
  intro xs
  induction xs with
  | nil => intro s _ _; exact Nat.le_refl _
  | cons i rest ih =>
      intro s hwf hword
      have hi : i.WF 400 := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF 400 := by
        intro a ha
        exact hwf a (by simp [ha])
      let mid := arun k s (auditInstr i)
      have hfirst := auditInstr_audit_mono k s i hi hword
      have hmidWord : WordState mid :=
        arun_word k (auditInstr i) s hword.1 hword.2
      have htail := ih mid hrest hmidWord
      rw [auditBlock, List.flatMap_cons, arun_append]
      exact Nat.le_trans hfirst htail

theorem productGuardBody_sourceAgree (k : Nat) (s : AState) :
    SourceAgree 400 (arun k s productGuardBody) s := by
  constructor
  · simp [productGuardBody, arun, astep, AState.writeReg]
  · intro j hj
    apply arun_frame k j productGuardBody
    simp [productGuardBody, writes, instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, auditReg, zeroReg, safeReg,
      quotientReg, mismatchReg, badReg]
    omega

theorem auditInstr_sourceAgree (k : Nat) (audited source : AState)
    (i : AInstr) (hi : i.WF 400)
    (hagree : SourceAgree 400 audited source) :
    SourceAgree 400 (arun k audited (auditInstr i))
      (astep k source i) := by
  have hstep := astep_sourceAgree (idx := k) hagree hi
  by_cases hmul : isProductMul i
  · rw [auditInstr, if_pos hmul, arun_append]
    exact SourceAgree.trans
      (productGuardBody_sourceAgree k (astep k audited i)) hstep
  · simpa only [auditInstr, if_neg hmul, List.append_nil, arun] using hstep

theorem auditBlock_sourceAgree (k : Nat) :
    ∀ (xs : List AInstr) (audited source : AState),
      (∀ i ∈ xs, i.WF 400) → SourceAgree 400 audited source →
      SourceAgree 400 (arun k audited (auditBlock xs))
        (arun k source xs) := by
  intro xs
  induction xs with
  | nil => intro audited source _ hagree; exact hagree
  | cons i rest ih =>
      intro audited source hwf hagree
      have hi : i.WF 400 := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF 400 := by
        intro a ha
        exact hwf a (by simp [ha])
      have hfirst := auditInstr_sourceAgree k audited source i hi hagree
      have htail := ih (arun k audited (auditInstr i))
        (astep k source i) hrest hfirst
      simpa only [auditBlock, List.flatMap_cons, arun_append, arun] using htail

theorem arun_sourceAgree (k : Nat) :
    ∀ (xs : List AInstr) (a s : AState),
      (∀ i ∈ xs, i.WF 400) → SourceAgree 400 a s →
      SourceAgree 400 (arun k a xs) (arun k s xs) := by
  intro xs
  induction xs with
  | nil => intro a s _ hagree; exact hagree
  | cons i rest ih =>
      intro a s hwf hagree
      have hi : i.WF 400 := hwf i (by simp)
      have hrest : ∀ x ∈ rest, x.WF 400 := by
        intro x hx
        exact hwf x (by simp [hx])
      exact ih (astep k a i) (astep k s i) hrest
        (astep_sourceAgree (idx := k) hagree hi)

theorem auditFold_sourceAgree (body : List AInstr)
    (hbody : ∀ i ∈ body, i.WF 400) :
    ∀ (indices : List Nat) (audited source : AState),
      SourceAgree 400 audited source →
      SourceAgree 400
        (indices.foldl (fun s k => arun k s (auditBlock body)) audited)
        (indices.foldl (fun s k => arun k s body) source) := by
  intro indices
  induction indices with
  | nil => intro audited source hagree; exact hagree
  | cons k rest ih =>
      intro audited source hagree
      exact ih _ _ (auditBlock_sourceAgree k body audited source hbody hagree)

theorem auditFold_audit_mono (body : List AInstr)
    (hbody : ∀ i ∈ body, i.WF 400) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      s.regs auditReg ≤
        (indices.foldl (fun st k => arun k st (auditBlock body)) s).regs
          auditReg := by
  intro indices
  induction indices with
  | nil => intro s _; exact Nat.le_refl _
  | cons k rest ih =>
      intro s hword
      let mid := arun k s (auditBlock body)
      have hfirst := auditBlock_audit_mono k body s hbody hword
      have hmidWord : WordState mid :=
        arun_word k (auditBlock body) s hword.1 hword.2
      have htail := ih mid hmidWord
      simpa only [List.foldl_cons] using Nat.le_trans hfirst htail

theorem auditFold_word (body : List AInstr) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      WordState
        (indices.foldl (fun st k => arun k st (auditBlock body)) s) := by
  intro indices
  induction indices with
  | nil => intro s hs; exact hs
  | cons k rest ih =>
      intro s hs
      apply ih
      exact arun_word k (auditBlock body) s hs.1 hs.2

/-! ## The unique guarded instruction in an R₂ body -/

def productBeforeBody (c : R2Cfg) : List AInstr := c.body.take 34

def productAfterBody (c : R2Cfg) : List AInstr := c.body.drop 35

theorem body_eq_product_split (c : R2Cfg) :
    c.body = productBeforeBody c ++ [productMulInstr] ++
      productAfterBody c := by
  rfl

theorem auditBlock_productBeforeBody (c : R2Cfg) :
    auditBlock (productBeforeBody c) = productBeforeBody c := by
  rfl

theorem auditBlock_productAfterBody (c : R2Cfg) :
    auditBlock (productAfterBody c) = productAfterBody c := by
  set_option maxRecDepth 20000 in
    rfl

theorem auditBlock_body_eq_product_split (c : R2Cfg) :
    auditBlock c.body = productBeforeBody c ++ [productMulInstr] ++
      productGuardBody ++ productAfterBody c := by
  rw [body_eq_product_split]
  change auditBlock (productBeforeBody c) ++ auditBlock [productMulInstr] ++
      auditBlock (productAfterBody c) =
    productBeforeBody c ++ [productMulInstr] ++ productGuardBody ++
      productAfterBody c
  rw [auditBlock_productBeforeBody, auditBlock_productAfterBody]
  rfl

theorem productBeforeBody_frames_audit (c : R2Cfg) :
    writes auditReg (productBeforeBody c) = false := by
  rfl

theorem productAfterBody_frames_audit (c : R2Cfg) :
    writes auditReg (productAfterBody c) = false := by
  set_option maxRecDepth 20000 in
    rfl

/-- A zero product latch after one instrumented R₂ body proves that body's
natural-number product fits in one machine word. -/
theorem product_fits_of_audited_body_zero (c : R2Cfg) (k : Nat) (s : AState)
    (hword : WordState s) (hin : s.regs auditReg = 0)
    (hout : (arun k s (auditBlock c.body)).regs auditReg = 0) :
    let pre := arun k s (productBeforeBody c)
    pre.regs 35 * pre.regs rBp < M := by
  let pre := arun k s (productBeforeBody c)
  let multiplied := astep k pre productMulInstr
  let guarded := arun k multiplied productGuardBody
  have hpreWord : WordState pre :=
    arun_word k (productBeforeBody c) s hword.1 hword.2
  have hpreAudit : pre.regs auditReg = 0 := by
    exact (arun_frame k auditReg (productBeforeBody c)
      (productBeforeBody_frames_audit c) s).trans hin
  have hmulWord : WordState multiplied := by
    change WordState (arun k pre [productMulInstr])
    exact arun_word k [productMulInstr] pre hpreWord.1 hpreWord.2
  have hmulAudit : multiplied.regs auditReg = 0 := by
    have hframe := astep_frame k auditReg pre productMulInstr (by decide)
    exact hframe.trans hpreAudit
  have hguardZero : guarded.regs auditReg = 0 := by
    rw [auditBlock_body_eq_product_split, arun_append, arun_append,
      arun_append] at hout
    have hsuffix := arun_frame k auditReg (productAfterBody c)
      (productAfterBody_frames_audit c) guarded
    apply hsuffix.symm.trans
    simpa only [guarded, multiplied, pre, arun] using hout
  have hx : multiplied.regs 35 = pre.regs 35 := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp]
  have hy : multiplied.regs rBp = pre.regs rBp := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp, rBp]
  have hproduct : multiplied.regs 36 =
      pre.regs 35 * pre.regs rBp % M := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp]
  exact product_fits_of_guard_zero k multiplied
    (pre.regs 35) (pre.regs rBp) hx hy hproduct
    (hpreWord.1 _) (hpreWord.1 _) hmulAudit hguardZero

/-! ## Production fold telescope -/

def runtimeProductEntry (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) runtimeProductSourceProgram.init

def runtimeProductLoopOut (arr : Nat → Nat) : AState :=
  (List.range runtimeProductSourceProgram.loopCount).foldl
      (fun s index => arun index s runtimeProductSourceProgram.body)
      (runtimeProductEntry arr)

def runtimeProductPrefix (arr : Nat → Nat) (j : Nat) : AState :=
  (List.range j).foldl
    (fun s index => arun index s runtimeProductSourceProgram.body)
    (runtimeProductEntry arr)

def runtimeProductBeforeMul (arr : Nat → Nat) (j : Nat) : AState :=
  arun j (runtimeProductPrefix arr j)
    (productBeforeBody runtimeProductionCfg)

def runtimeOriginalEntry (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr)
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init

def runtimeOriginalPrefix (arr : Nat → Nat) (j : Nat) : AState :=
  (List.range j).foldl
    (fun s index => arun index s runtimeProductionCfg.body)
    (runtimeOriginalEntry arr)

def runtimeOriginalBeforeMul (arr : Nat → Nat) (j : Nat) : AState :=
  arun j (runtimeOriginalPrefix arr j)
    (productBeforeBody runtimeProductionCfg)

theorem runtimeProductBeforeMul_sourceAgree (arr : Nat → Nat) (j : Nat) :
    SourceAgree 400 (runtimeProductBeforeMul arr j)
      (runtimeOriginalBeforeMul arr j) := by
  have hp := r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed
  have hinit : SourceAgree 400 (runtimeProductEntry arr)
      (runtimeOriginalEntry arr) := by
    rw [runtimeProductEntry, runtimeOriginalEntry,
      runtimeProductSourceProgram_init]
    exact auditBlock_sourceAgree 0
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init
      (initialAStateWithArray arr) (initialAStateWithArray arr) hp.2.1
      (SourceAgree.refl 400 (initialAStateWithArray arr))
  have hprefix : SourceAgree 400 (runtimeProductPrefix arr j)
      (runtimeOriginalPrefix arr j) := by
    rw [runtimeProductPrefix, runtimeOriginalPrefix,
      runtimeProductSourceProgram_body]
    exact auditFold_sourceAgree runtimeProductionCfg.body hp.2.2.1
      (List.range j) (runtimeProductEntry arr) (runtimeOriginalEntry arr) hinit
  have hbefore := arun_sourceAgree j
    (productBeforeBody runtimeProductionCfg)
    (runtimeProductPrefix arr j) (runtimeOriginalPrefix arr j)
    (by
      intro i hi
      exact hp.2.2.1 i (List.mem_of_mem_take hi)) hprefix
  exact hbefore

private theorem fold_arun_word (body : List AInstr) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      WordState (indices.foldl (fun st k => arun k st body) s) := by
  intro indices
  induction indices with
  | nil => intro s hs; exact hs
  | cons k rest ih =>
      intro s hs
      apply ih
      exact arun_word k body s hs.1 hs.2

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
      have hfirst := hmono k s hs
      have hmidWord : WordState mid := arun_word k body s hs.1 hs.2
      have htail := ih mid hmidWord
      simpa only [List.foldl_cons] using Nat.le_trans hfirst htail

/-- Parametric receipt bridge: terminal zero plus monotonicity of the
epilogue suffices to expose a zero loop latch, without specializing the
enormous source-fold expression. -/
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
  have hentryWord : WordState entry :=
    arun_word 0 p.init (initialAStateWithArray arr)
      hzeroWord.1 hzeroWord.2
  have hloopWord : WordState loopOut :=
    hloopOut ▸ fold_arun_word p.body (List.range p.loopCount) entry hentryWord
  have houtEq := AProgram.eq_arun_of_runFromArray_eq_some p arr out hrun
  have hfinalZero : (arun 0 loopOut p.epilogue).regs r = 0 := by
    rw [hloopOut]
    rw [← houtEq]
    exact hout
  have hle := hepiMono loopOut hloopWord
  exact Nat.eq_zero_of_le_zero
    (Nat.le_trans hle (Nat.le_of_eq hfinalZero))

/-- A successful product-instrumented source run whose terminal latch is zero
certifies the exact product at every production iteration. -/
theorem runtime_every_product_fits_of_source_run (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState)
    (hrun : runtimeProductSourceProgram.runFromArray arr = some out)
    (houtZero : out.regs auditReg = 0) :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      (runtimeProductBeforeMul arr j).regs 35 *
        (runtimeProductBeforeMul arr j).regs rBp < M := by
  let p := runtimeProductSourceProgram
  let c := runtimeProductionCfg
  let N := p.loopCount
  let entry := arun 0 (initialAStateWithArray arr) p.init
  let loopOut := (List.range N).foldl
    (fun s index => arun index s p.body) entry
  have hp := r2RuntimeProgram_wf c runtimeProductionSeed
  have hzeroWord := initialAStateWithArray_word arr harr
  have hentryWord : WordState entry := by
    exact arun_word 0 p.init
      (initialAStateWithArray arr) hzeroWord.1 hzeroWord.2
  have hloopWord : WordState loopOut := by
    exact fold_arun_word p.body (List.range N) entry hentryWord
  have hstepMono : ∀ k s, WordState s →
      s.regs auditReg ≤ (arun k s p.body).regs auditReg := by
    intro k s hs
    rw [show p.body = auditBlock c.body by
      exact runtimeProductSourceProgram_body]
    exact auditBlock_audit_mono k c.body s hp.2.2.1 hs
  have hepiMono : ∀ s, WordState s →
      s.regs auditReg ≤ (arun 0 s p.epilogue).regs auditReg := by
    intro s hs
    rw [show p.epilogue = auditBlock c.epilogue by
      exact runtimeProductSourceProgram_epilogue]
    exact auditBlock_audit_mono 0 c.epilogue s hp.2.2.2 hs
  have hloopZero : loopOut.regs auditReg = 0 := by
    apply loop_zero_of_runFromArray p arr harr out auditReg hrun houtZero
      loopOut
    · rfl
    · exact hepiMono
  intro j hj
  have hN : N = c.period * c.segCount :=
    runtimeProductSourceProgram_loopCount
  rw [← hN] at hj
  let pre := runtimeProductPrefix arr j
  let after := arun j pre p.body
  have hpreWord : WordState pre := by
    exact fold_arun_word p.body (List.range j) entry hentryWord
  have hafterWord : WordState after :=
    arun_word j p.body pre hpreWord.1 hpreWord.2
  have hbodyMono := hstepMono j pre hpreWord
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [tailLen]
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htailMono := fold_step_mono p.body auditReg hstepMono tail after
    hafterWord
  have hloopZero' :
      ((List.range N).foldl
        (fun s index => arun index s p.body) entry).regs
          auditReg = 0 := by
    simpa only [loopOut] using hloopZero
  rw [hrange, List.foldl_append] at hloopZero'
  change
    (tail.foldl (fun s index => arun index s p.body)
      after).regs auditReg = 0 at hloopZero'
  have hafterZero : after.regs auditReg = 0 :=
    Nat.eq_zero_of_le_zero
      (Nat.le_trans htailMono (Nat.le_of_eq hloopZero'))
  have hpreZero : pre.regs auditReg = 0 :=
    Nat.eq_zero_of_le_zero
      (Nat.le_trans hbodyMono (Nat.le_of_eq hafterZero))
  have hafterZero' :
      (arun j pre (auditBlock c.body)).regs auditReg = 0 := by
    rw [← show p.body = auditBlock c.body by
      exact runtimeProductSourceProgram_body]
    exact hafterZero
  have hfit := product_fits_of_audited_body_zero c j pre hpreWord hpreZero
    hafterZero'
  simpa only [runtimeProductBeforeMul, runtimeProductPrefix, pre, c] using hfit

theorem runtime_every_original_product_fits_of_source_run (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState)
    (hrun : runtimeProductSourceProgram.runFromArray arr = some out)
    (houtZero : out.regs auditReg = 0) :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      (runtimeOriginalBeforeMul arr j).regs 35 *
        (runtimeOriginalBeforeMul arr j).regs rBp < M := by
  intro j hj
  have hfit := runtime_every_product_fits_of_source_run arr harr out hrun
    houtZero j hj
  have hagree := runtimeProductBeforeMul_sourceAgree arr j
  rw [← hagree.2 35 (by decide), ← hagree.2 rBp (by decide)]
  exact hfit

#print axioms productGuardBody_audit_mono
#print axioms auditBlock_audit_mono
#print axioms auditBlock_body_eq_product_split
#print axioms product_fits_of_audited_body_zero
#print axioms runtime_every_product_fits_of_source_run
#print axioms runtime_every_original_product_fits_of_source_run

end LeanCompCert.Ports.R2SegSieve.R2ProductAudit
