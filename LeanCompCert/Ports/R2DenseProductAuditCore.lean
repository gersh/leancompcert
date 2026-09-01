import LeanCompCert.Ports.R2ProductAuditTelescope
import LeanCompCert.Ports.R2DenseHead
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Core product-transition audit for dense R₂ producers

This is the dense analogue of `runtimeProductSourceProgram`: the guard is
inserted immediately after every literal product multiplication in the actual
dense producer.  The instrumented program is itself the producer, so its final
memory and its no-wrap evidence belong to one causal source execution.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanCompCert.Ports.R2SegSieve.R2DenseProductAudit

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.R2SegSieve.R2ProductAudit

def acceptBody : List AInstr :=
  [ .scalar (.binop R2ProductAudit.auditReg .bor
      (.reg R2ProductAudit.auditReg) (.reg rVMark)) ]

def sourceProgram (c : R2Cfg) (seed : R2Seed) : AProgram :=
  let source := r2DenseHeadProgram c seed
  { regCount := 406
    arrayLen := source.arrayLen
    loopCount := c.markSteps
    init := auditBlock source.init
    body := auditBlock source.body
    epilogue := acceptBody
    output := R2ProductAudit.auditReg }

@[simp] theorem sourceProgram_loopCount (c : R2Cfg) (seed : R2Seed) :
    (sourceProgram c seed).loopCount = c.markSteps := rfl
@[simp] theorem sourceProgram_init (c : R2Cfg) (seed : R2Seed) :
    (sourceProgram c seed).init = auditBlock (r2DenseHeadProgram c seed).init := rfl
@[simp] theorem sourceProgram_body (c : R2Cfg) (seed : R2Seed) :
    (sourceProgram c seed).body = auditBlock c.denseHeadBody := rfl
@[simp] theorem sourceProgram_epilogue (c : R2Cfg) (seed : R2Seed) :
    (sourceProgram c seed).epilogue = acceptBody := rfl

theorem sourceProgram_wf (c : R2Cfg) (seed : R2Seed) :
    (sourceProgram c seed).WF := by
  have hp := r2DenseHeadProgram_wf c seed
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  refine ⟨?_, auditBlock_wf _ hinit, auditBlock_wf _ hbody, ?_⟩
  · show R2ProductAudit.auditReg < 406
    decide
  · intro i hi
    simp [sourceProgram, acceptBody] at hi
    subst i
    change AInstr.WF 406
      (.scalar (.binop R2ProductAudit.auditReg .bor
        (.reg R2ProductAudit.auditReg) (.reg rVMark)))
    decide

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

private theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  exact ⟨Nat.eq_zero_of_le_zero (Nat.le_trans Nat.left_le_or (Nat.le_of_eq h)),
    Nat.eq_zero_of_le_zero (Nat.le_trans Nat.right_le_or (Nat.le_of_eq h))⟩

theorem acceptBody_zero_sound (s : AState) (hword : WordState s)
    (hzero : (arun 0 s acceptBody).regs R2ProductAudit.auditReg = 0) :
    s.regs R2ProductAudit.auditReg = 0 ∧ s.regs rVMark = 0 := by
  have hor := or_lt_M (hword.1 R2ProductAudit.auditReg) (hword.1 rVMark)
  have hrun : (arun 0 s acceptBody).regs R2ProductAudit.auditReg =
      (s.regs R2ProductAudit.auditReg ||| s.regs rVMark) % M := by
    simp [acceptBody, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp]
  rw [Nat.mod_eq_of_lt hor] at hrun
  exact or_eq_zero (hrun.symm.trans hzero)

def denseProductBeforeBody (c : R2Cfg) : List AInstr :=
  c.denseHeadBody.take 34

def denseProductAfterBody (c : R2Cfg) : List AInstr :=
  c.denseHeadBody.drop 35

theorem denseBody_eq_product_split (c : R2Cfg) :
    c.denseHeadBody = denseProductBeforeBody c ++ [productMulInstr] ++
      denseProductAfterBody c := by
  rfl

theorem auditBlock_denseProductBeforeBody (c : R2Cfg) :
    auditBlock (denseProductBeforeBody c) = denseProductBeforeBody c := by
  rfl

theorem auditBlock_denseBody_eq_product_split (c : R2Cfg) :
    auditBlock c.denseHeadBody = denseProductBeforeBody c ++
      [productMulInstr] ++ productGuardBody ++
        auditBlock (denseProductAfterBody c) := by
  rw [denseBody_eq_product_split]
  change auditBlock (denseProductBeforeBody c) ++ auditBlock [productMulInstr] ++
      auditBlock (denseProductAfterBody c) = _
  rw [auditBlock_denseProductBeforeBody]
  rfl

theorem denseProductBeforeBody_frames_audit (c : R2Cfg) :
    writes auditReg (denseProductBeforeBody c) = false := by rfl

/-- One accepted instrumented dense body proves exact word room at its literal
resident product multiplication. -/
theorem product_fits_of_audited_dense_body_zero
    (c : R2Cfg) (k : Nat) (s : AState)
    (hafterWF : ∀ i ∈ denseProductAfterBody c, i.WF 400)
    (hword : WordState s) (hin : s.regs auditReg = 0)
    (hout : (arun k s (auditBlock c.denseHeadBody)).regs auditReg = 0) :
    let pre := arun k s (denseProductBeforeBody c)
    pre.regs 35 * pre.regs rBp < M := by
  let pre := arun k s (denseProductBeforeBody c)
  let multiplied := astep k pre productMulInstr
  let guarded := arun k multiplied productGuardBody
  have hpreWord : WordState pre :=
    arun_word k (denseProductBeforeBody c) s hword.1 hword.2
  have hpreAudit : pre.regs auditReg = 0 :=
    (arun_frame k auditReg _ (denseProductBeforeBody_frames_audit c) s).trans hin
  have hmulWord : WordState multiplied := by
    change WordState (arun k pre [productMulInstr])
    exact arun_word k [productMulInstr] pre hpreWord.1 hpreWord.2
  have hmulAudit : multiplied.regs auditReg = 0 := by
    exact (astep_frame k auditReg pre productMulInstr (by decide)).trans hpreAudit
  have hguardZero : guarded.regs auditReg = 0 := by
    rw [auditBlock_denseBody_eq_product_split, arun_append, arun_append,
      arun_append] at hout
    have hguardWord : WordState guarded :=
      arun_word k productGuardBody multiplied hmulWord.1 hmulWord.2
    have hsuffix := auditBlock_audit_mono k (denseProductAfterBody c) guarded
      hafterWF hguardWord
    exact Nat.eq_zero_of_le_zero (Nat.le_trans hsuffix (Nat.le_of_eq (by
      simpa only [guarded, multiplied, pre, arun] using hout)))
  have hx : multiplied.regs 35 = pre.regs 35 := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp]
  have hy : multiplied.regs rBp = pre.regs rBp := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp, rBp]
  have hproduct : multiplied.regs 36 = pre.regs 35 * pre.regs rBp % M := by
    simp [multiplied, productMulInstr, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp]
  exact product_fits_of_guard_zero k multiplied (pre.regs 35) (pre.regs rBp)
    hx hy hproduct (hpreWord.1 _) (hpreWord.1 _) hmulAudit hguardZero

def auditedEntry (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) (sourceProgram c seed).init

def auditedPrefix (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (j : Nat) : AState :=
  (List.range j).foldl
    (fun s k => arun k s (sourceProgram c seed).body)
    (auditedEntry c seed arr)

def auditedLoop (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) : AState :=
  auditedPrefix c seed arr c.markSteps

def originalEntry (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) (r2DenseHeadProgram c seed).init

def originalPrefix (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (j : Nat) : AState :=
  (List.range j).foldl
    (fun s k => arun k s (r2DenseHeadProgram c seed).body)
    (originalEntry c seed arr)

def auditedBeforeMul (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (j : Nat) : AState :=
  arun j (auditedPrefix c seed arr j) (denseProductBeforeBody c)

def originalBeforeMul (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (j : Nat) : AState :=
  arun j (originalPrefix c seed arr j) (denseProductBeforeBody c)

theorem auditedPrefix_sourceAgree
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) (j : Nat) :
    SourceAgree 400 (auditedPrefix c seed arr j)
      (originalPrefix c seed arr j) := by
  have hp := r2DenseHeadProgram_wf c seed
  have hinit : SourceAgree 400 (auditedEntry c seed arr)
      (originalEntry c seed arr) := by
    exact auditBlock_sourceAgree 0 _ _ _ hp.2.1
      (SourceAgree.refl 400 (initialAStateWithArray arr))
  exact auditFold_sourceAgree _ hp.2.2.1 (List.range j) _ _ hinit

theorem auditedBeforeMul_sourceAgree
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) (j : Nat) :
    SourceAgree 400 (auditedBeforeMul c seed arr j)
      (originalBeforeMul c seed arr j) := by
  have hp := r2DenseHeadProgram_wf c seed
  have hprefix := auditedPrefix_sourceAgree c seed arr j
  exact arun_sourceAgree j (denseProductBeforeBody c) _ _
    (fun i hi => hp.2.2.1 i (List.mem_of_mem_take hi)) hprefix

theorem fold_word (body : List AInstr) :
    ∀ (xs : List Nat) (s : AState), WordState s →
      WordState (xs.foldl (fun q k => arun k q body) s) := by
  intro xs
  induction xs with
  | nil => intro s hs; exact hs
  | cons k ks ih =>
      intro s hs
      exact ih _ (arun_word k body s hs.1 hs.2)

theorem denseSourceBody_wf (c : R2Cfg) (seed : R2Seed) :
    ∀ i ∈ c.denseHeadBody, i.WF 400 := by
  have hp := r2DenseHeadProgram_wf c seed
  simpa [r2DenseHeadProgram, regCount] using hp.2.2.1

theorem auditedEntry_word (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) : WordState (auditedEntry c seed arr) := by
  exact arun_word 0 (sourceProgram c seed).init (initialAStateWithArray arr)
    (initialAStateWithArray_word arr harr).1
    (initialAStateWithArray_word arr harr).2

theorem denseAuditBody_mono (c : R2Cfg) (seed : R2Seed)
    (k : Nat) (s : AState) (hs : WordState s) :
    s.regs R2ProductAudit.auditReg ≤
      (arun k s (sourceProgram c seed).body).regs
        R2ProductAudit.auditReg := by
  rw [sourceProgram_body]
  exact auditBlock_audit_mono k c.denseHeadBody s
    (denseSourceBody_wf c seed) hs

theorem auditedLoop_eq_rangeFold (c : R2Cfg) (seed : R2Seed)
    (arr : Nat → Nat) :
    auditedLoop c seed arr =
      (List.range c.markSteps).foldl
        (fun s k => arun k s (sourceProgram c seed).body)
        (auditedEntry c seed arr) := rfl

/- Body-opaque range telescope.  This theorem knows only that one step and a
suffix fold preserve words and monotonically increase the selected register. -/
theorem rangeFold_prefix_step_zero
    (body : List AInstr) (entry : AState) (N audit : Nat)
    (hentry : WordState entry)
    (hmono : ∀ k s, WordState s →
      s.regs audit ≤ (arun k s body).regs audit)
    (hfinal : ((List.range N).foldl (fun s k => arun k s body) entry).regs
      audit = 0)
    (j : Nat) (hj : j < N) :
    let pre := (List.range j).foldl (fun s k => arun k s body) entry
    pre.regs audit = 0 ∧ (arun j pre body).regs audit = 0 := by
  let pre := (List.range j).foldl (fun s k => arun k s body) entry
  let after := arun j pre body
  have hpreWord : WordState pre := fold_word body (List.range j) entry hentry
  have hafterWord : WordState after := arun_word j body pre hpreWord.1 hpreWord.2
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
  have htailMono : after.regs audit ≤
      (tail.foldl (fun s k => arun k s body) after).regs audit := by
    have foldMono : ∀ (xs : List Nat) (s : AState), WordState s →
        s.regs audit ≤ (xs.foldl (fun q k => arun k q body) s).regs audit := by
      intro xs
      induction xs with
      | nil => intro s _; exact Nat.le_refl _
      | cons k ks ih =>
        intro s hs
        exact Nat.le_trans (hmono k s hs)
          (ih _ (arun_word k body s hs.1 hs.2))
    exact foldMono tail after hafterWord
  rw [hrange, List.foldl_append] at hfinal
  change (tail.foldl (fun s k => arun k s body) after).regs audit = 0 at hfinal
  have hafterZero : after.regs audit = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_trans htailMono (Nat.le_of_eq hfinal))
  have hpreZero : pre.regs audit = 0 :=
    Nat.eq_zero_of_le_zero
      (Nat.le_trans (hmono j pre hpreWord) (Nat.le_of_eq hafterZero))
  exact ⟨hpreZero, hafterZero⟩

theorem rangeFold_local_of_final_zero
    (body : List AInstr) (entry : AState) (N audit : Nat)
    (hentry : WordState entry)
    (hmono : ∀ k s, WordState s →
      s.regs audit ≤ (arun k s body).regs audit)
    (hfinal : ((List.range N).foldl (fun s k => arun k s body) entry).regs
      audit = 0)
    (P : Nat → AState → Prop)
    (hlocal : ∀ j s, WordState s → s.regs audit = 0 →
      (arun j s body).regs audit = 0 → P j s) :
    ∀ j, j < N →
      P j ((List.range j).foldl (fun s k => arun k s body) entry) := by
  intro j hj
  have hz := rangeFold_prefix_step_zero body entry N audit hentry hmono
    hfinal j hj
  exact hlocal j _ (fold_word body (List.range j) entry hentry) hz.1 hz.2


#print axioms sourceProgram_wf
#print axioms product_fits_of_audited_dense_body_zero
#print axioms auditedPrefix_sourceAgree
#print axioms auditedBeforeMul_sourceAgree
#print axioms rangeFold_local_of_final_zero

end LeanCompCert.Ports.R2SegSieve.R2DenseProductAudit
