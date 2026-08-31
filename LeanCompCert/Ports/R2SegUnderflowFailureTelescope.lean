import LeanCompCert.Ports.R2SegLogAccumulator
import LeanCompCert.Verified.ArrayAudit

/-!
# Symbolic telescope for the R₂ negative-jump underflow counter

The strengthened production log body compares every finished negative jump
with the post-linear accumulator *before* executing modular subtraction.  A
dedicated counter `rVSub` records that Boolean comparison.  This file proves
the exact literal increment and telescopes a terminal zero back to every
scheduled body, without evaluating a production state or event table.

Historical receipts predate this counter.  They are deliberately not
imported here: future causal runs must sign the strengthened ten-counter
result layout in `R2SegSieve`.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 10000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock

/-- Mathematical value of the literal audit bit.  The equality test on
`fin` makes it Boolean even for an arbitrary machine state. -/
def underflowFailure (d term positive fin : Nat) : Nat :=
  (if d < term then 1 else 0) *
    (if positive = 0 then 1 else 0) *
      (if fin = 1 then 1 else 0)

theorem underflowFailure_le_one (d term positive fin : Nat) :
    underflowFailure d term positive fin ≤ 1 := by
  simp only [underflowFailure]
  split <;> split <;> split <;> simp

theorem underflowFailure_eq_zero_iff_of_negative_final
    (d term : Nat) :
    underflowFailure d term 0 1 = 0 ↔ term ≤ d := by
  simp [underflowFailure, Nat.not_lt]

/-- Exact scalar semantics of the seven literal audit instructions. -/
theorem logUnderflowAuditInstrs_vsub_run
    (k : Nat) (s : RegState) (d term positive fin sub : Nat)
    (hd : s rD = d) (hterm : s 281 = term)
    (hpositive : s 266 = positive) (hfin : s 247 = fin)
    (hsub : s rVSub = sub)
    (hdM : d < M) (htermM : term < M)
    (hpositiveM : positive < M) (hfinM : fin < M)
    (hroom : sub + underflowFailure d term positive fin < M) :
    (srun k s logUnderflowAuditInstrs) rVSub =
      sub + underflowFailure d term positive fin := by
  have hd' : s 180 = d := by simpa only [rD] using hd
  have hsub' : s 359 = sub := by simpa only [rVSub] using hsub
  by_cases hdt : d < term <;>
    by_cases hp : positive = 0 <;>
    by_cases hf : fin = 1 <;>
    simp_all [logUnderflowAuditInstrs, underflowFailure, srun,
      RegState.set, sdest, sval, denoteOperand, denoteOp, rD, rViol, rVSub,
      Nat.mod_eq_of_lt hdM, Nat.mod_eq_of_lt htermM,
      Nat.mod_eq_of_lt hpositiveM, Nat.mod_eq_of_lt hfinM,
      Nat.mod_eq_of_lt hroom, M]
  all_goals
    have hnot : ¬ d < term := by omega
    simp [hnot]
    omega

/-- Array-state form of the exact audit increment. -/
theorem logUnderflowAuditBody_vsub_run
    (k : Nat) (s : AState) (d term positive fin sub : Nat)
    (hd : s.regs rD = d) (hterm : s.regs 281 = term)
    (hpositive : s.regs 266 = positive) (hfin : s.regs 247 = fin)
    (hsub : s.regs rVSub = sub)
    (hdM : d < M) (htermM : term < M)
    (hpositiveM : positive < M) (hfinM : fin < M)
    (hroom : sub + underflowFailure d term positive fin < M) :
    (arun k s logUnderflowAuditBody).regs rVSub =
      sub + underflowFailure d term positive fin := by
  rw [logUnderflowAuditBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logUnderflowAuditInstrs_vsub_run k s.regs d term positive fin sub
    hd hterm hpositive hfin hsub hdM htermM hpositiveM hfinM hroom

/-! ## One complete scheduled body -/

def bodyBeforeUnderflowAudit (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ c.logBody.take 139

def bodyAfterUnderflowAudit (c : R2Cfg) : List AInstr :=
  c.logBody.drop 146 ++ c.tailBody

theorem body_eq_underflow_stages (c : R2Cfg) :
    c.body = bodyBeforeUnderflowAudit c ++ logUnderflowAuditBody ++
      bodyAfterUnderflowAudit c := by
  rfl

def beforeUnderflowAudit (c : R2Cfg) (k : Nat) (s : AState) : AState :=
  arun k s (bodyBeforeUnderflowAudit c)

/-- Exact compiled underflow bit observed by one scheduled body. -/
def bodyUnderflowBit (c : R2Cfg) (k : Nat) (s : AState) : Nat :=
  let pre := beforeUnderflowAudit c k s
  underflowFailure (pre.regs rD) (pre.regs 281)
    (pre.regs 266) (pre.regs 247)

theorem bodyUnderflowBit_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    bodyUnderflowBit c k s ≤ 1 := by
  exact underflowFailure_le_one _ _ _ _

/-- One scheduled body adds exactly its pre-subtraction audit bit. -/
theorem body_vsub_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hword : WordState s)
    (hroom : s.regs rVSub + bodyUnderflowBit c k s < M) :
    (arun k s c.body).regs rVSub =
      s.regs rVSub + bodyUnderflowBit c k s := by
  let pre := beforeUnderflowAudit c k s
  have hpreWord : WordState pre :=
    arun_word k (bodyBeforeUnderflowAudit c) s hword.1 hword.2
  have hpreSub : pre.regs rVSub = s.regs rVSub :=
    arun_frame k rVSub (bodyBeforeUnderflowAudit c) (by rfl) s
  let audited := arun k pre logUnderflowAuditBody
  have haudit := logUnderflowAuditBody_vsub_run k pre
    (pre.regs rD) (pre.regs 281) (pre.regs 266) (pre.regs 247)
    (s.regs rVSub) rfl rfl rfl rfl hpreSub
    (hpreWord.1 rD) (hpreWord.1 281) (hpreWord.1 266)
    (hpreWord.1 247) (by simpa only [bodyUnderflowBit, pre] using hroom)
  have hsuffix :
      (arun k audited (bodyAfterUnderflowAudit c)).regs rVSub =
        audited.regs rVSub :=
    arun_frame k rVSub (bodyAfterUnderflowAudit c) (by rfl) audited
  rw [body_eq_underflow_stages, arun_append, arun_append]
  exact hsuffix.trans haudit

/-! ## Size-independent counter telescope -/

/-- Across any symbolic schedule, the dedicated counter is monotone and
grows by at most one per body. -/
theorem foldl_body_vsub_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hword : WordState s)
    (hroom : s.regs rVSub + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVSub ≤ out.regs rVSub ∧
      out.regs rVSub ≤ s.regs rVSub + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      let bit := bodyUnderflowBit c k s
      have hbit : bit ≤ 1 := bodyUnderflowBit_le_one c k s
      have hfirstRoom : s.regs rVSub + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vsub_increment c k s hword (by
        simpa only [bit] using hfirstRoom)
      change (arun k s c.body).regs rVSub = s.regs rVSub + bit at hfirst
      have hnextWord : WordState (arun k s c.body) :=
        arun_word k c.body s hword.1 hword.2
      have htailRoom :
          (arun k s c.body).regs rVSub + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) hnextWord htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVSub ≤ s.regs rVSub + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVSub := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVSub
              ≤ (arun k s c.body).regs rVSub + ks.length := htail.2
          _ = s.regs rVSub + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVSub + (ks.length + 1) := by omega

/-- A terminal zero counter rules out the literal underflow bit at every
earlier scheduled body.  The theorem is generic and keeps `List.range N`
symbolic. -/
theorem every_bodyUnderflowBit_zero_of_fold_zero
    (c : R2Cfg) (entry : AState) (N : Nat)
    (hword : WordState entry) (hentry : entry.regs rVSub = 0)
    (hNM : N < M)
    (hfinal :
      ((List.range N).foldl (fun st k => arun k st c.body) entry).regs
        rVSub = 0) :
    ∀ j, j < N →
      bodyUnderflowBit c j
        ((List.range j).foldl (fun st k => arun k st c.body) entry) = 0 := by
  intro j hj
  let pre := (List.range j).foldl (fun st k => arun k st c.body) entry
  let bit := bodyUnderflowBit c j pre
  let after := arun j pre c.body
  have hpreWord : WordState pre :=
    foldl_arun_word c.body (List.range j) entry hword.1 hword.2
  have hpreBounds := foldl_body_vsub_bounds c (List.range j) entry hword (by
    rw [hentry]
    simp only [List.length_range, Nat.zero_add]
    omega)
  have hpreLe : pre.regs rVSub ≤ j := by
    simpa only [pre, List.length_range, hentry, Nat.zero_add] using
      hpreBounds.2
  have hbitLe : bit ≤ 1 := bodyUnderflowBit_le_one c j pre
  have hfirstRoom : pre.regs rVSub + bit < M := by omega
  have hfirst := body_vsub_increment c j pre hpreWord (by
    simpa only [bit] using hfirstRoom)
  change after.regs rVSub = pre.regs rVSub + bit at hfirst
  have hafterLe : after.regs rVSub ≤ j + 1 := by omega
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
  have hafterWord : WordState after :=
    arun_word j c.body pre hpreWord.1 hpreWord.2
  have htailRoom : after.regs rVSub + tail.length < M := by
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vsub_bounds c tail after hafterWord htailRoom
  dsimp only at htailBounds
  have hfinal' :
      (tail.foldl (fun st k => arun k st c.body) after).regs rVSub = 0 := by
    rw [hrange, List.foldl_append] at hfinal
    simpa only [List.foldl_cons, List.foldl_nil, pre, after] using hfinal
  have hafterZero : after.regs rVSub = 0 := by omega
  change bit = 0
  omega

#print axioms logUnderflowAuditInstrs_vsub_run
#print axioms logUnderflowAuditBody_vsub_run
#print axioms body_vsub_increment
#print axioms foldl_body_vsub_bounds
#print axioms every_bodyUnderflowBit_zero_of_fold_zero

end LeanCompCert.Ports.R2SegSieve
