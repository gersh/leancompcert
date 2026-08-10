import LeanCompCert.Ports.CDEMAbelPrimitives
import LeanCompCert.Verified.SqrtEquiv

namespace LeanCompCert.Ports.CDEMAbelBisection

open LeanCompCert.Verified
open LeanCompCert.Ports

def pred (w k s : Nat) : Prop := w * w ≤ s * s * k

instance (w k s : Nat) : Decidable (pred w k s) := by
  unfold pred
  infer_instance

def exactRoot (w k : Nat) : Nat :=
  if pred w k (Nat.sqrt (w * w / k)) then
    Nat.sqrt (w * w / k)
  else Nat.sqrt (w * w / k) + 1

theorem seed_sq_mul_le (w k : Nat) :
    Nat.sqrt (w * w / k) * Nat.sqrt (w * w / k) * k ≤ w * w := by
  calc
    Nat.sqrt (w * w / k) * Nat.sqrt (w * w / k) * k
        ≤ (w * w / k) * k := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
    _ ≤ w * w := Nat.div_mul_le_self _ _

theorem exactRoot_pred (w k : Nat) (hk : 0 < k) : pred w k (exactRoot w k) := by
  unfold exactRoot
  split
  · assumption
  · rename_i hnot
    unfold pred at hnot ⊢
    let q := w * w / k
    let t := Nat.sqrt q
    have hq : q < (t + 1) * (t + 1) := by
      exact Nat.lt_succ_sqrt q
    have hdiv := Nat.div_add_mod (w * w) k
    have hmod := Nat.mod_lt (w * w) hk
    dsimp only [q, t] at hq ⊢
    have hcover : w * w ≤ (w * w / k + 1) * k := by
      exact Nat.le_of_lt (calc
        w * w = k * (w * w / k) + w * w % k := hdiv.symm
        _ < k * (w * w / k) + k := Nat.add_lt_add_left hmod _
        _ = (w * w / k + 1) * k := by
          simp [Nat.mul_add, Nat.mul_comm])
    have hmul : (w * w / k + 1) * k ≤
        (Nat.sqrt (w * w / k) + 1) *
          (Nat.sqrt (w * w / k) + 1) * k :=
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt hq)
    exact Nat.le_trans hcover hmul

theorem exactRoot_minimal (w k s : Nat) (hs : s < exactRoot w k) :
    ¬pred w k s := by
  by_cases hk0 : k = 0
  · subst k
    have hsqrt0 : Nat.sqrt 0 = 0 := by decide
    cases w <;> simp [exactRoot, pred, hsqrt0] at hs ⊢
  unfold exactRoot at hs
  split at hs
  · rename_i hseed
    have hsqrt : s < Nat.sqrt (w * w / k) := hs
    have hsq : s * s < w * w / k := by
      have hmono := Nat.mul_lt_mul_of_lt_of_lt hsqrt hsqrt
      have hsqrtSq := Nat.sqrt_le (w * w / k)
      omega
    unfold pred
    have hmul := Nat.mul_lt_mul_of_pos_right hsq (Nat.pos_of_ne_zero hk0)
    have hqmul : (w * w / k) * k ≤ w * w := Nat.div_mul_le_self _ _
    exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le hmul hqmul)
  · rename_i hseed
    have hsle : s ≤ Nat.sqrt (w * w / k) := by omega
    have hsq : s * s ≤ Nat.sqrt (w * w / k) * Nat.sqrt (w * w / k) :=
      Nat.mul_le_mul hsle hsle
    intro hp
    unfold pred at hp hseed
    have hsk : s * s * k ≤
        Nat.sqrt (w * w / k) * Nat.sqrt (w * w / k) * k :=
      Nat.mul_le_mul_right k hsq
    exact hseed (Nat.le_trans hp hsk)

theorem pred_iff_exactRoot_le (w k s : Nat) (hk : 0 < k) :
    pred w k s ↔ exactRoot w k ≤ s := by
  constructor
  · intro hp
    apply Nat.le_of_not_gt
    intro hs
    exact exactRoot_minimal w k s hs hp
  · intro hs
    have hp := exactRoot_pred w k hk
    unfold pred at hp ⊢
    exact Nat.le_trans hp (Nat.mul_le_mul_right k (Nat.mul_le_mul hs hs))

structure Bracket where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def Bracket.width (p : Bracket) : Nat := p.hi - p.lo

def midpoint (p : Bracket) : Nat := p.lo + p.width / 2

def step (w k : Nat) (p : Bracket) : Bracket :=
  let m := midpoint p
  if pred w k m then ⟨p.lo, m⟩ else ⟨m + 1, p.hi⟩

def iter (w k : Nat) : Nat → Bracket → Bracket
  | 0, p => p
  | n + 1, p => iter w k n (step w k p)

def Bracket.Contains (p : Bracket) (target : Nat) : Prop :=
  p.lo ≤ target ∧ target ≤ p.hi

theorem step_contains (w k : Nat) (hk : 0 < k) (p : Bracket)
    (h : p.Contains (exactRoot w k)) :
    (step w k p).Contains (exactRoot w k) := by
  unfold Bracket.Contains at h ⊢
  simp only [step, midpoint, Bracket.width]
  split
  · rename_i hp
    have hm := (pred_iff_exactRoot_le w k _ hk).mp hp
    change p.lo ≤ exactRoot w k ∧
      exactRoot w k ≤ p.lo + (p.hi - p.lo) / 2
    exact ⟨h.1, hm⟩
  · rename_i hp
    have hm := mt (pred_iff_exactRoot_le w k _ hk).mpr hp
    change p.lo + (p.hi - p.lo) / 2 + 1 ≤ exactRoot w k ∧
      exactRoot w k ≤ p.hi
    exact ⟨by omega, h.2⟩

theorem step_width (w k : Nat) (p : Bracket) :
    (step w k p).width ≤ p.width / 2 := by
  simp only [step, midpoint, Bracket.width]
  split
  · change p.lo + (p.hi - p.lo) / 2 - p.lo ≤ (p.hi - p.lo) / 2
    simp
  · change p.hi - (p.lo + (p.hi - p.lo) / 2 + 1) ≤
      (p.hi - p.lo) / 2
    omega

theorem iter_contains (w k : Nat) (hk : 0 < k) (n : Nat) (p : Bracket)
    (h : p.Contains (exactRoot w k)) :
    (iter w k n p).Contains (exactRoot w k) := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih =>
      exact ih (step w k p) (step_contains w k hk p h)

theorem iter_width (w k n : Nat) (p : Bracket) :
    (iter w k n p).width ≤ p.width / 2 ^ n := by
  induction n generalizing p with
  | zero => simp [iter]
  | succ n ih =>
      calc
        (iter w k (n + 1) p).width = (iter w k n (step w k p)).width := rfl
        _ ≤ (step w k p).width / 2 ^ n := ih (step w k p)
        _ ≤ (p.width / 2) / 2 ^ n := Nat.div_le_div_right (step_width w k p)
        _ = p.width / (2 * 2 ^ n) := Nat.div_div_eq_div_mul ..
        _ = p.width / 2 ^ (n + 1) := by
          have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [show n + 1 = n.succ by omega, Nat.pow_succ]
            omega
          rw [hp]

theorem iter_eq_target_of_width_lt_pow (w k n : Nat) (p : Bracket)
    (hk : 0 < k) (hc : p.Contains (exactRoot w k))
    (hw : p.width < 2 ^ n) :
    iter w k n p = ⟨exactRoot w k, exactRoot w k⟩ := by
  have hwidth := iter_width w k n p
  have hz : (iter w k n p).width = 0 := by
    have hdiv : p.width / 2 ^ n = 0 := Nat.div_eq_of_lt hw
    omega
  have hcontains := iter_contains w k hk n p hc
  generalize hout : iter w k n p = out at hz hcontains ⊢
  rcases out with ⟨lo, hi⟩
  simp only [Bracket.width] at hz
  simp only [Bracket.Contains] at hcontains
  have hlo : lo = exactRoot w k := by omega
  have hhi : hi = exactRoot w k := by omega
  subst lo
  subst hi
  rfl

theorem budget_covers_width (w : Nat) :
    w < 2 ^ CDEMAbelScan.bsBudget w := by
  have hn : w + 1 ≠ 0 := by omega
  have hlog : w + 1 < 2 ^ (Nat.log2 (w + 1) + 1) :=
    (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  have hp : 2 ^ (Nat.log2 (w + 1) + 1) ≤
      2 ^ (Nat.log2 (w + 1) + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  unfold CDEMAbelScan.bsBudget
  omega

theorem iter_budget_eq_target (w k : Nat) (p : Bracket)
    (hk : 0 < k) (hc : p.Contains (exactRoot w k))
    (hw : p.width ≤ w) :
    iter w k (CDEMAbelScan.bsBudget w) p =
      ⟨exactRoot w k, exactRoot w k⟩ := by
  apply iter_eq_target_of_width_lt_pow w k _ p hk hc
  exact Nat.lt_of_le_of_lt hw (budget_covers_width w)

def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

theorem le_ceilDiv_mul (n d : Nat) (hd : 0 < d) :
    n ≤ ceilDiv n d * d := by
  unfold ceilDiv
  have hdiv := Nat.div_add_mod (n + d - 1) d
  have hmod := Nat.mod_lt (n + d - 1) hd
  have hcomm : d * ((n + d - 1) / d) = ((n + d - 1) / d) * d :=
    Nat.mul_comm ..
  omega

theorem pred_ceilDiv (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    (ceilDiv n d - 1) * d < n := by
  unfold ceilDiv
  have hdiv := Nat.div_add_mod (n + d - 1) d
  have hmod := Nat.mod_lt (n + d - 1) hd
  let q := (n + d - 1) / d
  have hprod : q * d ≤ n + d - 1 := by
    dsimp only [q]
    have hcomm : d * ((n + d - 1) / d) = ((n + d - 1) / d) * d :=
      Nat.mul_comm ..
    omega
  by_cases hq : q = 0
  · simp [q, hq, hn]
  · have hqsplit : q = (q - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.pos_of_ne_zero hq)).symm
    rw [hqsplit, Nat.add_mul] at hprod
    dsimp only [q] at hprod ⊢
    omega

theorem ceilDiv_le_self (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    ceilDiv n d ≤ n := by
  unfold ceilDiv
  apply Nat.div_le_of_le_mul
  have hmul : d - 1 ≤ n * (d - 1) := by
    have h := Nat.mul_le_mul_right (d - 1) (show 1 ≤ n by omega)
    simpa using h
  have hid : n + n * (d - 1) = d * n := by
    calc
      n + n * (d - 1) = n * (1 + (d - 1)) := by
        simp [Nat.mul_add]
      _ = n * d := by rw [Nat.add_sub_of_le (by omega : 1 ≤ d)]
      _ = d * n := Nat.mul_comm ..
  omega

def initial (w k : Nat) : Bracket :=
  let t := Nat.sqrt k
  ⟨ceilDiv w (t + 1), ceilDiv w t⟩

theorem initial_contains (w k : Nat) (hw : 0 < w) (hk : 0 < k) :
    (initial w k).Contains (exactRoot w k) := by
  let t := Nat.sqrt k
  have htSq : t * t ≤ k := by
    dsimp only [t]
    exact Nat.sqrt_le k
  have hklt : k < (t + 1) * (t + 1) := by
    dsimp only [t]
    exact Nat.lt_succ_sqrt k
  have htpos : 0 < t := by
    by_cases ht0 : t = 0
    · rw [ht0] at hklt
      simp at hklt
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hhiCeil : w ≤ ceilDiv w t * t := le_ceilDiv_mul w t htpos
  have hhiPred : pred w k (ceilDiv w t) := by
    unfold pred
    have hsq := Nat.mul_le_mul hhiCeil hhiCeil
    have htK : ceilDiv w t * ceilDiv w t * (t * t) ≤
        ceilDiv w t * ceilDiv w t * k :=
      Nat.mul_le_mul_left (ceilDiv w t * ceilDiv w t) htSq
    calc
      w * w ≤ (ceilDiv w t * t) * (ceilDiv w t * t) := hsq
      _ = ceilDiv w t * ceilDiv w t * (t * t) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ ceilDiv w t * ceilDiv w t * k := htK
  have hloCeil := pred_ceilDiv w (t + 1) hw (by omega)
  have hloNot : ¬pred w k (ceilDiv w (t + 1) - 1) := by
    unfold pred
    have hkLe : k ≤ (t + 1) * (t + 1) := Nat.le_of_lt hklt
    have hmul :
        (ceilDiv w (t + 1) - 1) * (ceilDiv w (t + 1) - 1) * k ≤
          (ceilDiv w (t + 1) - 1) * (ceilDiv w (t + 1) - 1) *
            ((t + 1) * (t + 1)) :=
      Nat.mul_le_mul_left _ hkLe
    have hsq := Nat.mul_lt_mul_of_lt_of_lt hloCeil hloCeil
    have hid :
        ((ceilDiv w (t + 1) - 1) * (t + 1)) *
            ((ceilDiv w (t + 1) - 1) * (t + 1)) =
          (ceilDiv w (t + 1) - 1) * (ceilDiv w (t + 1) - 1) *
            ((t + 1) * (t + 1)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hid] at hsq
    exact Nat.not_le_of_gt (Nat.lt_of_le_of_lt hmul hsq)
  have hlo : ceilDiv w (t + 1) ≤ exactRoot w k := by
    have hnot := mt (pred_iff_exactRoot_le w k _ hk).mpr hloNot
    omega
  have hhi : exactRoot w k ≤ ceilDiv w t :=
    (pred_iff_exactRoot_le w k _ hk).mp hhiPred
  change ceilDiv w (Nat.sqrt k + 1) ≤ exactRoot w k ∧
    exactRoot w k ≤ ceilDiv w (Nat.sqrt k)
  simpa [t] using And.intro hlo hhi

theorem initial_width_le (w k : Nat) (hw : 0 < w) (hk : 0 < k) :
    (initial w k).width ≤ w := by
  let t := Nat.sqrt k
  have htpos : 0 < t := by
    have h : k < (t + 1) * (t + 1) := by
      simpa [t, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt k
    by_cases ht0 : t = 0
    · rw [ht0] at h
      simp at h
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hhi := ceilDiv_le_self w t hw htpos
  change ceilDiv w (Nat.sqrt k) - ceilDiv w (Nat.sqrt k + 1) ≤ w
  exact Nat.le_trans (Nat.sub_le _ _) (by simpa [t] using hhi)

theorem initial_budget_exact (w k : Nat) (hw : 0 < w) (hk : 0 < k) :
    iter w k (CDEMAbelScan.bsBudget w) (initial w k) =
      ⟨exactRoot w k, exactRoot w k⟩ :=
  iter_budget_eq_target w k (initial w k) hk
    (initial_contains w k hw hk) (initial_width_le w k hw hk)

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives

/-! ## Refinement of one literal machine bisection round -/

def probeS : List Instr :=
  [ .binop 193 .sub (.reg CDEMAbelScan.rSh) (.reg CDEMAbelScan.rSl)
  , .binop 193 .lshr (.reg 193) (.lit 1)
  , .binop 193 .add (.reg CDEMAbelScan.rSl) (.reg 193)
  , .binop 194 .mul (.reg 142) (.reg 193)
  , .binop 195 .sub (.lit 1) (.reg 142)
  , .binop 196 .mul (.reg 195) (.reg CDEMAbelScan.rSh)
  , .binop 194 .add (.reg 194) (.reg 196) ]

theorem probe_run (idx : Nat) (r : RegState) (lo hi : Nat)
    (hlo : r CDEMAbelScan.rSl = lo) (hhi : r CDEMAbelScan.rSh = hi)
    (hgate : r 142 = 1) (hlohi : lo ≤ hi) (hhiM : hi < M) :
    let out := srun idx r probeS
    out 193 = midpoint ⟨lo, hi⟩ ∧ out 194 = midpoint ⟨lo, hi⟩ ∧
      out CDEMAbelScan.rSl = lo ∧ out CDEMAbelScan.rSh = hi := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hdiffM : hi - lo < M := by omega
  have hsub := msub_exact hi lo hlohi hhiM
  have hshift : (((hi - lo) >>> 1) % M) = (hi - lo) / 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hdiffM)
  have hmidM : lo + (hi - lo) / 2 < M := by omega
  have hcoeff : 1 + (M - 1) = M := by decide
  have hlo18 : r 18 = lo := by simpa [CDEMAbelScan.rSl] using hlo
  have hhi19 : r 19 = hi := by simpa [CDEMAbelScan.rSh] using hhi
  simp only [probeS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, reduceIte, Nat.reduceEqDiff, CDEMAbelScan.rSl,
    CDEMAbelScan.rSh, hlo18, hhi19, hgate, h1M, hsub, hshift,
    Nat.mod_eq_of_lt hmidM]
  simp [midpoint, Bracket.width, hcoeff, Nat.mod_eq_of_lt hmidM]

theorem probe_frame (idx : Nat) (r : RegState) (j : Nat)
    (h193 : j ≠ 193) (h194 : j ≠ 194) (h195 : j ≠ 195)
    (h196 : j ≠ 196) :
    srun idx r probeS j = r j := by
  apply srun_untouched
  intro i hi
  simp only [probeS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem productionOkS_frame (c : CDEMAbelScan.Cfg) (idx : Nat)
    (r : RegState) (j : Nat)
    (hj : (j < 100 ∨ 129 < j) ∧
      j ≠ 197 ∧ j ≠ CDEMAbelScan.rViol ∧ j ≠ CDEMAbelScan.rVDiv) :
    srun idx r (okS c 194 142 197) j = r j := by
  apply srun_untouched
  intro i hi
  simp [okS, CDEMAbelScan.okBody, CDEMAbelScan.mulWideBody,
    Section413G1Denote.scalarOf] at hi
  have hrViol : CDEMAbelScan.rViol = 22 := rfl
  have hrVDiv : CDEMAbelScan.rVDiv = 245 := rfl
  rcases hj with ⟨hj | hj, hj197, hjViol, hjVDiv⟩ <;>
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp only [sdest, CDEMAbelScan.rViol, CDEMAbelScan.rVDiv] <;>
    omega

def updatePreS : List Instr :=
  [ .binop 197 .mul (.reg 197) (.reg 142)
  , .binop 198 .add (.reg 193) (.lit 1) ]

def updateS : List Instr := updatePreS ++
  Section413G1Denote.muxS 199 197 193 CDEMAbelScan.rSh 200 ++
  Section413G1Denote.muxS 201 197 CDEMAbelScan.rSl 198 200 ++
  Section413G1Denote.muxS CDEMAbelScan.rSh 142 199 CDEMAbelScan.rSh 200 ++
  Section413G1Denote.muxS CDEMAbelScan.rSl 142 201 CDEMAbelScan.rSl 200

theorem updatePre_run (idx : Nat) (r : RegState) (flag mid : Nat)
    (h197 : r 197 = flag) (h142 : r 142 = 1) (h193 : r 193 = mid)
    (hflag : flag ≤ 1) (hmidM : mid + 1 < M) :
    let out := srun idx r updatePreS
    out 197 = flag ∧ out 198 = mid + 1 ∧
      ∀ j, j ≠ 197 → j ≠ 198 → out j = r j := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hflagM : flag < M := by omega
  simp [updatePreS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    h197, h142, h193, h1M, Nat.mod_eq_of_lt hflagM,
    Nat.mod_eq_of_lt hmidM]
  intro j hj197 hj198
  simp [hj197, hj198]

theorem update_run (idx : Nat) (r : RegState) (w k lo hi : Nat)
    (hlo : r CDEMAbelScan.rSl = lo) (hhi : r CDEMAbelScan.rSh = hi)
    (hmid : r 193 = midpoint ⟨lo, hi⟩)
    (hpred : r 197 = if pred w k (midpoint ⟨lo, hi⟩) then 1 else 0)
    (hgate : r 142 = 1) (hword : ∀ j, r j < M)
    (hmidSuccM : midpoint ⟨lo, hi⟩ + 1 < M) :
    let out := srun idx r updateS
    out CDEMAbelScan.rSl = (step w k ⟨lo, hi⟩).lo ∧
      out CDEMAbelScan.rSh = (step w k ⟨lo, hi⟩).hi := by
  classical
  let mid := midpoint (⟨lo, hi⟩ : Bracket)
  let flag := if pred w k mid then 1 else 0
  let r0 := srun idx r updatePreS
  let r1 := srun idx r0 (Section413G1Denote.muxS 199 197 193 rSh 200)
  let r2 := srun idx r1 (Section413G1Denote.muxS 201 197 rSl 198 200)
  let r3 := srun idx r2 (Section413G1Denote.muxS rSh 142 199 rSh 200)
  let r4 := srun idx r3 (Section413G1Denote.muxS rSl 142 201 rSl 200)
  have hflag : flag ≤ 1 := by
    by_cases hp : pred w k mid <;> simp [flag, hp]
  have hpre := updatePre_run idx r flag mid
    (by simpa [flag, mid] using hpred) hgate (by simpa [mid] using hmid)
    hflag (by simpa [mid] using hmidSuccM)
  dsimp only at hpre
  have h0frame (j : Nat) (h197j : j ≠ 197) (h198j : j ≠ 198) :
      r0 j = r j := by simpa [r0] using hpre.2.2 j h197j h198j
  have h0_197 : r0 197 = flag := by simpa [r0] using hpre.1
  have h0_198 : r0 198 = mid + 1 := by simpa [r0] using hpre.2.1
  have h0word : ∀ j, r0 j < M := srun_lt_of_lt idx _ r hword
  have h1word : ∀ j, r1 j < M := srun_lt_of_lt idx _ r0 h0word
  have h2word : ∀ j, r2 j < M := srun_lt_of_lt idx _ r1 h1word
  have h3word : ∀ j, r3 j < M := srun_lt_of_lt idx _ r2 h2word
  have h1frame (j : Nat) (h199j : j ≠ 199) (h200j : j ≠ 200) :
      r1 j = r0 j := by
    simpa [r1] using Section413G1Denote.muxS_frame idx r0
      199 197 193 rSh 200 j h199j h200j
  have h2frame (j : Nat) (h201j : j ≠ 201) (h200j : j ≠ 200) :
      r2 j = r1 j := by
    simpa [r2] using Section413G1Denote.muxS_frame idx r1
      201 197 rSl 198 200 j h201j h200j
  have h3frame (j : Nat) (hhij : j ≠ rSh) (h200j : j ≠ 200) :
      r3 j = r2 j := by
    simpa [r3] using Section413G1Denote.muxS_frame idx r2
      rSh 142 199 rSh 200 j hhij h200j
  have h4frame (j : Nat) (hloj : j ≠ rSl) (h200j : j ≠ 200) :
      r4 j = r3 j := by
    simpa [r4] using Section413G1Denote.muxS_frame idx r3
      rSl 142 201 rSl 200 j hloj h200j
  have h1out : r1 199 = if flag = 1 then mid else hi := by
    have h := Section413G1Denote.muxS_spec idx r0 199 197 193 rSh 200
      (by decide) (by decide) (by decide) (by simp [rSh])
      (by rw [h0_197]; exact hflag) h0word
    simpa [r1, h0_197, h0frame 193 (by decide) (by decide),
      h0frame rSh (by simp [rSh]) (by simp [rSh]), hmid, hhi, mid] using h
  have h2out : r2 201 = if flag = 1 then lo else mid + 1 := by
    have h := Section413G1Denote.muxS_spec idx r1 201 197 rSl 198 200
      (by decide) (by decide) (by simp [rSl]) (by decide)
      (by rw [h1frame 197 (by decide) (by decide), h0_197]; exact hflag)
      h1word
    simpa [r2, h1frame 197 (by decide) (by decide), h0_197,
      h1frame rSl (by simp [rSl]) (by simp [rSl]),
      h0frame rSl (by simp [rSl]) (by simp [rSl]), hlo,
      h1frame 198 (by decide) (by decide), h0_198, mid] using h
  have h2_199 : r2 199 = if flag = 1 then mid else hi := by
    rw [h2frame 199 (by decide) (by decide), h1out]
  have h2gate : r2 142 = 1 := by
    rw [h2frame 142 (by decide) (by decide),
      h1frame 142 (by decide) (by decide), h0frame 142 (by decide) (by decide),
      hgate]
  have h3hi : r3 rSh = if flag = 1 then mid else hi := by
    have h := Section413G1Denote.muxS_spec idx r2 rSh 142 199 rSh 200
      (by simp [rSh]) (by decide) (by decide) (by simp [rSh])
      (by rw [h2gate]; omega) h2word
    simpa [r3, h2gate, h2_199] using h
  have h3_201 : r3 201 = if flag = 1 then lo else mid + 1 := by
    rw [h3frame 201 (by simp [rSh]) (by decide), h2out]
  have h3gate : r3 142 = 1 := by
    rw [h3frame 142 (by simp [rSh]) (by decide), h2gate]
  have h4lo : r4 rSl = if flag = 1 then lo else mid + 1 := by
    have h := Section413G1Denote.muxS_spec idx r3 rSl 142 201 rSl 200
      (by simp [rSl]) (by decide) (by decide) (by simp [rSl])
      (by rw [h3gate]; omega) h3word
    simpa [r4, h3gate, h3_201] using h
  have h4hi : r4 rSh = if flag = 1 then mid else hi := by
    rw [h4frame rSh (by simp [rSl, rSh]) (by simp [rSh]), h3hi]
  rw [updateS, srun_append, srun_append, srun_append, srun_append]
  change r4 rSl = _ ∧ r4 rSh = _
  rw [h4lo, h4hi]
  by_cases hp : pred w k mid <;> simp [step, flag, mid, hp]

def roundS (c : CDEMAbelScan.Cfg) : List Instr :=
  probeS ++ okS c 194 142 197 ++ updateS

theorem round_run (c : CDEMAbelScan.Cfg) (idx : Nat) (r : RegState)
    (lo hi k : Nat)
    (hword : ∀ j, r j < M)
    (hlo : r rSl = lo) (hhi : r rSh = hi) (hk : r rK = k)
    (hgate : r 142 = 1) (hlohi : lo ≤ hi) (hhiM : hi < M)
    (hmidpos : 0 < midpoint ⟨lo, hi⟩)
    (hW : c.wScale < M) (hkM : k < M)
    (haSqM : (c.wScale / midpoint ⟨lo, hi⟩) *
      (c.wScale / midpoint ⟨lo, hi⟩) < M)
    (h2aM : 2 * (c.wScale / midpoint ⟨lo, hi⟩) + 1 < M)
    (hseM : midpoint ⟨lo, hi⟩ *
      (k - (c.wScale / midpoint ⟨lo, hi⟩) *
        (c.wScale / midpoint ⟨lo, hi⟩)) < M)
    (habM : (c.wScale / midpoint ⟨lo, hi⟩) *
      (c.wScale % midpoint ⟨lo, hi⟩) < M)
    (h2abM : 2 * (c.wScale / midpoint ⟨lo, hi⟩) *
      (c.wScale % midpoint ⟨lo, hi⟩) < M)
    (hmidSuccM : midpoint ⟨lo, hi⟩ + 1 < M) :
    let out := srun idx r (roundS c)
    out rSl = (step c.wScale k ⟨lo, hi⟩).lo ∧
      out rSh = (step c.wScale k ⟨lo, hi⟩).hi := by
  let p := srun idx r probeS
  let q := srun idx p (okS c 194 142 197)
  have hp := probe_run idx r lo hi hlo hhi hgate hlohi hhiM
  dsimp only at hp
  have hpword : ∀ j, p j < M := srun_lt_of_lt idx _ r hword
  have hp194 : p 194 = midpoint ⟨lo, hi⟩ := by simpa [p] using hp.2.1
  have hpk : p rK = k := by
    have h := probe_frame idx r rK (by simp [rK]) (by simp [rK])
      (by simp [rK]) (by simp [rK])
    simpa [p, hk] using h
  have hpred := productionOkS_run_sq c idx p (midpoint ⟨lo, hi⟩) k
    hpword hp194 hpk hmidpos hW hkM haSqM h2aM hseM habM h2abM
  have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ p hpword
  have hqframe (j : Nat)
      (hj : (j < 100 ∨ 129 < j) ∧ j ≠ 197 ∧ j ≠ rViol ∧ j ≠ rVDiv) :
      q j = p j := by simpa [q] using productionOkS_frame c idx p j hj
  have hqlo : q rSl = lo := by
    rw [hqframe rSl (by simp [rSl, rViol, rVDiv]), show p rSl = lo from hp.2.2.1]
  have hqhi : q rSh = hi := by
    rw [hqframe rSh (by simp [rSh, rViol, rVDiv]), show p rSh = hi from hp.2.2.2]
  have hqmid : q 193 = midpoint ⟨lo, hi⟩ := by
    rw [hqframe 193 (by simp [rViol, rVDiv]), show p 193 = _ from hp.1]
  have hqgate : q 142 = 1 := by
    rw [hqframe 142 (by simp [rViol, rVDiv])]
    have h := probe_frame idx r 142 (by decide) (by decide) (by decide) (by decide)
    simpa [p, hgate] using h
  have hqpred : q 197 =
      if pred c.wScale k (midpoint ⟨lo, hi⟩) then 1 else 0 := by
    rw [show q 197 = _ from hpred]
    rfl
  have hu := update_run idx q c.wScale k lo hi hqlo hqhi hqmid hqpred
    hqgate hqword hmidSuccM
  dsimp only at hu
  rw [roundS, srun_append, srun_append]
  exact hu


/-! ## Iterated machine rounds -/

theorem update_frame (idx : Nat) (r : RegState) (j : Nat)
    (hj : j ≠ 197 ∧ j ≠ 198 ∧ j ≠ 199 ∧ j ≠ 200 ∧ j ≠ 201 ∧
      j ≠ rSh ∧ j ≠ rSl) :
    srun idx r updateS j = r j := by
  apply srun_untouched
  intro i hi
  simp [updateS, updatePreS, Section413G1Denote.muxS] at hi
  rcases hj with ⟨h197, h198, h199, h200, h201, hSh, hSl⟩
  rcases hi with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem round_preserves_k (c : Cfg) (idx : Nat) (r : RegState) :
    srun idx r (roundS c) rK = r rK := by
  rw [roundS, srun_append, srun_append,
    update_frame idx (srun idx (srun idx r probeS) (okS c 194 142 197)) rK
      (by simp [rK, rSh, rSl]),
    productionOkS_frame c idx (srun idx r probeS) rK
      (by simp [rK, rViol, rVDiv]),
    probe_frame idx r rK (by simp [rK]) (by simp [rK])
      (by simp [rK]) (by simp [rK])]

theorem round_preserves_gate (c : Cfg) (idx : Nat) (r : RegState) :
    srun idx r (roundS c) 142 = r 142 := by
  rw [roundS, srun_append, srun_append,
    update_frame idx (srun idx (srun idx r probeS) (okS c 194 142 197)) 142
      (by simp [rSh, rSl]),
    productionOkS_frame c idx (srun idx r probeS) 142
      (by simp [rViol, rVDiv]),
    probe_frame idx r 142 (by decide) (by decide) (by decide) (by decide)]

structure RoundFit (c : Cfg) (k : Nat) (p : Bracket) : Prop where
  midpoint_pos : 0 < midpoint p
  wScale_word : c.wScale < M
  k_word : k < M
  a_sq_word : (c.wScale / midpoint p) * (c.wScale / midpoint p) < M
  two_a_word : 2 * (c.wScale / midpoint p) + 1 < M
  residual_word : midpoint p *
    (k - (c.wScale / midpoint p) * (c.wScale / midpoint p)) < M
  ab_word : (c.wScale / midpoint p) * (c.wScale % midpoint p) < M
  two_ab_word : 2 * (c.wScale / midpoint p) *
    (c.wScale % midpoint p) < M
  midpoint_succ_word : midpoint p + 1 < M

def roundsS (c : Cfg) : Nat → List Instr
  | 0 => []
  | n + 1 => roundS c ++ roundsS c n

theorem rounds_run (c : Cfg) (idx : Nat) (n : Nat) (r : RegState)
    (k : Nat) (p : Bracket)
    (hword : ∀ j, r j < M)
    (hlo : r rSl = p.lo) (hhi : r rSh = p.hi) (hk : r rK = k)
    (hgate : r 142 = 1) (hlohi : p.lo ≤ p.hi) (hhiM : p.hi < M)
    (hkpos : 0 < k) (hcontains : p.Contains (exactRoot c.wScale k))
    (hfit : ∀ i, i < n → RoundFit c k (iter c.wScale k i p)) :
    let out := srun idx r (roundsS c n)
    out rSl = (iter c.wScale k n p).lo ∧
      out rSh = (iter c.wScale k n p).hi := by
  induction n generalizing r p with
  | zero =>
      change r rSl = p.lo ∧ r rSh = p.hi
      exact ⟨hlo, hhi⟩
  | succ n ih =>
      let q := srun idx r (roundS c)
      have hf : RoundFit c k p := by
        simpa [iter] using hfit 0 (by omega)
      have hr := round_run c idx r p.lo p.hi k hword hlo hhi hk hgate
        hlohi hhiM hf.midpoint_pos hf.wScale_word hf.k_word hf.a_sq_word
        hf.two_a_word hf.residual_word hf.ab_word hf.two_ab_word
        hf.midpoint_succ_word
      dsimp only at hr
      have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ r hword
      have hqk : q rK = k := by
        simpa [q] using (round_preserves_k c idx r).trans hk
      have hqgate : q 142 = 1 := by
        simpa [q] using (round_preserves_gate c idx r).trans hgate
      have hmidle : midpoint p ≤ p.hi := by
        simp only [midpoint, Bracket.width]
        omega
      have hnextcontains := step_contains c.wScale k hkpos p hcontains
      have hnextle : (step c.wScale k p).lo ≤ (step c.wScale k p).hi := by
        unfold Bracket.Contains at hnextcontains
        omega
      have hnexthi : (step c.wScale k p).hi < M := by
        simp only [step]
        split <;> simp only <;> omega
      have hnextfit : ∀ i, i < n →
          RoundFit c k (iter c.wScale k i (step c.wScale k p)) := by
        intro i hi
        simpa [iter] using hfit (i + 1) (by omega)
      have hout := ih q (step c.wScale k p) hqword hr.1 hr.2 hqk hqgate
        hnextle hnexthi hnextcontains hnextfit
      rw [roundsS, srun_append]
      change srun idx q (roundsS c n) rSl = _ ∧
        srun idx q (roundsS c n) rSh = _
      simpa [iter] using hout


end LeanCompCert.Ports.CDEMAbelBisection
