import LeanCompCert.Ports.RamareCombined100MLambdaPsiEndpoints

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M

/-- Select lambda endpoints, update the two quotient sums, and advance both
psi endpoints.  Shape registers `100..105`, candidate `132`, and phase gate
`11` are the stable conventions of the lower layers. -/
def candidateBody (c : Cfg) : List AInstr :=
  selectionBody c ++ sumBody ++ lowerEndpointBody ++ upperEndpointBody

/-- The four state components owned by the candidate arithmetic suffix. -/
structure CandidateProjection where
  sumL : Nat
  sumU : Nat
  psiL : PsiQR
  psiU : PsiQR
  deriving Repr, DecidableEq

def observeCandidate (s : AState) : CandidateProjection :=
  { sumL := s.regs rSumL
    sumU := s.regs rSumU
    psiL := ⟨s.regs rPsiLQ, s.regs rPsiLR⟩
    psiU := ⟨s.regs rPsiUQ, s.regs rPsiUR⟩ }

def candidateLowerLambda (c : Cfg) (s : AState) : Nat :=
  selectedLambda (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
    (s.regs lRLogL - s.regs 11 * s.regs lRIL)
    (s.arr (selectedLoIndex c (s.regs sRP)))

def candidateUpperLambda (c : Cfg) (s : AState) : Nat :=
  selectedLambda (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
    (s.regs lRLogU - s.regs 11 * s.regs lRIU)
    (s.arr (selectedHiIndex c (s.regs sRP)))

/-- Source-shaped candidate arithmetic, expressed only in terms of the entry
machine observation and the already-refined lambda lookup. -/
def candidateArithmetic (c : Cfg) (s : AState) : CandidateProjection :=
  let lamL := candidateLowerLambda c s
  let lamU := candidateUpperLambda c s
  let zL : PsiQR := ⟨s.regs rPsiLQ, s.regs rPsiLR⟩
  let zU : PsiQR := ⟨s.regs rPsiUQ, s.regs rPsiUR⟩
  { sumL := s.regs rSumL + lamL / s.regs 132
    sumU := s.regs rSumU + ceilDiv lamU (s.regs 132)
    psiL :=
      ⟨if s.regs 11 = 1 then (zL.advance (s.regs 132) lamL).q else zL.q,
       if s.regs 11 = 1 then (zL.advance (s.regs 132) lamL).r else zL.r⟩
    psiU :=
      ⟨if s.regs 11 = 1 then (zU.advance (s.regs 132) lamU).q else zU.q,
       if s.regs 11 = 1 then (zU.advance (s.regs 132) lamU).r else zU.r⟩ }

@[simp] theorem observeCandidate_sumL (s : AState) :
    (observeCandidate s).sumL = s.regs rSumL := rfl

@[simp] theorem observeCandidate_sumU (s : AState) :
    (observeCandidate s).sumU = s.regs rSumU := rfl

@[simp] theorem candidateArithmetic_sumL (c : Cfg) (s : AState) :
    (candidateArithmetic c s).sumL =
      s.regs rSumL + candidateLowerLambda c s / s.regs 132 := rfl

@[simp] theorem candidateArithmetic_sumU (c : Cfg) (s : AState) :
    (candidateArithmetic c s).sumU =
      s.regs rSumU + ceilDiv (candidateUpperLambda c s) (s.regs 132) := rfl

/-- Exact composition of the lambda selection, floor/ceiling sums, and both
word-sized quotient transitions.  The hypotheses are precisely the word,
table-initialization, no-wrap, and canonical-transition invariants needed by
the emitted straight-line candidate block. -/
theorem candidateBody_run (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hpreL : s.regs 11 * s.regs lRIL ≤ s.regs lRLogL)
    (hpreU : s.regs 11 * s.regs lRIU ≤ s.regs lRLogU)
    (hlen : c.logLen < M)
    (haddrL : s.regs sRP + c.logLoBase < M)
    (haddrU : s.regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hn0 : 0 < s.regs 132) (hn : s.regs 132 + 1 < M)
    (hsumL : s.regs rSumL +
      candidateLowerLambda c s / s.regs 132 < M)
    (hsumU : s.regs rSumU +
      ceilDiv (candidateUpperLambda c s) (s.regs 132) < M)
    (haL : s.regs rPsiLR + candidateLowerLambda c s < M)
    (haU : s.regs rPsiUR + candidateUpperLambda c s < M)
    (houtL :
      (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M)
    (houtU :
      (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M) :
    observeCandidate (arun k s (candidateBody c)) = candidateArithmetic c s ∧
      (arun k s (candidateBody c)).arr = s.arr := by
  let selected := arun k s (selectionBody c)
  let summed := arun k selected sumBody
  let lowered := arun k summed lowerEndpointBody
  let finished := arun k lowered upperEndpointBody
  have hwSelected := arun_word k (selectionBody c) s hregs harr
  have hwSummed := arun_word k sumBody selected hwSelected.1 hwSelected.2
  have hsGate : selected.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by rfl)
  have hsN : selected.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by rfl)
  have hsSumL : selected.regs rSumL = s.regs rSumL :=
    arun_reg_frame k rSumL _ s (by rfl)
  have hsSumU : selected.regs rSumU = s.regs rSumU :=
    arun_reg_frame k rSumU _ s (by rfl)
  have hsPsiLQ : selected.regs rPsiLQ = s.regs rPsiLQ :=
    arun_reg_frame k rPsiLQ _ s (by rfl)
  have hsPsiLR : selected.regs rPsiLR = s.regs rPsiLR :=
    arun_reg_frame k rPsiLR _ s (by rfl)
  have hsPsiUQ : selected.regs rPsiUQ = s.regs rPsiUQ :=
    arun_reg_frame k rPsiUQ _ s (by rfl)
  have hsPsiUR : selected.regs rPsiUR = s.regs rPsiUR :=
    arun_reg_frame k rPsiUR _ s (by rfl)
  have hselection := selectionBody_run c k s hgate
    (hregs lRIL) (hregs lRIU) (hregs lRLogL) (hregs lRLogU)
    hpreL hpreU hlen haddrL haddrU hsink
    (harr _) (harr _)
  rcases hselection with
    ⟨hOldL, hOldU, hTabL, hTabU, hsLamL, hsLamU, hsArr⟩
  have hsLamL' : selected.regs rLamL = candidateLowerLambda c s := by
    simpa [candidateLowerLambda] using hsLamL
  have hsLamU' : selected.regs rLamU = candidateUpperLambda c s := by
    simpa [candidateUpperLambda] using hsLamU
  have hsum := sumBody_run k selected
    (by simpa [hsN] using hn0)
    (by have := hn; simpa [hsN] using Nat.lt_of_succ_lt hn)
    (by simpa [hsSumL, hsLamL', hsN] using hsumL)
    (by simpa [hsSumU, hsLamU', hsN] using hsumU)
  have hmArr : summed.arr = selected.arr :=
    (sumBody_inputs k selected).2.2.2
  have hmGate : summed.regs 11 = s.regs 11 := by
    rw [arun_reg_frame k 11 sumBody selected (by decide), hsGate]
  have hmN : summed.regs 132 = s.regs 132 := by
    rw [arun_reg_frame k 132 sumBody selected (by decide), hsN]
  have hmLamL : summed.regs rLamL = candidateLowerLambda c s := by
    rw [arun_reg_frame k rLamL sumBody selected (by decide), hsLamL']
  have hmLamU : summed.regs rLamU = candidateUpperLambda c s := by
    rw [arun_reg_frame k rLamU sumBody selected (by decide), hsLamU']
  have hmPsiLQ : summed.regs rPsiLQ = s.regs rPsiLQ := by
    rw [arun_reg_frame k rPsiLQ sumBody selected (by decide), hsPsiLQ]
  have hmPsiLR : summed.regs rPsiLR = s.regs rPsiLR := by
    rw [arun_reg_frame k rPsiLR sumBody selected (by decide), hsPsiLR]
  have hmPsiUQ : summed.regs rPsiUQ = s.regs rPsiUQ := by
    rw [arun_reg_frame k rPsiUQ sumBody selected (by decide), hsPsiUQ]
  have hmPsiUR : summed.regs rPsiUR = s.regs rPsiUR := by
    rw [arun_reg_frame k rPsiUR sumBody selected (by decide), hsPsiUR]
  have hlower := lowerEndpointBody_run k summed
    (by simpa [hmGate] using hgate) (hwSummed.1 rPsiLQ)
    (hwSummed.1 rPsiLR) (hwSummed.1 rLamL)
    (by simpa [hmN] using hn)
    (by simpa [hmPsiLR, hmLamL] using haL)
    (by simpa [hmN, hmLamL, hmPsiLQ, hmPsiLR] using houtL)
  have hlGate : lowered.regs 11 = s.regs 11 := by
    rw [arun_reg_frame k 11 lowerEndpointBody summed (by decide), hmGate]
  have hlN : lowered.regs 132 = s.regs 132 := by
    rw [arun_reg_frame k 132 lowerEndpointBody summed (by decide), hmN]
  have hlLamU : lowered.regs rLamU = candidateUpperLambda c s := by
    rw [arun_reg_frame k rLamU lowerEndpointBody summed (by decide), hmLamU]
  have hlPsiUQ : lowered.regs rPsiUQ = s.regs rPsiUQ := by
    rw [arun_reg_frame k rPsiUQ lowerEndpointBody summed (by decide), hmPsiUQ]
  have hlPsiUR : lowered.regs rPsiUR = s.regs rPsiUR := by
    rw [arun_reg_frame k rPsiUR lowerEndpointBody summed (by decide), hmPsiUR]
  have hwLowered :=
    arun_word k lowerEndpointBody summed hwSummed.1 hwSummed.2
  have hupper := upperEndpointBody_run k lowered
    (by simpa [hlGate] using hgate) (hwLowered.1 rPsiUQ)
    (hwLowered.1 rPsiUR) (hwLowered.1 rLamU)
    (by simpa [hlN] using hn)
    (by simpa [hlPsiUR, hlLamU] using haU)
    (by simpa [hlN, hlLamU, hlPsiUQ, hlPsiUR] using houtU)
  have hfinishedSumL : finished.regs rSumL =
      s.regs rSumL + candidateLowerLambda c s / s.regs 132 := by
    rw [arun_reg_frame k rSumL upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumL lowerEndpointBody summed (by decide)]
    simpa [hsSumL, hsLamL', hsN] using hsum.1
  have hfinishedSumU : finished.regs rSumU =
      s.regs rSumU + ceilDiv (candidateUpperLambda c s) (s.regs 132) := by
    rw [arun_reg_frame k rSumU upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumU lowerEndpointBody summed (by decide)]
    simpa [hsSumU, hsLamU', hsN] using hsum.2
  have hfinishedPsiLQ : finished.regs rPsiLQ =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
          ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q
      else s.regs rPsiLQ) := by
    rw [arun_reg_frame k rPsiLQ upperEndpointBody lowered (by decide)]
    simpa [hmGate, hmN, hmLamL, hmPsiLQ, hmPsiLR] using hlower.1
  have hfinishedPsiLR : finished.regs rPsiLR =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
          ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r
      else s.regs rPsiLR) := by
    rw [arun_reg_frame k rPsiLR upperEndpointBody lowered (by decide)]
    simpa [hmGate, hmN, hmLamL, hmPsiLQ, hmPsiLR] using hlower.2.1
  have hfinishedPsiUQ : finished.regs rPsiUQ =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
          ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q
      else s.regs rPsiUQ) := by
    simpa [hlGate, hlN, hlLamU, hlPsiUQ, hlPsiUR] using hupper.1
  have hfinishedPsiUR : finished.regs rPsiUR =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
          ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r
      else s.regs rPsiUR) := by
    simpa [hlGate, hlN, hlLamU, hlPsiUQ, hlPsiUR] using hupper.2.1
  have hfinishedArr : finished.arr = s.arr := by
    rw [hupper.2.2, hlower.2.2, hmArr, hsArr]
  have hbody : arun k s (candidateBody c) = finished := by
    simp [candidateBody, selected, summed, lowered, finished, arun_append]
  rw [hbody]
  constructor
  · unfold observeCandidate candidateArithmetic
    rw [CandidateProjection.mk.injEq]
    refine ⟨hfinishedSumL, hfinishedSumU, ?_, ?_⟩
    · rw [PsiQR.mk.injEq]
      exact ⟨hfinishedPsiLQ, hfinishedPsiLR⟩
    · rw [PsiQR.mk.injEq]
      exact ⟨hfinishedPsiUQ, hfinishedPsiUR⟩
  · exact hfinishedArr

/-- A modular addition whose result did not fall below its first word did
not carry.  This is the arithmetic bridge used by the emitted post-run carry
checks. -/
theorem add_lt_word_of_mod_ge {a b : Nat}
    (ha : a < M) (hb : b < M) (hge : a ≤ (a + b) % M) : a + b < M := by
  by_cases hwrap : a + b < M
  · exact hwrap
  · have hMle : M ≤ a + b := Nat.le_of_not_gt hwrap
    have hsumLt : a + b < 2 * M := by omega
    have hmod : (a + b) % M = a + b - M := by
      rw [Nat.mod_eq_sub_mod hMle, Nat.mod_eq_of_lt]
      omega
    rw [hmod] at hge
    omega

/-- If the old quotient is a word and the remainder-plus-lambda addition is
exact, the rebased quotient is also a word. -/
theorem PsiQR.advance_q_lt_word (n lam : Nat) (z : PsiQR)
    (hq : z.q < M) (hadd : z.r + lam < M) : (z.advance n lam).q < M := by
  unfold PsiQR.advance
  dsimp only
  by_cases hle : z.q ≤ z.r + lam
  · rw [if_pos hle]
    change z.q + (z.r + lam - z.q) / (n + 1) < M
    have hdiv : (z.r + lam - z.q) / (n + 1) ≤
        z.r + lam - z.q := Nat.div_le_self _ _
    omega
  · rw [if_neg hle]
    split
    · change z.q - (z.q - (z.r + lam)) / (n + 1) < M
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq
    · change z.q - (z.q - (z.r + lam)) / (n + 1) - 1 < M
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq)

/-- State-shaped lower-endpoint specialization.  Keeping this wrapper beside
the scalar quotient lemma prevents callers from unfolding a large machine
state merely to infer the three scalar arguments. -/
theorem candidateLowerAdvance_q_lt_word (c : Cfg) (s : AState)
    (hq : s.regs rPsiLQ < M)
    (hadd : s.regs rPsiLR + candidateLowerLambda c s < M) :
    (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
      ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M :=
  PsiQR.advance_q_lt_word _ _ _ hq hadd

/-- Upper-endpoint counterpart of `candidateLowerAdvance_q_lt_word`. -/
theorem candidateUpperAdvance_q_lt_word (c : Cfg) (s : AState)
    (hq : s.regs rPsiUQ < M)
    (hadd : s.regs rPsiUR + candidateUpperLambda c s < M) :
    (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
      ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M :=
  PsiQR.advance_q_lt_word _ _ _ hq hadd

/-- Exact candidate arithmetic recovered from the fixed post-run carry
checks.  The four cumulative additions are first denoted modulo `M`; the
nondecrease checks then establish precisely the no-wrap premises of
`candidateBody_run`. -/
theorem candidateBody_run_of_post_checks (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hpreL : s.regs 11 * s.regs lRIL ≤ s.regs lRLogL)
    (hpreU : s.regs 11 * s.regs lRIU ≤ s.regs lRLogU)
    (hlen : c.logLen < M)
    (haddrL : s.regs sRP + c.logLoBase < M)
    (haddrU : s.regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hn0 : 0 < s.regs 132) (hn : s.regs 132 + 1 < M)
    (hsumLPost : s.regs rSumL ≤
      (arun k s (candidateBody c)).regs rSumL)
    (hsumUPost : s.regs rSumU ≤
      (arun k s (candidateBody c)).regs rSumU)
    (haLPost : s.regs rPsiLR +
      (arun k s (candidateBody c)).regs rLamL < M)
    (haUPost : s.regs rPsiUR +
      (arun k s (candidateBody c)).regs rLamU < M) :
    observeCandidate (arun k s (candidateBody c)) = candidateArithmetic c s ∧
      (arun k s (candidateBody c)).arr = s.arr := by
  let selected := arun k s (selectionBody c)
  let summed := arun k selected sumBody
  let lowered := arun k summed lowerEndpointBody
  let finished := arun k lowered upperEndpointBody
  have hwSelected := arun_word k (selectionBody c) s hregs harr
  have hsGate : selected.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by rfl)
  have hsN : selected.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by rfl)
  have hsSumL : selected.regs rSumL = s.regs rSumL :=
    arun_reg_frame k rSumL _ s (by rfl)
  have hsSumU : selected.regs rSumU = s.regs rSumU :=
    arun_reg_frame k rSumU _ s (by rfl)
  have hsPsiLR : selected.regs rPsiLR = s.regs rPsiLR :=
    arun_reg_frame k rPsiLR _ s (by rfl)
  have hsPsiUR : selected.regs rPsiUR = s.regs rPsiUR :=
    arun_reg_frame k rPsiUR _ s (by rfl)
  have hselection := selectionBody_run c k s hgate
    (hregs lRIL) (hregs lRIU) (hregs lRLogL) (hregs lRLogU)
    hpreL hpreU hlen haddrL haddrU hsink (harr _) (harr _)
  rcases hselection with
    ⟨_hOldL, _hOldU, _hTabL, _hTabU, hsLamL, hsLamU, _hsArr⟩
  have hsLamL' : selected.regs rLamL = candidateLowerLambda c s := by
    simpa [candidateLowerLambda] using hsLamL
  have hsLamU' : selected.regs rLamU = candidateUpperLambda c s := by
    simpa [candidateUpperLambda] using hsLamU
  have hsumRaw := sumBody_run_mod k selected
    (by simpa [hsN] using hn0)
    (by simpa [hsN] using Nat.lt_of_succ_lt hn)
  have hbody : arun k s (candidateBody c) = finished := by
    simp [candidateBody, selected, summed, lowered, finished, arun_append]
  have hfinishedSumL : finished.regs rSumL = summed.regs rSumL := by
    rw [arun_reg_frame k rSumL upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumL lowerEndpointBody summed (by decide)]
  have hfinishedSumU : finished.regs rSumU = summed.regs rSumU := by
    rw [arun_reg_frame k rSumU upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumU lowerEndpointBody summed (by decide)]
  have hsumLGe : s.regs rSumL ≤
      (s.regs rSumL + candidateLowerLambda c s / s.regs 132) % M := by
    rw [hbody, hfinishedSumL] at hsumLPost
    calc
      s.regs rSumL ≤ summed.regs rSumL := hsumLPost
      _ = _ := by simpa [hsSumL, hsLamL', hsN] using hsumRaw.1
  have hsumUGe : s.regs rSumU ≤
      (s.regs rSumU + ceilDiv (candidateUpperLambda c s) (s.regs 132)) % M := by
    rw [hbody, hfinishedSumU] at hsumUPost
    calc
      s.regs rSumU ≤ summed.regs rSumU := hsumUPost
      _ = _ := by simpa [hsSumU, hsLamU', hsN] using hsumRaw.2
  have hlamLWord : candidateLowerLambda c s < M := by
    rw [← hsLamL']
    exact hwSelected.1 rLamL
  have hlamUWord : candidateUpperLambda c s < M := by
    rw [← hsLamU']
    exact hwSelected.1 rLamU
  have hsumL : s.regs rSumL +
      candidateLowerLambda c s / s.regs 132 < M :=
    add_lt_word_of_mod_ge (hregs rSumL)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlamLWord) hsumLGe
  have hceilWord : ceilDiv (candidateUpperLambda c s) (s.regs 132) < M := by
    apply Nat.lt_of_le_of_lt _ hlamUWord
    apply (ceilDiv_le_iff_le_mul hn0).2
    have hone : 1 ≤ s.regs 132 := hn0
    exact Nat.le_mul_of_pos_right _ hn0
  have hsumU : s.regs rSumU +
      ceilDiv (candidateUpperLambda c s) (s.regs 132) < M :=
    add_lt_word_of_mod_ge (hregs rSumU) hceilWord hsumUGe
  have hfinishedLamL : finished.regs rLamL = selected.regs rLamL := by
    rw [arun_reg_frame k rLamL upperEndpointBody lowered (by decide),
      arun_reg_frame k rLamL lowerEndpointBody summed (by decide),
      arun_reg_frame k rLamL sumBody selected (by decide)]
  have hfinishedLamU : finished.regs rLamU = selected.regs rLamU := by
    rw [arun_reg_frame k rLamU upperEndpointBody lowered (by decide),
      arun_reg_frame k rLamU lowerEndpointBody summed (by decide),
      arun_reg_frame k rLamU sumBody selected (by decide)]
  have haL : s.regs rPsiLR + candidateLowerLambda c s < M := by
    rw [hbody, hfinishedLamL, hsLamL'] at haLPost
    exact haLPost
  have haU : s.regs rPsiUR + candidateUpperLambda c s < M := by
    rw [hbody, hfinishedLamU, hsLamU'] at haUPost
    exact haUPost
  have houtL :
      (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M :=
    PsiQR.advance_q_lt_word _ _ _ (hregs rPsiLQ) haL
  have houtU :
      (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M :=
    PsiQR.advance_q_lt_word _ _ _ (hregs rPsiUQ) haU
  exact candidateBody_run c k s hregs harr hgate hpreL hpreU hlen haddrL
    haddrU hsink hn0 hn hsumL hsumU haL haU houtL houtU

/-- The selected lambda words remain available at the end of the candidate
suffix.  This theorem has no cumulative arithmetic premises. -/
theorem candidateBody_lambdas (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hpreL : s.regs 11 * s.regs lRIL ≤ s.regs lRLogL)
    (hpreU : s.regs 11 * s.regs lRIU ≤ s.regs lRLogU)
    (hlen : c.logLen < M)
    (haddrL : s.regs sRP + c.logLoBase < M)
    (haddrU : s.regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M) :
    (arun k s (candidateBody c)).regs rLamL = candidateLowerLambda c s ∧
      (arun k s (candidateBody c)).regs rLamU = candidateUpperLambda c s := by
  let selected := arun k s (selectionBody c)
  have hselection := selectionBody_run c k s hgate
    (hregs lRIL) (hregs lRIU) (hregs lRLogL) (hregs lRLogU)
    hpreL hpreU hlen haddrL haddrU hsink (harr _) (harr _)
  rcases hselection with
    ⟨_hOldL, _hOldU, _hTabL, _hTabU, hsLamL, hsLamU, _hsArr⟩
  have hsLamL : selected.regs rLamL = candidateLowerLambda c s := by
    simpa [candidateLowerLambda] using hsLamL
  have hsLamU : selected.regs rLamU = candidateUpperLambda c s := by
    simpa [candidateUpperLambda] using hsLamU
  rw [candidateBody, arun_append, arun_append, arun_append,
    arun_reg_frame k rLamL upperEndpointBody _ (by decide),
    arun_reg_frame k rLamL lowerEndpointBody _ (by decide),
    arun_reg_frame k rLamL sumBody _ (by decide),
    arun_reg_frame k rLamU upperEndpointBody _ (by decide),
    arun_reg_frame k rLamU lowerEndpointBody _ (by decide),
    arun_reg_frame k rLamU sumBody _ (by decide), hsLamL, hsLamU]
  exact ⟨rfl, rfl⟩


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep
