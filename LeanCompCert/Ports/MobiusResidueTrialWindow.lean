import LeanCompCert.Ports.MobiusResidueTrial
import LeanCompCert.Ports.MobiusResidueWindow

/-!
# Candidate-level meaning of the trial-division residue program

`MobiusResidueTrial.fullProgram_denote` identifies the complete rolled program
with a flat joint fold, one step per trial divisor.  The arithmetic residue,
however, is specified one gated integer at a time.  This file proves the exact
reassociation between those views:

* non-final trial rounds have the identity `idleSig` effect;
* the final round has `trialSig`, formed from the completed `trialRun`;
* `fullBlock_spec` collapses one candidate's divisor rounds to one residue
  step; and
* `fullValue_eq_trialResAt` collapses the whole flat fold to one transparent
  residue step per candidate.

The final identification of `trialSig` with `muSig` belongs in the Mathlib
consumer, where `ArithmeticFunction.moebius` is available.
-/

namespace LeanCompCert.Ports.MobiusResidueTrial

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Ports.MobiusResidueRealisation

/-- A non-final divisor round: it names the candidate but updates no residue
field. -/
def idleSig (n : Nat) : Sig := ⟨n, 0, 0, 0⟩

/-- The single gated signal produced after all trial divisors for `X`. -/
def trialSig (X R : Nat) : Sig :=
  let t := trialRun X R
  ⟨X, muPlus t, muMinus t, 1⟩

/-- An idle signal is the identity on word-sized residue fields. -/
theorem resStep_idle (k n : Nat) (r : Res)
    (hlo : r.tLo < M) (hhi : r.tHi < M)
    (hc : r.cel < M) (hcs : r.celSq < M) (hv : r.viol < M) :
    resStep k (idleSig n) r = r := by
  simp [resStep, idleSig, accStep, celStep, violStep,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hcs, Nat.mod_eq_of_lt hv]

/-- Every persistent residue register is a machine word. -/
def ResWord (r : Res) : Prop :=
  r.tLo < M ∧ r.tHi < M ∧ r.cel < M ∧ r.celSq < M ∧ r.viol < M

/-- Every transparent residue step produces word-sized fields. -/
theorem resStep_word (k : Nat) (g : Sig) (r : Res) :
    ResWord (resStep k g r) := by
  unfold ResWord resStep
  dsimp only
  exact ⟨accStep_fst_lt _ _ _ _ _ _, accStep_snd_lt _ _ _ _ _ _,
    Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos⟩

/-- Decode the signal of round `r` of candidate `n`. -/
theorem roundSig_round (c : Cfg) (n r : Nat) (hr : r < c.rounds)
    (a : Abs) (hmo : a.mo < M) :
    roundSig c (n * c.rounds + r) a =
      let t := trialStep (r + 2)
        (if r = 0 then ⟨c.lo + n, 0, 0⟩ else a.t)
      let last := if r + 1 = c.rounds then 1 else 0
      ⟨c.lo + n, last * muPlus t, last * muMinus t, last⟩ := by
  rw [roundSig, gstep_round c n r hr a hmo]
  obtain ⟨hdiv, hmod⟩ := index_decode c n r hr
  rw [hdiv, hmod]
  by_cases hlast : r + 1 = c.rounds
  · have hq : r = c.rounds - 1 := by omega
    simp only [if_pos hlast, if_pos hq]
  · have hq : ¬ r = c.rounds - 1 := by omega
    simp only [if_neg hlast, if_neg hq]

/-- Every non-final divisor round exposes the idle signal. -/
theorem roundSig_idle (c : Cfg) (n r : Nat) (hr : r < c.rounds)
    (a : Abs) (hmo : a.mo < M) (hlast : r + 1 ≠ c.rounds) :
    roundSig c (n * c.rounds + r) a = idleSig (c.lo + n) := by
  rw [roundSig_round c n r hr a hmo]
  simp [hlast, idleSig]

theorem trialPrefix_succ (X r : Nat) :
    trialPrefix X (r + 1) = trialStep (r + 2) (trialPrefix X r) := by
  simp only [trialPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The final divisor round exposes the signal of the complete trial run. -/
theorem roundSig_last (c : Cfg) (n r : Nat) (hr : r < c.rounds)
    (hlast : r + 1 = c.rounds) (a : Abs) (hmo : a.mo < M)
    (hpre : (if r = 0 then ⟨c.lo + n, 0, 0⟩ else a.t) =
      trialPrefix (c.lo + n) r) :
    roundSig c (n * c.rounds + r) a = trialSig (c.lo + n) c.rounds := by
  rw [roundSig_round c n r hr a hmo]
  simp only [if_pos hlast]
  rw [hpre, ← trialPrefix_succ, hlast, trialPrefix_full]
  simp [trialSig]

/-- The base computation over the first `count` rounds of candidate `n`. -/
def basePrefix (c : Cfg) (n count : Nat) (a : Abs) : Abs :=
  (List.range count).foldl
    (fun x r => gstep c (n * c.rounds + r) x) a

/-- The joint base/residue computation over a candidate-round prefix. -/
def fullPrefix (c : Cfg) (k n count : Nat) (a : FullAbs) : FullAbs :=
  (List.range count).foldl
    (fun x r => fullGstep c k (n * c.rounds + r) x) a

theorem basePrefix_succ (c : Cfg) (n count : Nat) (a : Abs) :
    basePrefix c n (count + 1) a =
      gstep c (n * c.rounds + count) (basePrefix c n count a) := by
  simp [basePrefix, List.range_succ, List.foldl_append]

theorem fullPrefix_succ (c : Cfg) (k n count : Nat) (a : FullAbs) :
    fullPrefix c k n (count + 1) a =
      fullGstep c k (n * c.rounds + count) (fullPrefix c k n count a) := by
  simp [fullPrefix, List.range_succ, List.foldl_append]

/-- Before the last round, the accumulator is unchanged and the trial state
is exactly the corresponding prefix. -/
theorem basePrefix_before (c : Cfg) (hR : 0 < c.rounds) (n count : Nat)
    (a : Abs) (hmo : a.mo < M) (hcount : count < c.rounds) :
    (basePrefix c n count a).mo = a.mo ∧
      (if count = 0 then ⟨c.lo + n, 0, 0⟩
        else (basePrefix c n count a).t) =
          trialPrefix (c.lo + n) count := by
  cases count with
  | zero => simp [basePrefix, trialPrefix]
  | succ q =>
      have hq : q < c.rounds := by omega
      have hne : q + 1 ≠ c.rounds := by omega
      have h := block_prefix c hR n a hmo q hq
      simp only [if_neg hne] at h
      change basePrefix c n (q + 1) a =
        ⟨a.bad, a.mo, trialPrefix (c.lo + n) (q + 1)⟩ at h
      rw [h]
      simp

/-- A joint round prefix changes the residue only when it completes the
candidate. -/
theorem fullPrefix_spec (c : Cfg) (k n : Nat) (hR : 0 < c.rounds)
    (a : FullAbs) (hmo : a.base.mo < M) (hw : ResWord a.residue) :
    ∀ count, count ≤ c.rounds →
      fullPrefix c k n count a =
        ⟨basePrefix c n count a.base,
          if count = c.rounds then
            resStep k (trialSig (c.lo + n) c.rounds) a.residue
          else a.residue⟩ := by
  intro count
  induction count with
  | zero =>
      intro _
      have hR0 : 0 ≠ c.rounds := by omega
      simp [fullPrefix, basePrefix, hR0]
  | succ q ih =>
      intro hle
      have hq : q < c.rounds := by omega
      have hqne : q ≠ c.rounds := by omega
      have hprev := ih (by omega)
      rw [fullPrefix_succ, hprev]
      simp only [if_neg hqne, fullGstep]
      have hb := basePrefix_before c hR n q a.base hmo hq
      have hmoq : (basePrefix c n q a.base).mo < M := by
        rw [hb.1]
        exact hmo
      by_cases hlast : q + 1 = c.rounds
      · rw [if_pos hlast,
          roundSig_last c n q hq hlast (basePrefix c n q a.base) hmoq hb.2]
        apply FullAbs.eq_of
        · exact (basePrefix_succ c n q a.base).symm
        · rfl
      · rw [if_neg hlast,
          roundSig_idle c n q hq (basePrefix c n q a.base) hmoq hlast]
        apply FullAbs.eq_of
        · exact (basePrefix_succ c n q a.base).symm
        · exact resStep_idle k (c.lo + n) a.residue
            hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2

/-- **One candidate block.**  All divisor rounds collapse to one transparent
residue step driven by the completed trial state. -/
theorem fullBlock_spec (c : Cfg) (k n : Nat) (hR : 0 < c.rounds)
    (a : FullAbs) (hmo : a.base.mo < M) (hw : ResWord a.residue) :
    BlockedFold.block c.rounds (fun x i => fullGstep c k i x) a n =
      ⟨BlockedFold.block c.rounds (fun x i => gstep c i x) a.base n,
        resStep k (trialSig (c.lo + n) c.rounds) a.residue⟩ := by
  rw [BlockedFold.block_eq_shift, BlockedFold.block_eq_shift]
  change fullPrefix c k n c.rounds a =
    ⟨basePrefix c n c.rounds a.base,
      resStep k (trialSig (c.lo + n) c.rounds) a.residue⟩
  rw [fullPrefix_spec c k n hR a hmo hw c.rounds (Nat.le_refl _),
    if_pos rfl]

/-- Initializing the residue does not perturb the base state and writes the
five supplied word values exactly. -/
theorem fullEntry_fullObs (c : Cfg) (r : Res) (hw : ResWord r) :
    fullObs (fullEntry c r) = ⟨obs (entry c), r⟩ := by
  apply FullAbs.eq_of
  · apply Abs.eq_of
    · simp [fullObs, fullEntry, residueInit, obs, entry, srun, sdest, sval,
        denoteOperand, RegState.set, initialState]
    · simp [fullObs, fullEntry, residueInit, obs, entry, srun, sdest, sval,
        denoteOperand, RegState.set, initialState]
    · apply Trial.eq_of <;>
        simp [fullObs, fullEntry, residueInit, obs, entry, srun, sdest, sval,
          denoteOperand, RegState.set, initialState]
  · simp [fullObs, fullEntry, residueInit, MobiusResidueScalar.readRes,
      srun, sdest, sval, denoteOperand, RegState.set,
      ArraySegSieve.rTLo, ArraySegSieve.rTHi, ArraySegSieve.rCeil,
      ArraySegSieve.rCeilSq, ArraySegSieve.rMViol,
      Nat.mod_eq_of_lt hw.1, Nat.mod_eq_of_lt hw.2.1,
      Nat.mod_eq_of_lt hw.2.2.1, Nat.mod_eq_of_lt hw.2.2.2.1,
      Nat.mod_eq_of_lt hw.2.2.2.2]

/-- The residue after `count` completed trial-division candidates. -/
def trialResAt (c : Cfg) (k : Nat) (r0 : Res) : Nat → Res
  | 0 => r0
  | n + 1 => resStep k (trialSig (c.lo + n) c.rounds)
      (trialResAt c k r0 n)

theorem trialResAt_word (c : Cfg) (k : Nat) (r0 : Res) (hw : ResWord r0) :
    ∀ n, ResWord (trialResAt c k r0 n)
  | 0 => hw
  | _ + 1 => resStep_word _ _ _

def baseBlocks (c : Cfg) (count : Nat) : Abs :=
  (List.range count).foldl
    (BlockedFold.block c.rounds (fun x i => gstep c i x)) (obs (entry c))

def fullBlocks (c : Cfg) (k count : Nat) (r0 : Res) : FullAbs :=
  (List.range count).foldl
    (BlockedFold.block c.rounds (fun x i => fullGstep c k i x))
      ⟨obs (entry c), r0⟩

/-- Candidate-level joint fold: its residue component is `trialResAt`. -/
theorem fullBlocks_spec (c : Cfg) (k : Nat) (hR : 0 < c.rounds)
    (hm0 : c.m0 < M) (r0 : Res) (hw : ResWord r0) :
    ∀ count, fullBlocks c k count r0 =
      ⟨baseBlocks c count, trialResAt c k r0 count⟩ := by
  intro count
  induction count with
  | zero => rfl
  | succ n ih =>
      rw [fullBlocks, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      change BlockedFold.block c.rounds (fun x i => fullGstep c k i x)
        (fullBlocks c k n r0) n = _
      rw [ih]
      have hmo : (baseBlocks c n).mo < M := by
        have hfold := (fold_blocks c hR hm0 n).2
        change (baseBlocks c n).mo = moAt c n at hfold
        rw [hfold]
        exact moAt_lt c hm0 n
      rw [fullBlock_spec c k n hR
        ⟨baseBlocks c n, trialResAt c k r0 n⟩ hmo
        (trialResAt_word c k r0 hw n)]
      apply FullAbs.eq_of
      · simp [baseBlocks, List.range_succ, List.foldl_append]
      · rfl

/-- **Whole flat-fold meaning.**  `fullValue` is exactly the final violation
counter of one `trialSig` residue step per candidate. -/
theorem fullValue_eq_trialResAt (c : Cfg) (k : Nat) (r0 : Res)
    (hR : 0 < c.rounds) (hm0 : c.m0 < M) (hw : ResWord r0) :
    fullValue c k r0 = (trialResAt c k r0 c.len).viol := by
  unfold fullValue
  rw [fullEntry_fullObs c r0 hw,
    BlockedFold.foldl_range_mul c.len c.rounds
      (fun a index => fullGstep c k index a) ⟨obs (entry c), r0⟩]
  change (fullBlocks c k c.len r0).residue.viol = _
  rw [fullBlocks_spec c k hR hm0 r0 hw c.len]

end LeanCompCert.Ports.MobiusResidueTrial
