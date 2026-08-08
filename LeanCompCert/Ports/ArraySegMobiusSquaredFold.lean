import LeanCompCert.Ports.MobiusSquaredResidueWindow
import LeanCompCert.Ports.ArraySegMobiusResidueFrame
import LeanCompCert.Ports.MobiusResidueTrialWindow

/-!
# Folding the production squared residue trace

This module attaches the transparent squared model to the actual
changing-index `coreBody ++ mobiusLiveSquaredResidue` execution.  It also
proves that the expanded scratch range remains disjoint from the verified
sieve-facing projection.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredFold

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusSquaredResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

private theorem squaredResidue_avoids_core (k j : Nat)
    (hj : CoreReg j = true) :
    (mobiusLiveSquaredResidue k).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 191)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 104 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj104
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj104⟩)
  have h150 : j < 150 ∨ 191 < j := by
    by_cases h : j < 150
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj191
      exact hw (Or.inr ⟨Nat.le_of_not_gt h, hj191⟩)
  simp [mobiusLiveSquaredResidue, mobiusSquaredTestBody,
    mobiusSquaredWideBody, mobiusLiveResidue, avoidsReg,
    rTLo, rTHi, rCeil, rCeilSq, rMViol]
  rcases h100 with h100 | h100 <;>
    rcases h150 with h150 | h150 <;> omega

/-- The expanded squared residue still frames the entire sieve projection. -/
theorem arun_squaredResidue_core_frame (k idx : Nat) (s : AState) :
    CoreAgree (arun idx s (mobiusLiveSquaredResidue k)) s := by
  constructor
  · exact arun_arr_frame idx (mobiusLiveSquaredResidue k) s (by rfl)
  · intro j hj
    exact arun_reg_frame idx j (mobiusLiveSquaredResidue k) s
      (squaredResidue_avoids_core k j hj)

/-- One squared combined event has the standalone core event as its exact
sieve-facing projection. -/
theorem arun_squaredCombined_core (c : Cfg) (k idx : Nat) {s t : AState}
    (h : CoreAgree s t) :
    CoreAgree (arun idx s (c.coreBody ++ mobiusLiveSquaredResidue k))
      (arun idx t c.coreBody) := by
  rw [arun_append]
  exact (arun_squaredResidue_core_frame k idx (arun idx s c.coreBody)).trans
    (arun_coreBody_congr c idx h)

/-- Actual changing-index execution of the squared combined body. -/
def squaredCombinedIndexedRun (idx : Nat) (c : Cfg) (k : Nat) :
    Nat → AState → AState
  | 0, s => s
  | fuel + 1, s =>
      arun (idx + fuel) (squaredCombinedIndexedRun idx c k fuel s)
        (c.coreBody ++ mobiusLiveSquaredResidue k)

@[simp] theorem squaredCombinedIndexedRun_zero (idx : Nat) (c : Cfg)
    (k : Nat) (s : AState) : squaredCombinedIndexedRun idx c k 0 s = s := rfl

@[simp] theorem squaredCombinedIndexedRun_succ (idx : Nat) (c : Cfg)
    (k fuel : Nat) (s : AState) :
    squaredCombinedIndexedRun idx c k (fuel + 1) s =
      arun (idx + fuel) (squaredCombinedIndexedRun idx c k fuel s)
        (c.coreBody ++ mobiusLiveSquaredResidue k) := rfl

/-- The changing-index runner is the `List.range` fold used by
`AProgram.denote` and by the generic fail-safe audit bridge. -/
theorem foldl_range_squaredCombined_eq_indexedRun (idx : Nat) (c : Cfg)
    (k fuel : Nat) (s : AState) :
    (List.range fuel).foldl
      (fun q j => arun (idx + j) q
        (c.coreBody ++ mobiusLiveSquaredResidue k)) s =
      squaredCombinedIndexedRun idx c k fuel s := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih,
        squaredCombinedIndexedRun_succ]
      rfl

/-- Index-zero form matching a closed `AProgram` body fold literally. -/
theorem foldl_range_squaredCombined_eq_indexedRun_zero (c : Cfg)
    (k fuel : Nat) (s : AState) :
    (List.range fuel).foldl
      (fun q j => arun j q
        (c.coreBody ++ mobiusLiveSquaredResidue k)) s =
      squaredCombinedIndexedRun 0 c k fuel s := by
  simpa only [Nat.zero_add] using
    foldl_range_squaredCombined_eq_indexedRun 0 c k fuel s

theorem squaredCombinedIndexedRun_add (idx : Nat) (c : Cfg)
    (k a b : Nat) (s : AState) :
    squaredCombinedIndexedRun idx c k (a + b) s =
      squaredCombinedIndexedRun (idx + a) c k b
        (squaredCombinedIndexedRun idx c k a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ, squaredCombinedIndexedRun_succ,
        squaredCombinedIndexedRun_succ, ih]
      have heq : idx + (a + b) = idx + a + b := by omega
      rw [heq]

/-- Consecutive complete windows of the squared production trace. -/
def squaredCombinedWindowRun (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) : AState :=
  squaredCombinedIndexedRun idx c k (fuel * c.period) s

@[simp] theorem squaredCombinedWindowRun_zero (idx : Nat) (c : Cfg)
    (k : Nat) (s : AState) : squaredCombinedWindowRun idx c k 0 s = s := by
  simp [squaredCombinedWindowRun]

theorem squaredCombinedWindowRun_succ (idx : Nat) (c : Cfg)
    (k fuel : Nat) (s : AState) :
    squaredCombinedWindowRun idx c k (fuel + 1) s =
      squaredCombinedIndexedRun (idx + fuel * c.period) c k c.period
        (squaredCombinedWindowRun idx c k fuel s) := by
  simp only [squaredCombinedWindowRun, Nat.add_mul, Nat.one_mul]
  exact squaredCombinedIndexedRun_add idx c k (fuel * c.period) c.period s

/-- The squared trace retains exactly the standalone indexed core trace. -/
theorem squaredCombinedIndexedRun_core (idx : Nat) (c : Cfg)
    (k fuel : Nat) {s t : AState} (h : CoreAgree s t) :
    CoreAgree (squaredCombinedIndexedRun idx c k fuel s)
      (indexedBodyRun idx c fuel t) := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
      rw [squaredCombinedIndexedRun_succ, indexedBodyRun_succ]
      exact arun_squaredCombined_core c k (idx + n) ih

/-- The squared combined runner preserves the machine-word invariant. -/
theorem squaredCombinedIndexedRun_word (idx : Nat) (c : Cfg)
    (k fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M) :
    (∀ j, (squaredCombinedIndexedRun idx c k fuel s).regs j < M) ∧
      (∀ j, (squaredCombinedIndexedRun idx c k fuel s).arr j < M) := by
  induction fuel with
  | zero => exact ⟨hregs, harr⟩
  | succ n ih =>
      rw [squaredCombinedIndexedRun_succ]
      exact arun_word (idx + n) _ _ ih.1 ih.2

/-- The core itself leaves every persistent residue field unchanged. -/
theorem readRes_arun_coreBody (c : Cfg) (idx : Nat) (s : AState) :
    readRes (arun idx s c.coreBody) = readRes s := by
  unfold readRes
  congr 1

/-- One actual combined event advances the transparent squared model. -/
theorem readRes_arun_squaredCombined (c : Cfg) (k len idx : Nat)
    (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M)
    (hn0 : (arun idx s c.coreBody).regs 65 ≠ 0) (hk : k ≤ 15)
    (hn : (arun idx s c.coreBody).regs 65 + 2 ^ (k + 2) < M)
    (hu : let core := arun idx s c.coreBody
      let w := wPair k (core.regs 65)
      let t := accStep (core.regs 79) (core.regs 80) w.1 w.2
        (core.regs rTLo) (core.regs rTHi)
      let a := absBias (vBias k t.1 t.2)
      a + (core.regs 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) :
    readRes (arun idx s (c.coreBody ++ mobiusLiveSquaredResidue k)) =
      squaredResStep k (readSig (arun idx s c.coreBody)) (readRes s) := by
  let core := arun idx s c.coreBody
  have hword := arun_word idx c.coreBody s hregs harr
  rw [arun_append, readRes_arun_squaredResidue k len idx core
    hword.1 hword.2 hn0 hk hn hu]
  rw [readRes_arun_coreBody]

/-- The exact signal sequence consumed by a finite squared trace. -/
def squaredCombinedSignals (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) : List Sig :=
  (List.range fuel).map fun j =>
    readSig (arun (idx + j)
      (squaredCombinedIndexedRun idx c k j s) c.coreBody)

/- Squared signal traces split at the same arbitrary event boundary as their
changing-index runner. -/
set_option maxRecDepth 10000 in
theorem squaredCombinedSignals_add (idx : Nat) (c : Cfg) (k a b : Nat)
    (s : AState) :
    squaredCombinedSignals idx c k (a + b) s =
      squaredCombinedSignals idx c k a s ++
        squaredCombinedSignals (idx + a) c k b
          (squaredCombinedIndexedRun idx c k a s) := by
  unfold squaredCombinedSignals
  rw [List.range_add, List.map_append, List.map_map]
  let pre : List Sig := (List.range a).map fun j =>
    readSig (arun (idx + j)
      (squaredCombinedIndexedRun idx c k j s) c.coreBody)
  refine congrArg (fun tail : List Sig => pre ++ tail) ?_
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  have hidx : idx + (a + j) = idx + a + j := (Nat.add_assoc idx a j).symm
  have hstate := squaredCombinedIndexedRun_add idx c k a j s
  have hi := congrArg (fun index =>
    arun index (squaredCombinedIndexedRun idx c k (a + j) s)
      c.coreBody) hidx
  have hs := congrArg (fun state =>
    arun (idx + a + j) state c.coreBody) hstate
  exact congrArg readSig (hi.trans hs)

/-- Iterating the squared model over an arbitrary finite signal list. -/
def squaredResFold (k : Nat) : List Sig → Res → Res
  | [], r => r
  | g :: gs, r => squaredResFold k gs (squaredResStep k g r)

/-- A disabled production event is also transparent to the squared checker.
In particular, root and marking events cannot create receipt failures. -/
theorem squaredResStep_idle (k n : Nat) (r : Res)
    (hlo : r.tLo < M) (hhi : r.tHi < M)
    (hc : r.cel < M) (hcs : r.celSq < M) (hv : r.viol < M) :
    squaredResStep k (idleSig n) r = r := by
  simp [squaredResStep, idleSig, accStep, celStep, squaredViolStep,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hcs, Nat.mod_eq_of_lt hv]

/-- Every transparent squared step preserves the five machine-word bounds. -/
theorem squaredResStep_word (k : Nat) (g : Sig) (r : Res) :
    ResWord (squaredResStep k g r) := by
  unfold ResWord squaredResStep
  dsimp only
  exact ⟨accStep_fst_lt _ _ _ _ _ _, accStep_snd_lt _ _ _ _ _ _,
    Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos⟩

/-- A finite production signal list consists of arbitrary proved idle events
interleaved with a consecutive mathematical Möbius suffix.  The final index is
the number of active rows, not the (much larger) compiled event count. -/
inductive ConsecutiveSignalSchedule (mu : Nat → Int) :
    Nat → List Sig → Nat → Prop
  | nil (lo : Nat) : ConsecutiveSignalSchedule mu lo [] 0
  | idle {lo n N : Nat} {xs : List Sig}
      (tail : ConsecutiveSignalSchedule mu lo xs N) :
      ConsecutiveSignalSchedule mu lo (idleSig n :: xs) N
  | step {lo N : Nat} {xs : List Sig}
      (tail : ConsecutiveSignalSchedule mu (lo + 1) xs N) :
      ConsecutiveSignalSchedule mu lo (muSig mu (lo + 1) :: xs) (N + 1)

/-- Canonical list of the next `N` mathematical signals after prefix `lo`. -/
def consecutiveMuSignals (mu : Nat → Int) : Nat → Nat → List Sig
  | _, 0 => []
  | lo, N + 1 => muSig mu (lo + 1) ::
      consecutiveMuSignals mu (lo + 1) N

theorem consecutiveMuSignals_schedule (mu : Nat → Int) (lo N : Nat) :
    ConsecutiveSignalSchedule mu lo (consecutiveMuSignals mu lo N) N := by
  induction N generalizing lo with
  | zero => exact .nil lo
  | succ N ih => exact .step (ih (lo + 1))

/-- The recursive mathematical signal list is the pointwise map over its
zero-based finite offset range. -/
theorem consecutiveMuSignals_eq_map_range (mu : Nat → Int) (lo N : Nat) :
    consecutiveMuSignals mu lo N =
      (List.range N).map fun j => muSig mu (lo + j + 1) := by
  induction N generalizing lo with
  | zero => rfl
  | succ N ih =>
      rw [List.range_succ_eq_map]
      simp only [consecutiveMuSignals, List.map_cons, List.map_map,
        Nat.add_zero]
      rw [ih]
      apply congrArg (List.cons (muSig mu (lo + 1)))
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_apply]
      congr 2
      omega

/-- A list of literal idle signals advances neither the mathematical prefix
nor its active-row count. -/
theorem ConsecutiveSignalSchedule.of_all_idle
    (mu : Nat → Int) (lo : Nat) (xs : List Sig)
    (h : ∀ g, g ∈ xs → ∃ n, g = idleSig n) :
    ConsecutiveSignalSchedule mu lo xs 0 := by
  induction xs with
  | nil => exact .nil lo
  | cons g gs ih =>
      obtain ⟨n, rfl⟩ := h g (by simp)
      exact .idle (ih (fun x hx => h x (by simp [hx])))

/-- A production signal segment is scheduled as entirely idle whenever each
of its literal event offsets is proved to emit an idle signal. -/
theorem squaredCombinedSignals_schedule_of_all_idle
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState)
    (h : ∀ j, j < fuel → ∃ n,
      readSig (arun (idx + j) (squaredCombinedIndexedRun idx c k j s)
        c.coreBody) = idleSig n) :
    ConsecutiveSignalSchedule mu lo
      (squaredCombinedSignals idx c k fuel s) 0 := by
  apply ConsecutiveSignalSchedule.of_all_idle
  intro g hg
  unfold squaredCombinedSignals at hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact h j (List.mem_range.mp hj)

/-- A production segment whose literal signals are the next mathematical
Möbius values has the canonical consecutive schedule. -/
theorem squaredCombinedSignals_schedule_of_active
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState)
    (h : ∀ j, j < fuel →
      readSig (arun (idx + j) (squaredCombinedIndexedRun idx c k j s)
        c.coreBody) = muSig mu (lo + j + 1)) :
    ConsecutiveSignalSchedule mu lo
      (squaredCombinedSignals idx c k fuel s) fuel := by
  have heq :
      (List.range fuel).map (fun j =>
        readSig (arun (idx + j) (squaredCombinedIndexedRun idx c k j s)
          c.coreBody)) =
      (List.range fuel).map (fun j => muSig mu (lo + j + 1)) := by
    apply List.map_congr_left
    intro j hj
    exact h j (List.mem_range.mp hj)
  rw [squaredCombinedSignals, heq, ← consecutiveMuSignals_eq_map_range]
  exact consecutiveMuSignals_schedule mu lo fuel

/-- Scheduled fragments compose when the second begins at the first fragment's
mathematical endpoint. -/
theorem ConsecutiveSignalSchedule.append
    {mu : Nat → Int} {lo A B : Nat} {xs ys : List Sig}
    (hx : ConsecutiveSignalSchedule mu lo xs A)
    (hy : ConsecutiveSignalSchedule mu (lo + A) ys B) :
    ConsecutiveSignalSchedule mu lo (xs ++ ys) (A + B) := by
  induction hx with
  | nil lo => simpa using hy
  | idle tail ih =>
      exact .idle (ih hy)
  | @step lo N xs tail ih =>
      have hy' : ConsecutiveSignalSchedule mu ((lo + 1) + N) ys B := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy
      have htail := ih hy'
      simpa only [List.cons_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ConsecutiveSignalSchedule.step htail

/-- Erasing the proved idle events from a scheduled production list leaves
exactly the shifted consecutive squared run. -/
theorem ConsecutiveSignalSchedule.squaredResFold_eq_runFrom
    {mu : Nat → Int} {lo N : Nat} {xs : List Sig}
    (h : ConsecutiveSignalSchedule mu lo xs N)
    (k : Nat) (r : Res) (hw : ResWord r) :
    squaredResFold k xs r = squaredResRunFrom k mu lo r N := by
  induction h generalizing r with
  | nil lo => rfl
  | idle tail ih =>
      simp only [squaredResFold]
      rw [squaredResStep_idle k _ r hw.1 hw.2.1 hw.2.2.1
        hw.2.2.2.1 hw.2.2.2.2]
      exact ih r hw
  | step tail ih =>
      simp only [squaredResFold]
      rw [ih (squaredResStep k (muSig mu (_ + 1)) r)
        (squaredResStep_word k (muSig mu (_ + 1)) r)]
      exact (squaredResRunFrom_succ_shift k mu _ r _).symm

/-- Equality of the four persistent fields shared by the old and squared
residue models.  The violation counters are intentionally independent. -/
def ResPrefixEq (a b : Res) : Prop :=
  a.tLo = b.tLo ∧ a.tHi = b.tHi ∧ a.cel = b.cel ∧ a.celSq = b.celSq

/-- The Möbius accumulator invariant depends only on the four persistent
fields shared by the historical and squared checkers. -/
theorem ResPrefixEq.resInv {k n : Nat} {mu : Nat → Int} {a b : Res}
    (hab : ResPrefixEq a b) (hb : ResInv k mu n b) : ResInv k mu n a := by
  rcases hab with ⟨hlo, hhi, hcel, hcelSq⟩
  exact
    { loLt := by simpa only [hlo] using hb.loLt
      hiLt := by simpa only [hhi] using hb.hiLt
      acc := by simpa only [hlo, hhi] using hb.acc
      bnd := hb.bnd
      cel := by simpa only [hcel] using hb.cel
      celSq := by simpa only [hcel, hcelSq] using hb.celSq
      celLt := by simpa only [hcel] using hb.celLt }

theorem squaredResStep_resStep_prefix_eq (k : Nat) (g : Sig) (a b : Res)
    (h : ResPrefixEq a b) :
    ResPrefixEq (squaredResStep k g a) (resStep k g b) := by
  rcases a with ⟨alo, ahi, ac, acs, av⟩
  rcases b with ⟨blo, bhi, bc, bcs, bv⟩
  simp only [ResPrefixEq] at h ⊢
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  simp [squaredResStep, resStep]

/-- Any finite squared fold has the same accumulator and ceiling fields as
the old fold over the same signals, provided those fields agree initially. -/
theorem squaredResFold_resFold_prefix_eq (k : Nat) (xs : List Sig)
    (a b : Res) (h : ResPrefixEq a b) :
    ResPrefixEq (squaredResFold k xs a) (resFold k xs b) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
      exact ih _ _ (squaredResStep_resStep_prefix_eq k g a b h)

theorem squaredResFold_resFold_prefix_eq_self (k : Nat) (xs : List Sig)
    (r : Res) :
    ResPrefixEq (squaredResFold k xs r) (resFold k xs r) := by
  exact squaredResFold_resFold_prefix_eq k xs r r ⟨rfl, rfl, rfl, rfl⟩

/-- Any invariant established for the historical fold transfers directly to
the paper-faithful squared fold over the identical finite signal trace. -/
theorem squaredResFold_inv_of_resFold_inv (k n : Nat) (mu : Nat → Int)
    (xs : List Sig) (r : Res)
    (h : ResInv k mu n (resFold k xs r)) :
    ResInv k mu n (squaredResFold k xs r) :=
  (squaredResFold_resFold_prefix_eq_self k xs r).resInv h

theorem squaredResFold_append (k : Nat) (xs ys : List Sig) (r : Res) :
    squaredResFold k (xs ++ ys) r =
      squaredResFold k ys (squaredResFold k xs r) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, squaredResFold] using
        ih (squaredResStep k x r)

set_option maxRecDepth 10000 in
/-- The literal finite trace is exactly the transparent fold over the signals
emitted by that same production trace. -/
theorem readRes_squaredCombinedIndexedRun_eq_fold
    (idx : Nat) (c : Cfg) (k len fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hready : ∀ j, j < fuel →
      let before := squaredCombinedIndexedRun idx c k j s
      let core := arun (idx + j) before c.coreBody
      core.regs 65 ≠ 0 ∧
      core.regs 65 + 2 ^ (k + 2) < M ∧
      (let w := wPair k (core.regs 65)
       let t := accStep (core.regs 79) (core.regs 80) w.1 w.2
         (core.regs rTLo) (core.regs rTHi)
       let a := absBias (vBias k t.1 t.2)
       a + (core.regs 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M)) :
    readRes (squaredCombinedIndexedRun idx c k fuel s) =
      squaredResFold k (squaredCombinedSignals idx c k fuel s)
        (readRes s) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (fun j hj => hready j (by omega))
      have hword := squaredCombinedIndexedRun_word idx c k n s hregs harr
      have hr := hready n (Nat.lt_succ_self n)
      rw [squaredCombinedIndexedRun_succ]
      rw [readRes_arun_squaredCombined c k len (idx + n)
        (squaredCombinedIndexedRun idx c k n s) hword.1 hword.2
        hr.1 hk hr.2.1 hr.2.2]
      rw [hprev]
      simp [squaredCombinedSignals, List.range_succ,
        squaredResFold_append, squaredResFold]

set_option maxRecDepth 10000 in
/-- Campaign-facing trace theorem.  Below `2^62`, the format lemma discharges
both squared-suffix no-wrap conditions uniformly, including on idle and
marking events. -/
theorem readRes_squaredCombinedIndexedRun_eq_fold_of_n_lt
    (idx : Nat) (c : Cfg) (k len fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hready : ∀ j, j < fuel →
      let before := squaredCombinedIndexedRun idx c k j s
      let core := arun (idx + j) before c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun idx c k fuel s) =
      squaredResFold k (squaredCombinedSignals idx c k fuel s)
        (readRes s) := by
  apply readRes_squaredCombinedIndexedRun_eq_fold idx c k len fuel s
    hregs harr hk
  intro j hj
  let core := arun (idx + j)
    (squaredCombinedIndexedRun idx c k j s) c.coreBody
  have hr : core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := hready j hj
  have hb := squaredResidue_word_bounds k (core.regs 65)
    (core.regs 79) (core.regs 80) (core.regs rTLo) (core.regs rTHi)
    hk hr.2
  exact ⟨hr.1, hb.1, hb.2⟩

end LeanCompCert.Ports.ArraySegMobiusSquaredFold
