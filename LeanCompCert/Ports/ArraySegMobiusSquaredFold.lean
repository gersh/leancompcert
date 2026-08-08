import LeanCompCert.Ports.MobiusSquaredResidueWindow
import LeanCompCert.Ports.ArraySegMobiusResidueFrame

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

/-- Iterating the squared model over an arbitrary finite signal list. -/
def squaredResFold (k : Nat) : List Sig → Res → Res
  | [], r => r
  | g :: gs, r => squaredResFold k gs (squaredResStep k g r)

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

end LeanCompCert.Ports.ArraySegMobiusSquaredFold
