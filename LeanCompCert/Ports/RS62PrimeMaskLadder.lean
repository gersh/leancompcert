import LeanCompCert.Ports.RamareCombined100MLogSweep
import LeanCompCert.Ports.RS62LoopE
import LeanCompCert.Verified.ArrayPipeline

/-!
# Linear RS62 ladder over a caller-owned prime mask

The older guarded RS62 port performs a bounded least-factor scan for every
candidate.  That is useful as a small control, but its production cost is
superlinear.  This module is the second stage of the production route: a
segmented sieve supplies one `0`/`1` cell per candidate, and this compiled
program consumes those cells in one linear pass.

The sieve is intentionally not trusted here.  The source theorem below is
parametric in the caller-owned array and exposes exactly the mask fact that a
later segmented-sieve refinement must prove.  No candidate range or prime
list is evaluated in Lean.
-/

namespace LeanCompCert.Ports.RS62PrimeMaskLadder

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62 (fpD incLWord incUWord)

abbrev rAddr : Nat := 20
abbrev rGate : Nat := 11
abbrev rN : Nat := 132

abbrev rLogL : Nat :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL
abbrev rLogU : Nat :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU
abbrev regCount : Nat :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.regCount

/-- Install the two carried ladder endpoints. -/
def init (SL SU : Nat) : List AInstr :=
  [ .scalar (.mov rLogL (.lit SL))
  , .scalar (.mov rLogU (.lit SU)) ]

/-- Decode one candidate and load its precomputed primality bit. -/
def maskPrefix (n0 : Nat) : List AInstr :=
  [ .scalar (.mov rAddr .idx)
  , .load rGate rAddr
  , .scalar (.binop rN .add (.lit (n0 - 1)) .idx) ]

/-- One candidate: load its mask bit, compute both exact word-safe RS62
increments, and gate the two additions by that bit. -/
def body (n0 : Nat) : List AInstr :=
  maskPrefix n0 ++
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody

def program (n0 f SL SU out : Nat) : AProgram := {
  regCount := regCount
  arrayLen := f
  loopCount := f
  init := init SL SU
  body := body n0
  epilogue := []
  output := out
}

/-! ## Pure mask semantics -/

/-- The arithmetic transition executed by one mask cell. -/
def maskStep (arr : Nat → Nat) (n0 : Nat)
    (state : Nat × Nat) (k : Nat) : Nat × Nat :=
  (state.1 + arr k * incLWord ((n0 - 1) + k),
    state.2 + arr k * incUWord ((n0 - 1) + k))

/-- The linear source model of the compiled mask consumer. -/
def maskFold (arr : Nat → Nat) (n0 f SL SU : Nat) : Nat × Nat :=
  (List.range f).foldl (maskStep arr n0) (SL, SU)

/-- Exact source meaning required of a sieve-produced mask. -/
def MaskCorrect (p : Nat → Bool) (arr : Nat → Nat)
    (n0 f : Nat) : Prop :=
  ∀ k, k < f → arr k = if p (n0 + k) then 1 else 0

private theorem foldl_congr_mem {A B : Type _} (l : List B)
    (left right : A → B → A) (init : A)
    (h : ∀ state x, x ∈ l → left state x = right state x) :
    l.foldl left init = l.foldl right init := by
  induction l generalizing init with
  | nil => rfl
  | cons x rest ih =>
      rw [List.foldl_cons, List.foldl_cons, h init x (by simp)]
      exact ih _ (fun state y hy => h state y (by simp [hy]))

/-- A correct mask makes the pure linear fold exactly the source RS62
recurrence.  This is symbolic in `f`; no range is evaluated in Lean. -/
theorem maskFold_eq_loopE (p : Nat → Bool) (arr : Nat → Nat)
    (n0 f SL SU : Nat) (hn0 : 3 ≤ n0)
    (hmask : MaskCorrect p arr n0 f) :
    maskFold arr n0 f SL SU =
      LeanCompCert.Ports.RS62.loopE p f n0 SL SU := by
  rw [LeanCompCert.Ports.RS62.loopE_eq_foldl,
    List.range'_eq_map_range, List.foldl_map]
  unfold maskFold
  apply foldl_congr_mem (List.range f)
  intro state k hk
  have hkf : k < f := List.mem_range.mp hk
  have hcell := hmask k hkf
  have harg : (n0 - 1) + k = n0 + k - 1 := by omega
  unfold maskStep LeanCompCert.Ports.RS62.stepGuarded
  rw [harg, hcell]
  by_cases hp : p (n0 + k) = true
  · rw [if_pos hp, if_pos hp]
    simpa [LeanCompCert.Ports.RS62.stepWord] using
      (LeanCompCert.Ports.RS62.stepWord_eq_stepRef state (n0 + k)
        (by omega))
  · simp only [Bool.not_eq_true] at hp
    simp [hp]

/-- Explicit no-wrap premises for the linear mask consumer.  They are stated
on pure prefix folds, so a compiled audit can establish source definedness
without Lean evaluating any production prefix. -/
def Room (arr : Nat → Nat) (n0 f SL SU : Nat) : Prop :=
  ∀ k, k < f →
    let state := maskFold arr n0 k SL SU
    state.1 + arr k * incLWord ((n0 - 1) + k) < M ∧
      state.2 + arr k * incUWord ((n0 - 1) + k) < M

theorem maskFold_succ (arr : Nat → Nat) (n0 f SL SU : Nat) :
    maskFold arr n0 (f + 1) SL SU =
      maskStep arr n0 (maskFold arr n0 f SL SU) f := by
  unfold maskFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Every correct-mask prefix is bounded by a deliberately coarse linear
majorant.  This is symbolic in the prefix length and is used only to prove
machine-word room; it does not evaluate a production fold. -/
theorem maskFold_prefix_bounds (p : Nat → Bool) (arr : Nat → Nat)
    (n0 f SL SU k : Nat) (hn0 : 3 ≤ n0) (hk : k ≤ f)
    (hmask : MaskCorrect p arr n0 f) :
    let state := maskFold arr n0 k SL SU
    state.1 ≤ SL + k * fpD ∧
      state.2 ≤ SU + k * (fpD + n0 + f) := by
  induction k with
  | zero => simp [maskFold]
  | succ k ih =>
      have hkf : k < f := by omega
      have hprev := ih (by omega)
      rw [maskFold_succ]
      dsimp only [maskStep]
      rw [hmask k hkf]
      cases hp : p (n0 + k) with
      | false =>
        simp only [hp, Bool.false_eq_true, if_false, Nat.zero_mul,
          Nat.add_zero]
        constructor
        · exact Nat.le_trans hprev.1 (by
            rw [Nat.succ_mul]
            omega)
        · exact Nat.le_trans hprev.2 (by
            rw [Nat.succ_mul]
            omega)
      | true =>
        simp only [hp, if_pos, Nat.one_mul]
        have hL := LeanCompCert.Ports.RS62.incLWord_le ((n0 - 1) + k)
        have hU := LeanCompCert.Ports.RS62.incUWord_le ((n0 - 1) + k)
        have hU' : incUWord ((n0 - 1) + k) ≤ fpD + n0 + f := by omega
        constructor
        · calc
            (maskFold arr n0 k SL SU).1 + incLWord ((n0 - 1) + k)
                ≤ (SL + k * fpD) + fpD := Nat.add_le_add hprev.1 hL
            _ = SL + (k + 1) * fpD := by rw [Nat.succ_mul]; omega
        · calc
            (maskFold arr n0 k SL SU).2 + incUWord ((n0 - 1) + k)
                ≤ (SU + k * (fpD + n0 + f)) + (fpD + n0 + f) :=
                  Nat.add_le_add hprev.2 hU'
            _ = SU + (k + 1) * (fpD + n0 + f) := by
              rw [Nat.succ_mul]
              omega

/-- Two scalar endpoint inequalities imply every `Room` premise for the
linear mask consumer.  A campaign checks only these small inequalities;
Lean never replays the candidate range. -/
theorem room_of_endpoint_bounds (p : Nat → Bool) (arr : Nat → Nat)
    (n0 f SL SU : Nat) (hn0 : 3 ≤ n0)
    (hmask : MaskCorrect p arr n0 f)
    (hSL : SL + f * fpD + fpD < M)
    (hSU : SU + f * (fpD + n0 + f) + (fpD + n0 + f) < M) :
    Room arr n0 f SL SU := by
  intro k hk
  have hprefix := maskFold_prefix_bounds p arr n0 f SL SU k hn0
    (Nat.le_of_lt hk) hmask
  dsimp only at hprefix ⊢
  have hcell := hmask k hk
  rw [hcell]
  have hL := LeanCompCert.Ports.RS62.incLWord_le ((n0 - 1) + k)
  have hU := LeanCompCert.Ports.RS62.incUWord_le ((n0 - 1) + k)
  have hU' : incUWord ((n0 - 1) + k) ≤ fpD + n0 + f := by omega
  have hkLe : k ≤ f := Nat.le_of_lt hk
  have hkMulL : k * fpD ≤ f * fpD := Nat.mul_le_mul_right fpD hkLe
  have hkMulU : k * (fpD + n0 + f) ≤ f * (fpD + n0 + f) :=
    Nat.mul_le_mul_right (fpD + n0 + f) hkLe
  cases hp : p (n0 + k) with
  | false =>
      simp only [hp, Bool.false_eq_true, if_false, Nat.zero_mul,
        Nat.add_zero]
      constructor
      · exact Nat.lt_of_le_of_lt
          (Nat.le_trans hprefix.1 (Nat.add_le_add_left hkMulL SL)) (by omega)
      · exact Nat.lt_of_le_of_lt
          (Nat.le_trans hprefix.2 (Nat.add_le_add_left hkMulU SU)) (by omega)
  | true =>
      simp only [hp, if_pos, Nat.one_mul]
      constructor
      · calc
          (maskFold arr n0 k SL SU).1 + incLWord ((n0 - 1) + k)
              ≤ (SL + k * fpD) + fpD := Nat.add_le_add hprefix.1 hL
          _ ≤ (SL + f * fpD) + fpD := by omega
          _ < M := by omega
      · calc
          (maskFold arr n0 k SL SU).2 + incUWord ((n0 - 1) + k)
              ≤ (SU + k * (fpD + n0 + f)) + (fpD + n0 + f) :=
                Nat.add_le_add hprefix.2 hU'
          _ ≤ (SU + f * (fpD + n0 + f)) + (fpD + n0 + f) := by omega
          _ < M := by omega

/-- Total machine-state fold used by the receipt bridge. -/
def machineFoldState (arr : Nat → Nat) (n0 f SL SU : Nat) : AState :=
  (List.range f).foldl (fun s k => arun k s (body n0))
    (arun 0 (initialAStateWithArray arr) (init SL SU))

theorem machineFoldState_succ (arr : Nat → Nat)
    (n0 f SL SU : Nat) :
    machineFoldState arr n0 (f + 1) SL SU =
      arun f (machineFoldState arr n0 f SL SU) (body n0) := by
  unfold machineFoldState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

set_option maxRecDepth 40000 in
theorem init_all (SL SU : Nat) :
    (init SL SU).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem body_all (n0 : Nat) :
    (body n0).all (ainstrWFB regCount) = true := by rfl

/-- The linear mask consumer is accepted by the proved array compiler. -/
theorem program_wf (n0 f SL SU out : Nat) (hout : out < regCount) :
    (program n0 f SL SU out).WF :=
  ⟨hout, forall_wf_of_all (init_all SL SU),
    forall_wf_of_all (body_all n0), by simp [program]⟩

/-- Exact total semantics of the three-instruction mask prefix. -/
theorem maskPrefix_run (n0 k : Nat) (s : AState)
    (hkM : k < M) (hnM : (n0 - 1) + k < M) :
    let out := arun k s (maskPrefix n0)
    out.regs rAddr = k ∧
      out.regs rGate = s.arr k ∧
      out.regs rN = (n0 - 1) + k ∧
      out.regs rLogL = s.regs rLogL ∧
      out.regs rLogU = s.regs rLogU ∧
      out.arr = s.arr := by
  simp [maskPrefix, arun, astep, rAddr, rGate, rN,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hnM]

/-- One loaded mask cell advances the two carried endpoints exactly.  The
only arithmetic hypotheses are the literal machine-word bounds used by the
compiled divisions and additions. -/
theorem body_run (n0 k : Nat) (s : AState)
    (hkM : k < M) (hn2 : 2 ≤ (n0 - 1) + k)
    (hn40 : (n0 - 1) + k ≤ 2 ^ 40)
    (hnM : (n0 - 1) + k < M)
    (hLower : s.regs rLogL + s.arr k * incLWord ((n0 - 1) + k) < M)
    (hUpper : s.regs rLogU + s.arr k * incUWord ((n0 - 1) + k) < M) :
    let out := arun k s (body n0)
    out.regs rLogL =
        s.regs rLogL + s.arr k * incLWord ((n0 - 1) + k) ∧
      out.regs rLogU =
        s.regs rLogU + s.arr k * incUWord ((n0 - 1) + k) ∧
      out.regs rN = (n0 - 1) + k ∧ out.arr = s.arr := by
  let pre := arun k s (maskPrefix n0)
  have hp := maskPrefix_run n0 k s hkM hnM
  change pre.regs rAddr = k ∧ pre.regs rGate = s.arr k ∧
    pre.regs rN = (n0 - 1) + k ∧ pre.regs rLogL = s.regs rLogL ∧
    pre.regs rLogU = s.regs rLogU ∧ pre.arr = s.arr at hp
  rcases hp with ⟨hAddr, hGate, hN, hLogL, hLogU, hArr⟩
  have hCandidate :=
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody_run k pre
    (by rw [hN]; exact hn2)
    (by rw [hN]; exact hn40)
    (by rw [hGate, hN]; omega)
    (by rw [hLogL, hGate, hN]; exact hLower)
    (by rw [hGate, hN]; omega)
    (by rw [hLogU, hGate, hN]; exact hUpper)
  change
    let out := arun k pre
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody
    out.regs rLogL =
        pre.regs rLogL + pre.regs rGate * incLWord (pre.regs rN) ∧
      out.regs rLogU =
        pre.regs rLogU + pre.regs rGate * incUWord (pre.regs rN) ∧
      out.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL =
        incLWord (pre.regs rN) ∧
      out.regs LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU =
        incUWord (pre.regs rN) ∧
      out.regs rN = pre.regs rN ∧ out.arr = pre.arr at hCandidate
  dsimp only
  rw [show arun k s (body n0) = arun k pre
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody by
    simp only [body, arun_append, pre]]
  refine ⟨hCandidate.1.trans ?_, hCandidate.2.1.trans ?_,
    hCandidate.2.2.2.2.1.trans hN,
    hCandidate.2.2.2.2.2.trans hArr⟩
  · rw [hLogL, hGate, hN]
  · rw [hLogU, hGate, hN]

/-- The total machine fold has exactly the pure mask-fold observation.  The
proof is an induction over symbolic fuel; production values remain opaque. -/
theorem machineFoldState_observe (arr : Nat → Nat)
    (n0 f SL SU : Nat) (hn0 : 3 ≤ n0) (hSL : SL < M) (hSU : SU < M)
    (hfM : f < M) (hEnd : n0 + f ≤ 2 ^ 40)
    (hRoom : Room arr n0 f SL SU) :
    let out := machineFoldState arr n0 f SL SU
    out.regs rLogL = (maskFold arr n0 f SL SU).1 ∧
      out.regs rLogU = (maskFold arr n0 f SL SU).2 ∧
      out.arr = arr := by
  induction f with
  | zero =>
      simp [machineFoldState, maskFold, init, arun, astep,
        initialAStateWithArray, AState.writeReg, sdest, sval, denoteOperand,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
        Nat.mod_eq_of_lt hSL, Nat.mod_eq_of_lt hSU]
  | succ f ih =>
      have hfM' : f < M := by omega
      have hEnd' : n0 + f ≤ 2 ^ 40 := by omega
      have hRoom' : Room arr n0 f SL SU := by
        intro k hk
        exact hRoom k (by omega)
      have hmid := ih hfM' hEnd' hRoom'
      let mid := machineFoldState arr n0 f SL SU
      change mid.regs rLogL = (maskFold arr n0 f SL SU).1 ∧
        mid.regs rLogU = (maskFold arr n0 f SL SU).2 ∧
        mid.arr = arr at hmid
      have hroomLast := hRoom f (Nat.lt_succ_self f)
      dsimp only at hroomLast
      have hWord : 2 ^ 40 < M := by decide
      have hnM : (n0 - 1) + f < M := by omega
      have hstep := body_run n0 f mid
        (by omega) (by omega) (by omega) hnM
        (by rw [hmid.1, hmid.2.2]; exact hroomLast.1)
        (by rw [hmid.2.1, hmid.2.2]; exact hroomLast.2)
      rw [machineFoldState_succ, maskFold_succ]
      change
        (arun f mid (body n0)).regs rLogL =
            (maskStep arr n0 (maskFold arr n0 f SL SU) f).1 ∧
          (arun f mid (body n0)).regs rLogU =
            (maskStep arr n0 (maskFold arr n0 f SL SU) f).2 ∧
          (arun f mid (body n0)).arr = arr
      dsimp only [maskStep]
      exact ⟨hstep.1.trans (by rw [hmid.1, hmid.2.2]),
        hstep.2.1.trans (by rw [hmid.2.1, hmid.2.2]),
        hstep.2.2.2.trans hmid.2.2⟩

/-- A successful compiled-consumer source run exposes the exact RS62 source
recurrence whenever its caller-owned prime mask is correct.  Physical audit
receipts establish `hRun`; this theorem performs no production fold in Lean. -/
theorem source_loopE_of_runFromArray (p : Nat → Bool)
    (arr : Nat → Nat) (n0 f SL SU outReg : Nat)
    (hn0 : 3 ≤ n0) (hSL : SL < M) (hSU : SU < M)
    (hfM : f < M) (hEnd : n0 + f ≤ 2 ^ 40)
    (hRoom : Room arr n0 f SL SU)
    (hmask : MaskCorrect p arr n0 f) (out : AState)
    (hRun : (program n0 f SL SU outReg).runFromArray arr = some out) :
    out.regs rLogL =
        (LeanCompCert.Ports.RS62.loopE p f n0 SL SU).1 ∧
      out.regs rLogU =
        (LeanCompCert.Ports.RS62.loopE p f n0 SL SU).2 ∧
      out.arr = arr := by
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (program n0 f SL SU outReg) arr out hRun
  have houtEq : out = machineFoldState arr n0 f SL SU := by
    simpa [program, machineFoldState, arun] using hout
  rw [houtEq]
  have hobs := machineFoldState_observe arr n0 f SL SU
    hn0 hSL hSU hfM hEnd hRoom
  rw [maskFold_eq_loopE p arr n0 f SL SU hn0 hmask] at hobs
  exact hobs

#print axioms program_wf
#print axioms maskPrefix_run
#print axioms body_run
#print axioms maskFold_eq_loopE
#print axioms room_of_endpoint_bounds
#print axioms machineFoldState_observe
#print axioms source_loopE_of_runFromArray

end LeanCompCert.Ports.RS62PrimeMaskLadder
