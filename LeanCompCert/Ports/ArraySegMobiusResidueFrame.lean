import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Ports.MobiusResidueWindow

/-! # Sieve/residue non-interference at total-state semantics

The production array program appends a scalar literature-specific residue to
each sieve-core iteration.  This file proves the core-facing projection of
that combined total-state trace is exactly the already-verified indexed sieve
trace.  The statement retains every production event, including marking
events whose signal gate is zero.
-/

namespace LeanCompCert.Ports.ArraySegMobiusResidueFrame

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Registers outside the residue's private register ranges. -/
def CoreReg (j : Nat) : Bool :=
  decide (¬((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171)))

/-- Two states agree on the complete sieve-facing projection. -/
def CoreAgree (s t : AState) : Prop :=
  s.arr = t.arr ∧ ∀ j, CoreReg j = true → s.regs j = t.regs j

theorem CoreAgree.refl (s : AState) : CoreAgree s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem CoreAgree.symm {s t : AState} (h : CoreAgree s t) : CoreAgree t s :=
  ⟨h.1.symm, fun j hj => (h.2 j hj).symm⟩

theorem CoreAgree.trans {s t u : AState} (hst : CoreAgree s t)
    (htu : CoreAgree t u) : CoreAgree s u :=
  ⟨hst.1.trans htu.1, fun j hj => (hst.2 j hj).trans (htu.2 j hj)⟩

/-- An operand reads only registers selected by `S`. -/
def OperandIn (S : Nat → Bool) : Operand → Bool
  | .reg j => S j
  | .lit _ => true
  | .idx => true

/-- Every register read or written by an instruction is selected by `S`. -/
def AInstrIn (S : Nat → Bool) : AInstr → Bool
  | .scalar (.mov d src) => S d && OperandIn S src
  | .scalar (.binop d _ lhs rhs) =>
      S d && OperandIn S lhs && OperandIn S rhs
  | .load d idx => S d && S idx
  | .store idx src => S idx && S src

private theorem operand_eq {S : Nat → Bool} {s t : AState}
    (h : CoreAgree s t) {o : Operand} (ho : OperandIn S o = true)
    (hS : ∀ j, S j = true → CoreReg j = true) (idx : Nat) :
    denoteOperand idx s.regs o = denoteOperand idx t.regs o := by
  cases o with
  | reg j =>
      exact h.2 j (hS j ho)
  | lit v => rfl
  | idx => rfl

private theorem sval_eq {S : Nat → Bool} {s t : AState}
    (h : CoreAgree s t) {i : Instr}
    (hi : match i with
      | .mov d src => S d && OperandIn S src
      | .binop d _ lhs rhs => S d && OperandIn S lhs && OperandIn S rhs)
    (hS : ∀ j, S j = true → CoreReg j = true) (idx : Nat) :
    LeanCompCert.Verified.InstrBlock.sval idx s.regs i =
      LeanCompCert.Verified.InstrBlock.sval idx t.regs i := by
  cases i with
  | mov d src =>
      simp only [Bool.and_eq_true] at hi
      simp only [LeanCompCert.Verified.InstrBlock.sval]
      exact operand_eq h hi.2 hS idx
  | binop d op lhs rhs =>
      simp only [Bool.and_eq_true] at hi
      simp only [LeanCompCert.Verified.InstrBlock.sval]
      rw [operand_eq h hi.1.2 hS idx, operand_eq h hi.2 hS idx]

/-- A syntactically core-only instruction preserves core agreement. -/
theorem astep_core_congr {S : Nat → Bool} {s t : AState} (h : CoreAgree s t)
    {a : AInstr} (ha : AInstrIn S a = true)
    (hS : ∀ j, S j = true → CoreReg j = true) (idx : Nat) :
    CoreAgree (astep idx s a) (astep idx t a) := by
  cases a with
  | scalar i =>
      cases i with
      | mov d src =>
          simp only [AInstrIn, Bool.and_eq_true] at ha
          have hd := hS d ha.1
          have hv : LeanCompCert.Verified.InstrBlock.sval idx s.regs (.mov d src) =
              LeanCompCert.Verified.InstrBlock.sval idx t.regs (.mov d src) :=
            sval_eq h (by simpa using ha) hS idx
          constructor
          · exact h.1
          · intro j hj
            by_cases hjd : j = d
            · subst j
              simpa [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg] using hv
            · simpa [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg, hjd] using h.2 j hj
      | binop d op lhs rhs =>
          simp only [AInstrIn, Bool.and_eq_true] at ha
          have hd := hS d ha.1.1
          have hv : LeanCompCert.Verified.InstrBlock.sval idx s.regs
                (.binop d op lhs rhs) =
              LeanCompCert.Verified.InstrBlock.sval idx t.regs
                (.binop d op lhs rhs) :=
            sval_eq h (by simpa using ha) hS idx
          constructor
          · exact h.1
          · intro j hj
            by_cases hjd : j = d
            · subst j
              simpa [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg] using hv
            · simpa [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg, hjd] using h.2 j hj
  | load d ir =>
      simp only [AInstrIn, Bool.and_eq_true] at ha
      have hir := h.2 ir (hS ir ha.2)
      constructor
      · exact h.1
      · intro j hj
        by_cases hjd : j = d
        · subst j
          simp [astep, AState.writeReg, hir, h.1]
        · simp [astep, AState.writeReg, hjd, h.2 j hj]
  | store ir sr =>
      simp only [AInstrIn, Bool.and_eq_true] at ha
      have hir := h.2 ir (hS ir ha.1)
      have hsr := h.2 sr (hS sr ha.2)
      constructor
      · funext j
        simp [astep, AState.writeArr, hir, hsr, h.1]
      · intro j hj
        exact h.2 j hj

/-- A core-only straight-line block preserves core agreement. -/
theorem arun_core_congr (S : Nat → Bool) (idx : Nat) :
    ∀ (l : List AInstr), l.all (AInstrIn S) = true →
      (∀ j, S j = true → CoreReg j = true) →
      ∀ (s t : AState), CoreAgree s t → CoreAgree (arun idx s l) (arun idx t l) := by
  intro l
  induction l with
  | nil => intro _ _ s t h; exact h
  | cons a rest ih =>
      intro hall hS s t h
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [arun_cons, arun_cons]
      exact ih hall.2 hS _ _ (astep_core_congr h hall.1 hS idx)

/-- The literal production core reads and writes no private residue register. -/
theorem coreBody_in_core (c : Cfg) :
    c.coreBody.all (AInstrIn CoreReg) = true := by
  rfl

/-- Consequently the production core respects the sieve-facing projection. -/
theorem arun_coreBody_congr (c : Cfg) (idx : Nat) {s t : AState}
    (h : CoreAgree s t) :
    CoreAgree (arun idx s c.coreBody) (arun idx t c.coreBody) :=
  arun_core_congr CoreReg idx c.coreBody (coreBody_in_core c)
    (fun _ h => h) s t h

private theorem residue_avoids_core (k j : Nat) (hj : CoreReg j = true) :
    (mobiusLiveResidue k).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 104 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj104
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj104⟩)
  have h150 : j < 150 ∨ 171 < j := by
    by_cases h : j < 150
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj171
      exact hw (Or.inr ⟨Nat.le_of_not_gt h, hj171⟩)
  simp [mobiusLiveResidue, avoidsReg, rTLo, rTHi, rCeil, rCeilSq, rMViol]
  rcases h100 with h100 | h100 <;>
    rcases h150 with h150 | h150 <;> omega

/-- The scalar residue leaves the entire sieve-facing projection unchanged. -/
theorem arun_residue_core_frame (k idx : Nat) (s : AState) :
    CoreAgree (arun idx s (mobiusLiveResidue k)) s := by
  constructor
  · exact arun_arr_frame idx (mobiusLiveResidue k) s (by rfl)
  · intro j hj
    exact arun_reg_frame idx j (mobiusLiveResidue k) s
      (residue_avoids_core k j hj)

/-- One combined body event has the same core projection as one core event. -/
theorem arun_combined_core (c : Cfg) (k idx : Nat) {s t : AState}
    (h : CoreAgree s t) :
    CoreAgree (arun idx s (c.coreBody ++ mobiusLiveResidue k))
      (arun idx t c.coreBody) := by
  rw [arun_append]
  exact (arun_residue_core_frame k idx (arun idx s c.coreBody)).trans
    (arun_coreBody_congr c idx h)

/-- The complete combined pure fold retains exactly the verified indexed
sieve trace in its core-facing projection. -/
theorem foldl_combined_core (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    CoreAgree
      ((List.range fuel).foldl
        (fun q idx => arun idx q (c.coreBody ++ mobiusLiveResidue k)) s)
      (indexedBodyRun 0 c fuel t) := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      change CoreAgree
        (arun n
          ((List.range n).foldl
            (fun q idx => arun idx q (c.coreBody ++ mobiusLiveResidue k)) s)
          (c.coreBody ++ mobiusLiveResidue k))
        (indexedBodyRun 0 c (n + 1) t)
      rw [indexedBodyRun_succ]
      simpa only [Nat.zero_add] using arun_combined_core c k n ih

private theorem liveInit_avoids_core (seed : MobLiveSeed) (j : Nat)
    (hj : CoreReg j = true) :
    (mobiusLiveInit seed).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 104 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj104
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj104⟩)
  simp [mobiusLiveInit, ArraySegSieve.seed, avoidsReg,
    rTLo, rTHi, rCeil, rCeilSq,
    rMViol]
  rcases h100 with h100 | h100 <;> omega

/-- The actual residue initializer changes only private residue registers. -/
theorem arun_liveInit_core_frame (seed : MobLiveSeed) (s : AState) :
    CoreAgree (arun 0 s (mobiusLiveInit seed)) s := by
  constructor
  · exact arun_arr_frame 0 (mobiusLiveInit seed) s (by rfl)
  · intro j hj
    exact arun_reg_frame 0 j (mobiusLiveInit seed) s
      (liveInit_avoids_core seed j hj)

/-- Total-state entry of the real combined Möbius program. -/
def combinedEntry (c : Cfg) (seed : MobLiveSeed) : AState :=
  arun 0 initialAState (c.coreInit ++ mobiusLiveInit seed)

/-- Every component of the real combined entry is a machine word.  In
particular, callers of the window-level residue theorem do not need to carry
word bounds as extra certificate fields: they follow from execution of the
compiled initializer itself. -/
theorem combinedEntry_word (c : Cfg) (seed : MobLiveSeed) :
    (∀ j, (combinedEntry c seed).regs j < M) ∧
      (∀ j, (combinedEntry c seed).arr j < M) := by
  apply arun_word 0 _ initialAState
  · intro j
    simp [initialAState, initialState, M]
  · intro j
    simp [initialAState, M]

/-- The five persistent residue fields installed by the real combined
initializer.  This exposes the exact modulo-normalized carry-in consumed by
the finite compiled trace. -/
theorem readRes_combinedEntry (c : Cfg) (seed : MobLiveSeed) :
    readRes (combinedEntry c seed) =
      { tLo := seed.tLo % M
        tHi := seed.tHi % M
        cel := seed.c % M
        celSq := seed.cSq % M
        viol := 0 } := by
  rw [combinedEntry, arun_append]
  simp [mobiusLiveInit, ArraySegSieve.seed, readRes, arun, astep,
    AState.writeReg, rTLo, rTHi, rCeil, rCeilSq, rMViol,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand]

/-- The standard compiled carry-in is the exact mathematical residue at
prefix zero.  The statement is independent of the arithmetic function,
because its finite prefix is empty. -/
theorem readRes_combinedEntry_start_inv (c : Cfg) (k : Nat)
    (mu : Nat → Int) (hk15 : k ≤ 15) :
    ResInv k mu 0 (readRes (combinedEntry c (mobLiveSeedStart k))) := by
  rw [readRes_combinedEntry]
  have hk64 : 2 ^ k < M := by
    simp only [M]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have h1 : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  simp only [mobLiveSeedStart, Nat.zero_mod, Nat.mod_eq_of_lt hk64, h1]
  constructor
  · exact M_pos
  · exact hk64
  ·
    have hp : 2 ^ 64 * 2 ^ k = 2 ^ (64 + k) :=
      (Nat.pow_add 2 64 k).symm
    simpa [Res.tLo, Res.tHi, M, accTrue] using
      congrArg (fun n : Nat => (n : Int)) hp
  · simp [accTrue]
  · simp [CeilInv]
  · rfl
  · decide

/-- Total-state changing-index trace of the combined program body. -/
def combinedRun (c : Cfg) (k fuel : Nat) (seed : MobLiveSeed) : AState :=
  (List.range fuel).foldl
    (fun q idx => arun idx q (c.coreBody ++ mobiusLiveResidue k))
    (combinedEntry c seed)

/-- The real combined initializer has the verified `coreEntry` as its exact
sieve-facing projection. -/
theorem combinedEntry_core (c : Cfg) (seed : MobLiveSeed) :
    CoreAgree (combinedEntry c seed) (coreEntry c) := by
  rw [combinedEntry, coreEntry, arun_append]
  exact arun_liveInit_core_frame seed (arun 0 initialAState c.coreInit)

/-- The complete combined trace retains the standalone indexed core trace. -/
theorem combinedRun_core (c : Cfg) (k fuel : Nat) (seed : MobLiveSeed) :
    CoreAgree (combinedRun c k fuel seed)
      (indexedBodyRun 0 c fuel (coreEntry c)) := by
  exact foldl_combined_core c k fuel (combinedEntry_core c seed)

set_option maxRecDepth 10000 in
/-- Production sieve postconditions transported onto the actual combined
core-plus-residue trace.  No residue arithmetic is assumed here: this theorem
only establishes that bolting on the literature computation cannot perturb
the verified sieve, table, or window schedule. -/
theorem combinedProductionCore_complete
    (c : Cfg) (k bootBound bootFuel laterFuel mainFuel delta : Nat)
    (seed : MobLiveSeed)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta) :
    let windows := bootFuel + 1 + (laterFuel + 1 + mainFuel)
    let full := combinedRun c k (windows * c.period) seed
    let ps := finalRootTable c bootBound bootFuel laterFuel
    CoreAgree full (indexedWindowRun 0 c windows (coreEntry c)) ∧
      (∀ j, j < c.segLen → machineCell c full j = ⟨0, 0⟩) ∧
      MachineTableRep c full ps ∧ full.regs rR = 0 ∧
      full.regs rW = mainBase c bootFuel laterFuel delta +
        mainFuel * c.segLen ∧
      full.regs rZero = 0 := by
  let windows := bootFuel + 1 + (laterFuel + 1 + mainFuel)
  let full := combinedRun c k (windows * c.period) seed
  let core := indexedWindowRun 0 c windows (coreEntry c)
  let ps := finalRootTable c bootBound bootFuel laterFuel
  have hagree : CoreAgree full core := by
    simpa only [full, core, indexedWindowRun] using
      combinedRun_core c k (windows * c.period) seed
  have hcore := indexedProductionCore_complete c bootBound bootFuel laterFuel
    mainFuel delta h
  change (∀ j, j < c.segLen → machineCell c core j = ⟨0, 0⟩) ∧
      MachineTableRep c core ps ∧ core.regs rR = 0 ∧
      core.regs rW = mainBase c bootFuel laterFuel delta +
        mainFuel * c.segLen ∧ core.regs rZero = 0 at hcore
  refine ⟨hagree, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hc := hcore.1 j hj
    unfold machineCell at hc ⊢
    rw [hagree.1]
    exact hc
  · exact
      { table := by
          rw [hagree.1]
          exact hcore.2.1.table
        cursor := by
          rw [hagree.2 rWrite (by rfl)]
          exact hcore.2.1.cursor
        guard := by
          rw [hagree.1]
          exact hcore.2.1.guard }
  · rw [hagree.2 rR (by rfl)]
    exact hcore.2.2.1
  · rw [hagree.2 rW (by rfl)]
    exact hcore.2.2.2.1
  · rw [hagree.2 rZero (by rfl)]
    exact hcore.2.2.2.2

end LeanCompCert.Ports.ArraySegMobiusResidueFrame
