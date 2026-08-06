import LeanCompCert.Ports.MertensCDEM
import LeanCompCert.Ports.CDEMAbelScan
import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.BlockDefined

/-!
# Compiled checker for the finite Möbius sawtooth head

The array is initialized with the already verified trial-division `muCode`
table.  One rolled rectangular loop covers `U = 6, ..., 11814` and
`n = 1, ..., 23630`.  It accumulates the positive and negative sides of
the fixed-point expression separately, so every live arithmetic operation
is unsigned and below `2^64`.
-/

namespace LeanCompCert.Ports.MoebiusSawtooth

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.MertensCDEM (muCode)
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB forall_wf_of_all)

def P : Nat := 1000000000
def Q : Nat := 200000000
def firstU : Nat := 6
def stopU : Nat := 11815
def width : Nat := 23630
def rounds : Nat := stopU - firstU
def arrayLen : Nat := width + 1
def loopCount : Nat := rounds * width
def trialRounds : Nat := 153

def tableCells : List (Nat × Nat) :=
  (List.range arrayLen).map fun n => (n, muCode n trialRounds)

/-- Store one table literal, using registers `28/29` as init scratch. -/
def storeLit (cell value : Nat) : List AInstr :=
  [ .scalar (.mov 28 (.lit cell)), .scalar (.mov 29 (.lit value)), .store 28 29 ]

def seedBody (n : Nat) : List AInstr :=
  (List.range n).foldl (fun acc k => storeLit k (muCode k trialRounds) ++ acc) []

theorem seedBody_zero : seedBody 0 = [] := rfl

theorem seedBody_succ (n : Nat) :
    seedBody (n + 1) = storeLit n (muCode n trialRounds) ++ seedBody n := by
  rw [seedBody, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rfl

def initBody : List AInstr := seedBody arrayLen

theorem initBody_eq : initBody = seedBody arrayLen := rfl

attribute [irreducible] initBody

/-! Registers: `0` violation, `7/8` the two nonnegative sides `A/B`.
All other registers are per-iteration scratch. -/
def regCount : Nat := 32

def bodyIndex : List AInstr :=
  [ .scalar (.binop 1 .udiv .idx (.lit width))       -- q
  , .scalar (.binop 2 .urem .idx (.lit width))
  , .scalar (.binop 2 .add (.reg 2) (.lit 1))        -- n
  , .scalar (.binop 3 .add (.reg 1) (.lit firstU))   -- U
  , .scalar (.binop 4 .mul (.reg 3) (.lit 2)) ]      -- 2U

def bodyReset : List AInstr :=
  [ .scalar (.binop 5 .eq (.reg 2) (.lit 1))
  , .scalar (.binop 6 .ne (.reg 2) (.lit 1))
  , .scalar (.binop 7 .mul (.reg 7) (.reg 6))        -- reset A
  , .scalar (.binop 8 .mul (.reg 8) (.reg 6))        -- reset B
  , .scalar (.binop 9 .mul (.reg 5) (.lit P))
  , .scalar (.binop 8 .add (.reg 8) (.reg 9)) ]      -- constant -P

def bodyLoadFlags : List AInstr :=
  [ .load 10 2                                       -- mu code
  , .scalar (.binop 11 .eq (.reg 10) (.lit 1))       -- positive
  , .scalar (.binop 12 .eq (.reg 10) (.lit 2))       -- negative
  , .scalar (.binop 13 .le (.reg 2) (.reg 3))        -- n <= U
  , .scalar (.binop 14 .le (.reg 2) (.reg 4))        -- n <= 2U
  , .scalar (.binop 15 .eq (.reg 2) (.reg 4)) ]      -- final row

def bodyTerm : List AInstr :=
  [ .scalar (.binop 17 .mul (.reg 3) (.lit (2 * P)))
  , .scalar (.binop 16 .udiv (.reg 17) (.reg 2)) ]   -- floor(2PU/n)

def bodyDecode : List AInstr :=
  bodyIndex ++ (bodyReset ++ (bodyLoadFlags ++ bodyTerm))

/-- Add `gate1 * gate2 * x` to `dest` and merge a u64-wrap bit into `bad`. -/
def bodyGuardedAdd (dest gate1 gate2 : Nat) (x : Operand) : List AInstr :=
  [ .scalar (.binop 18 .mul (.reg gate1) (.reg gate2))
  , .scalar (.binop 18 .mul (.reg 18) x)
  , .scalar (.binop dest .add (.reg dest) (.reg 18))
  , .scalar (.binop 22 .lt (.reg dest) (.reg 18))
  , .scalar (.binop 0 .bor (.reg 0) (.reg 22)) ]

def bodyBfix : List AInstr :=
  bodyGuardedAdd 7 13 11 (.reg 16) ++
    bodyGuardedAdd 8 13 12 (.reg 16)

def bodyM2Prep : List AInstr :=
  [ .scalar (.mov 24 (.reg 13))
  , .scalar (.mov 13 (.reg 14))
  , .scalar (.mov 16 (.lit P)) ]

def bodyM2 : List AInstr := bodyM2Prep ++ bodyBfix

def bodyMUPrep : List AInstr :=
  [ .scalar (.mov 13 (.reg 24))
  , .scalar (.mov 23 (.reg 11))
  , .scalar (.mov 11 (.reg 12))
  , .scalar (.mov 12 (.reg 23)) ]

def bodyMU : List AInstr := bodyMUPrep ++ bodyBfix

def bodyLimit : List AInstr :=
  [ .scalar (.binop 19 .mul (.reg 3) (.lit Q))
  , .scalar (.binop 19 .sub (.reg 19) (.reg 3)) ]

def bodyWrapB : List AInstr :=
  [ .scalar (.binop 20 .add (.reg 8) (.reg 19))
  , .scalar (.binop 22 .lt (.reg 20) (.reg 19))
  , .scalar (.binop 0 .bor (.reg 0) (.reg 22)) ]

def bodyFailA : List AInstr :=
  [ .scalar (.binop 21 .gt (.reg 7) (.reg 20))
  , .scalar (.binop 21 .mul (.reg 21) (.reg 15))
  , .scalar (.binop 0 .bor (.reg 0) (.reg 21)) ]

def bodyWrapA : List AInstr :=
  [ .scalar (.binop 20 .add (.reg 7) (.reg 19))
  , .scalar (.binop 22 .lt (.reg 20) (.reg 19))
  , .scalar (.binop 0 .bor (.reg 0) (.reg 22)) ]

def bodyFailB : List AInstr :=
  [ .scalar (.binop 21 .gt (.reg 8) (.reg 20))
  , .scalar (.binop 21 .mul (.reg 21) (.reg 15))
  , .scalar (.binop 0 .bor (.reg 0) (.reg 21)) ]

def bodyCheck : List AInstr :=
  bodyLimit ++ (bodyWrapB ++ (bodyFailA ++ (bodyWrapA ++ bodyFailB)))

def body : List AInstr :=
  bodyDecode ++ (bodyBfix ++ (bodyM2 ++ (bodyMU ++ bodyCheck)))

def program : AProgram := {
  regCount := regCount
  arrayLen := arrayLen
  loopCount := loopCount
  init := initBody
  body := body
  epilogue := []
  output := 0
}

theorem program_arrayLen : program.arrayLen = arrayLen := rfl
theorem program_loopCount : program.loopCount = loopCount := rfl
theorem program_body : program.body = body := rfl
theorem program_epilogue : program.epilogue = [] := rfl
theorem program_output : program.output = 0 := rfl

theorem seedBody_all (n : Nat) : (seedBody n).all (ainstrWFB regCount) = true := by
  induction n with
  | zero => rw [seedBody_zero]; rfl
  | succ n ih =>
      rw [seedBody_succ, List.all_append, ih]
      rfl

theorem initBody_all : initBody.all (ainstrWFB regCount) = true := by
  let f := fun l : List AInstr => l.all (ainstrWFB regCount) = true
  exact Eq.mp (congrArg f initBody_eq).symm (seedBody_all _)

set_option maxRecDepth 1000000 in
theorem body_all : body.all (ainstrWFB regCount) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem program_wf : program.WF :=
  ⟨by decide, forall_wf_of_all initBody_all, forall_wf_of_all body_all,
    fun _ h => nomatch h⟩

theorem program_compiled (base : Int) (hBase : BaseOk program.arrayLen base)
    (n : Nat) (hDenote : program.denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence (program.initialMCC base) program.compile)
        (fun m : Verified.MemFragment.MCCState => m.env ⟨program.output + 1⟩)
      = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ program_wf base hBase n hDenote

/-! ## Denotation: initialization -/

theorem storeLit_defined (len k cell value : Nat) (s : AState)
    (hc : cell < len) (hcM : cell < M) :
    AllDefined len k s (storeLit cell value) := by
  simp [storeLit, AllDefined, ADefined, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, hc, Nat.mod_eq_of_lt hcM]

theorem arun_storeLit_arr (k cell value i : Nat) (s : AState) (hcM : cell < M) :
    (arun k s (storeLit cell value)).arr i =
      if i = cell then value % M else s.arr i := by
  simp [storeLit, arun, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, AState.writeArr,
    Nat.mod_eq_of_lt hcM]

theorem arun_storeLit_reg (k cell value j : Nat) (s : AState)
    (h28 : j ≠ 28) (h29 : j ≠ 29) :
    (arun k s (storeLit cell value)).regs j = s.regs j := by
  simp [storeLit, arun, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, AState.writeArr, h28, h29]

theorem arun_storeLit_reg28 (k cell value : Nat) (s : AState) (hcM : cell < M) :
    (arun k s (storeLit cell value)).regs 28 = cell := by
  simp [storeLit, arun, astep, sdest, sval, denoteOperand, AState.writeReg,
    AState.writeArr, Nat.mod_eq_of_lt hcM]

theorem arun_storeLit_reg29 (k cell value : Nat) (s : AState) :
    (arun k s (storeLit cell value)).regs 29 = value % M := by
  simp [storeLit, arun, astep, sdest, sval, denoteOperand, AState.writeReg,
    AState.writeArr]

theorem muCode_lt_M (n r : Nat) : muCode n r < M := by
  simp only [muCode]
  split
  · decide
  · split <;> decide

set_option maxRecDepth 1000000 in
theorem seedBody_defined (n : Nat) (hn : n ≤ arrayLen) (s : AState) :
    AllDefined arrayLen 0 s (seedBody n) := by
  induction n generalizing s with
  | zero => rw [seedBody_zero]; trivial
  | succ n ih =>
      rw [seedBody_succ, AllDefined_append]
      exact ⟨storeLit_defined arrayLen 0 n (muCode n trialRounds) s (by omega)
          (Nat.lt_trans (by omega) (by decide : arrayLen < M)),
        ih (by omega) (arun 0 s (storeLit n (muCode n trialRounds)))⟩

set_option maxRecDepth 1000000 in
theorem seedBody_arr_ge_state (n i : Nat) (hi : n ≤ i) (hn : n ≤ arrayLen)
    (s : AState) : (arun 0 s (seedBody n)).arr i = s.arr i := by
  induction n generalizing s with
  | zero => rw [seedBody_zero]; rfl
  | succ n ih =>
      rw [seedBody_succ, arun_append, ih (by omega) (by omega)]
      rw [arun_storeLit_arr 0 n (muCode n trialRounds) i s
        (Nat.lt_trans (by omega) (by decide : arrayLen < M)), if_neg (by omega)]

set_option maxRecDepth 1000000 in
theorem seedBody_arr_lt_state (n i : Nat) (hi : i < n) (hn : n ≤ arrayLen)
    (s : AState) : (arun 0 s (seedBody n)).arr i = muCode i trialRounds := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
      rw [seedBody_succ, arun_append]
      by_cases h : i = n
      · subst i
        rw [seedBody_arr_ge_state n n (Nat.le_refl n) (by omega)]
        rw [arun_storeLit_arr 0 n (muCode n trialRounds) n s
          (Nat.lt_trans (by omega) (by decide : arrayLen < M)), if_pos rfl,
          Nat.mod_eq_of_lt (muCode_lt_M n trialRounds)]
      · exact ih (by omega) (by omega)
          (arun 0 s (storeLit n (muCode n trialRounds)))

set_option maxRecDepth 1000000 in
theorem seedBody_arr_lt (n i : Nat) (hi : i < n) (hn : n ≤ arrayLen) :
    (arun 0 initialAState (seedBody n)).arr i = muCode i trialRounds :=
  seedBody_arr_lt_state n i hi hn initialAState

set_option maxRecDepth 1000000 in
theorem seedBody_arr_ge (n i : Nat) (hi : n ≤ i) (hn : n ≤ arrayLen) :
    (arun 0 initialAState (seedBody n)).arr i = 0 := by
  rw [seedBody_arr_ge_state n i hi hn]
  rfl

set_option maxRecDepth 1000000 in
theorem seedBody_arr_full (i : Nat) (hi : i < arrayLen) :
    (arun 0 initialAState (seedBody arrayLen)).arr i = muCode i trialRounds :=
  seedBody_arr_lt arrayLen i hi (Nat.le_refl arrayLen)

set_option maxRecDepth 1000000 in
theorem seedBody_reg_state (n j : Nat) (h28 : j ≠ 28) (h29 : j ≠ 29)
    (s : AState) : (arun 0 s (seedBody n)).regs j = s.regs j := by
  induction n generalizing s with
  | zero => rw [seedBody_zero]; rfl
  | succ n ih =>
      rw [seedBody_succ, arun_append, ih,
        arun_storeLit_reg 0 n (muCode n trialRounds) j s h28 h29]

theorem seedBody_reg (n j : Nat) (h28 : j ≠ 28) (h29 : j ≠ 29) :
    (arun 0 initialAState (seedBody n)).regs j = 0 := by
  rw [seedBody_reg_state n j h28 h29 initialAState]
  rfl

theorem seedBody_reg28_pos : ∀ (n : Nat), 0 < n → ∀ s : AState,
    (arun 0 s (seedBody n)).regs 28 = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      intro s
      cases n with
      | zero =>
          rw [seedBody_succ, arun_append, seedBody_zero, arun_nil,
            arun_storeLit_reg28 0 0 (muCode 0 trialRounds) s (by decide)]
      | succ n =>
          rw [seedBody_succ, arun_append]
          exact ih (by omega) _

theorem seedBody_reg29_pos : ∀ (n : Nat), 0 < n → ∀ s : AState,
    (arun 0 s (seedBody n)).regs 29 = muCode 0 trialRounds := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      intro s
      cases n with
      | zero =>
          rw [seedBody_succ, arun_append, seedBody_zero, arun_nil, arun_storeLit_reg29,
            Nat.mod_eq_of_lt (muCode_lt_M 0 trialRounds)]
      | succ n =>
          rw [seedBody_succ, arun_append]
          exact ih (by omega) _

/-- Compact mathematical description of the state after the literal table
initializer.  Keeping this state explicit prevents downstream elaboration
from unfolding all 70,893 initialization instructions. -/
def entry : AState :=
  { regs := fun j =>
      if j = 28 then 0
      else if j = 29 then muCode 0 trialRounds else 0
  , arr := fun i => if i < arrayLen then muCode i trialRounds else 0 }

theorem astate_eq_of {s t : AState} (hregs : s.regs = t.regs)
    (harr : s.arr = t.arr) : s = t := by
  cases s
  cases t
  simp_all

set_option maxRecDepth 1000000 in
theorem seedBody_full_eq_entry :
    arun 0 initialAState (seedBody arrayLen) = entry := by
  apply astate_eq_of
  · funext j
    by_cases h28 : j = 28
    · subst j
      simp only [entry, if_pos]
      exact seedBody_reg28_pos arrayLen (by decide) initialAState
    · rw [show entry.regs j = if j = 29 then muCode 0 trialRounds else 0 by
          simp [entry, h28]]
      by_cases h29 : j = 29
      · subst j
        rw [if_pos rfl]
        exact seedBody_reg29_pos arrayLen (by decide) initialAState
      · rw [if_neg h29]
        exact seedBody_reg arrayLen j h28 h29
  · funext i
    by_cases hi : i < arrayLen
    · rw [show entry.arr i = muCode i trialRounds by simp [entry, hi]]
      exact seedBody_arr_lt arrayLen i hi (Nat.le_refl arrayLen)
    · rw [show entry.arr i = 0 by simp [entry, hi]]
      exact seedBody_arr_ge arrayLen i (by omega) (Nat.le_refl arrayLen)

set_option maxRecDepth 1000000 in
theorem init_denote :
    denoteAInstrs arrayLen 0 initialAState initBody = some entry := by
  have hseed : denoteAInstrs arrayLen 0 initialAState (seedBody arrayLen) =
      some entry := by
    rw [denoteAInstrs_eq_arun arrayLen 0 _ initialAState
    (seedBody_defined arrayLen (Nat.le_refl arrayLen) initialAState),
    seedBody_full_eq_entry]
  let f := fun l : List AInstr => denoteAInstrs arrayLen 0 initialAState l = some entry
  exact Eq.mp (congrArg f initBody_eq).symm hseed

set_option maxRecDepth 1000000 in
theorem seedBody_reg_full (j : Nat) (h28 : j ≠ 28) (h29 : j ≠ 29) :
    (arun 0 initialAState (seedBody arrayLen)).regs j = 0 :=
  seedBody_reg arrayLen j h28 h29

end LeanCompCert.Ports.MoebiusSawtooth
