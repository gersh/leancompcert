/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCompCert.Verified.ArrayPipeline
import LeanCompCert.Verified.ArrayAuditFromArray
import LeanCompCert.Verified.InstrBlock

/-!
# External dense product-plane shard scanner

This read-only rolled program consumes the exact final array of a dense marker.
It checks one half-open shard `[iLo,iHi)` of plane zero and sets a sticky bit
when `arr[i] > windowBase + i`.  It never executes the marking computation.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.R2DenseProductPlaneScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayAudit

structure Cfg where
  arrayLen : Nat
  segLen : Nat
  windowBase : Nat
  iLo : Nat
  iHi : Nat
  deriving Repr

def Cfg.count (c : Cfg) : Nat := c.iHi - c.iLo

abbrev rBad : Nat := 0
abbrev rAddr : Nat := 1
abbrev rProd : Nat := 2
abbrev rCandidate : Nat := 3
abbrev rThisBad : Nat := 4
abbrev regCount : Nat := 5

def body (c : Cfg) : List AInstr :=
  [ .scalar (.binop rAddr .add (.lit c.iLo) .idx)
  , .load rProd rAddr
  , .scalar (.binop rCandidate .add (.lit c.windowBase) (.reg rAddr))
  , .scalar (.binop rThisBad .gt (.reg rProd) (.reg rCandidate))
  , .scalar (.binop rBad .bor (.reg rBad) (.reg rThisBad)) ]

def program (c : Cfg) : AProgram :=
  { regCount := regCount
    arrayLen := c.arrayLen
    loopCount := c.count
    init := []
    body := body c
    epilogue := []
    output := rBad }

theorem program_wf (c : Cfg) : (program c).WF := by
  simp [AProgram.WF, program, body, AInstr.WF, Instr.WF, Operand.WF,
    regCount, rBad, rAddr, rProd, rCandidate, rThisBad]

/-- Static public bounds required for exact addresses and additions. -/
structure Ready (c : Cfg) (arr : Nat → Nat) : Prop where
  shard_order : c.iLo ≤ c.iHi
  shard_live : c.iHi ≤ c.segLen
  plane_allocated : c.segLen ≤ c.arrayLen
  array_pos : 0 < c.arrayLen
  array_word : c.arrayLen < M
  candidate_word : c.windowBase + c.segLen < M
  words : ∀ i, arr i < M

def ShardChecked (c : Cfg) (arr : Nat → Nat) : Prop :=
  ∀ i, c.iLo ≤ i → i < c.iHi → arr i ≤ c.windowBase + i

def symbolicFinal (c : Cfg) (arr : Nat → Nat) : AState :=
  arun 0 ((List.range c.count).foldl
    (fun s k => arun k s (body c))
    (arun 0 (initialAStateWithArray arr) (program c).init))
    (program c).epilogue

def MachineAccepts (c : Cfg) (arr : Nat → Nat) : Prop :=
  (symbolicFinal c arr).regs rBad = 0

theorem runFromArray_eq_symbolicFinal (c : Cfg) (arr : Nat → Nat)
    (out : AState) (hRun : (program c).runFromArray arr = some out) :
    out = symbolicFinal c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some (program c) arr out hRun
  simpa [program, symbolicFinal] using h

/-- The scanner is read-only, making it suitable for an exact shared-memory
handoff from the dense producer and for subsequent independent scanners. -/
theorem body_arr (c : Cfg) (k : Nat) (s : AState) :
    (arun k s (body c)).arr = s.arr := by
  simp [body, arun, astep, AState.writeReg, sdest, sval, denoteOperand]

theorem body_bad (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hsarr : s.arr = arr) (hk : k < c.count)
    (hready : Ready c arr) :
    (arun k s (body c)).regs rBad =
      (s.regs rBad |||
        (if arr (c.iLo + k) > c.windowBase + (c.iLo + k) then 1 else 0)) % M := by
  have hkHi : c.iLo + k < c.iHi := by
    simp only [Cfg.count] at hk
    omega
  have hiLive : c.iLo + k < c.segLen :=
    Nat.lt_of_lt_of_le hkHi hready.shard_live
  have haddr : c.iLo + k < c.arrayLen :=
    Nat.lt_of_lt_of_le hiLive hready.plane_allocated
  have hkM : k < M := by
    have := hready.array_word
    omega
  have hloM : c.iLo < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_trans haddr hready.array_word)
  have haddrM : c.iLo + k < M :=
    Nat.lt_trans haddr hready.array_word
  have hbaseM : c.windowBase < M := by
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hready.candidate_word
  have hcandM : c.windowBase + (c.iLo + k) < M := by
    exact Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hiLive c.windowBase)
      (Nat.le_of_lt hready.candidate_word)
  simp [body, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
    denoteOp, hsarr, Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hloM,
    Nat.mod_eq_of_lt haddrM, Nat.mod_eq_of_lt hbaseM,
    Nat.mod_eq_of_lt hcandM, rBad, rAddr, rProd, rCandidate, rThisBad]

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

private theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a ≤ a ||| b := Nat.left_le_or
  have hb : b ≤ a ||| b := Nat.right_le_or
  omega

theorem fold_zero_sound (c : Cfg) (arr : Nat → Nat) (hready : Ready c arr) :
    ∀ (xs : List Nat) (s : AState), s.arr = arr → s.regs rBad < M →
      (∀ k, k ∈ xs → k < c.count) →
      ((xs.foldl (fun q k => arun k q (body c)) s).regs rBad = 0) →
      s.regs rBad = 0 ∧
        ∀ k, k ∈ xs → arr (c.iLo + k) ≤ c.windowBase + (c.iLo + k) := by
  intro xs
  induction xs with
  | nil =>
      intro s hsarr hbad hall hz
      exact ⟨hz, by simp⟩
  | cons k ks ih =>
      intro s hsarr hbad hall hz
      let s' := arun k s (body c)
      have hk : k < c.count := hall k (by simp)
      have hs'arr : s'.arr = arr := (body_arr c k s).trans hsarr
      have hs'bad : s'.regs rBad < M := by
        rw [body_bad c arr k s hsarr hk hready]
        exact Nat.mod_lt _ (by simp [M])
      have htail :
          (ks.foldl (fun q j => arun j q (body c)) s').regs rBad = 0 := by
        simpa [s'] using hz
      have hi := ih s' hs'arr hs'bad (fun j hj => hall j (by simp [hj])) htail
      have hstep := body_bad c arr k s hsarr hk hready
      have hbitM : (if arr (c.iLo + k) > c.windowBase + (c.iLo + k)
          then 1 else 0) < M := by split <;> simp [M]
      have horM := or_lt_M hbad hbitM
      rw [Nat.mod_eq_of_lt horM] at hstep
      have hor0 : s.regs rBad |||
          (if arr (c.iLo + k) > c.windowBase + (c.iLo + k)
            then 1 else 0) = 0 := hstep.symm.trans hi.1
      have hzparts := or_eq_zero hor0
      refine ⟨hzparts.1, ?_⟩
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simpa using hzparts.2
      · exact hi.2 j hj

theorem machineAccepts_implies_shardChecked
    (c : Cfg) (arr : Nat → Nat) (hready : Ready c arr)
    (haccept : MachineAccepts c arr) : ShardChecked c arr := by
  have hfold := fold_zero_sound c arr hready (List.range c.count)
    (initialAStateWithArray arr) rfl (by change 0 < M; simp [M])
    (by simp) (by simpa [MachineAccepts, symbolicFinal, program, arun] using haccept)
  intro i hlo hhi
  have hk : i - c.iLo < c.count := by simp [Cfg.count]; omega
  have heq : c.iLo + (i - c.iLo) = i := by omega
  simpa [heq] using hfold.2 (i - c.iLo) (by simp [hk])

def RolledResult (p : AProgram) (base : Int) (mem : Mem)
    (value : Int) : Prop :=
  Option.bind
    (evalMCCSequence
      (p.counterAugment.initialMCCWithMem base mem) p.rolledCompile)
    (fun out : MCCState => out.env ⟨p.output + 1⟩) = some value

def AuditRolledZero (p : AProgram) (base : Int) (mem : Mem) : Prop :=
  RolledResult (auditProgram p) base mem 0

/-- Fail-safe audit and ordinary signed result for the same physical memory
recover the exact source shard proposition. -/
theorem shardChecked_of_rolled_audit_and_result
    (c : Cfg) (arr : Nat → Nat) (hready : Ready c arr)
    (base : Int) (hBase : BaseOk c.arrayLen base) (mem : Mem)
    (cells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (audit : AuditRolledZero (program c) base mem)
    (result : RolledResult (program c) base mem 0) :
    ShardChecked c arr := by
  obtain ⟨out, hRun⟩ := source_runFromArray_of_audit_rolled_zero
    (program c) (program_wf c) base hBase arr mem cells hready.words
    (by simpa [program] using hready.array_pos)
    hready.array_word audit
  have hzero : out.regs (program c).output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      (program c) (program_wf c) base hBase arr mem cells
      (fun k _ => hready.words k) out hRun 0 result
  have heq := runFromArray_eq_symbolicFinal c arr out hRun
  have haccept : MachineAccepts c arr := by
    rw [heq] at hzero
    simpa [MachineAccepts, program] using hzero
  exact machineAccepts_implies_shardChecked c arr hready haccept


end LeanCompCert.Ports.R2DenseProductPlaneScanner
