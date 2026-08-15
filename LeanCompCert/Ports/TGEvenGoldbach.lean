import LeanCompCert.Verified.ArrayPipeline
import LeanCompCert.Verified.ArrayAuditFromArray
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.PackedSieve

/-!
# A compiled finite even-Goldbach witness checker

Oliveira e Silva--Herzog--Pardi verify consecutive even integers in bounded
intervals. Their producer finds a prime pair for every even integer using a
segmented sieve and a small-prime scan. This module gives the independent,
fail-closed consumer: a caller supplies one `(p,q)` witness and two compiled
primality bits per even integer, and a constant-size rolled array program
checks all rows.

The proof is symbolic in the interval length. Lean neither enumerates the
interval nor tests a candidate for primality. A preceding compiled sieve (or
compiled certificate checker) supplies `PrimeRowsCorrect`; this checker only
does four array loads and exact `u64` arithmetic per row.
-/

namespace LeanCompCert.Ports.TGEvenGoldbach

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.PackedSieve

/-- Four equal-length planes: `p`, `q`, the primality bit for `p`, and the
primality bit for `q`. Row `k` represents `evenLo + 2*k`. -/
structure Cfg where
  evenLo : Nat
  count : Nat
  deriving Repr

def Cfg.pBase (_ : Cfg) : Nat := 0
def Cfg.qBase (c : Cfg) : Nat := c.count
def Cfg.pBitBase (c : Cfg) : Nat := 2 * c.count
def Cfg.qBitBase (c : Cfg) : Nat := 3 * c.count
def Cfg.arrayLen (c : Cfg) : Nat := 4 * c.count
def Cfg.evenAt (c : Cfg) (k : Nat) : Nat := c.evenLo + 2 * k

abbrev rViol : Nat := 0
abbrev rAddr : Nat := 1
abbrev rP : Nat := 2
abbrev rQ : Nat := 3
abbrev rPBit : Nat := 4
abbrev rQBit : Nat := 5
abbrev rTarget : Nat := 6
abbrev rPLe : Nat := 7
abbrev rDiff : Nat := 8
abbrev rQEq : Nat := 9
abbrev rPBitGood : Nat := 10
abbrev rQBitGood : Nat := 11
abbrev rGood : Nat := 12
abbrev rBad : Nat := 13
abbrev regCount : Nat := 14

/-- One branch-free row check. The output flag is monotone and remains a bit. -/
def body (c : Cfg) : List AInstr :=
  [ .scalar (.mov rAddr .idx)
  , .load rP rAddr
  , .scalar (.binop rAddr .add (.lit c.qBase) .idx)
  , .load rQ rAddr
  , .scalar (.binop rAddr .add (.lit c.pBitBase) .idx)
  , .load rPBit rAddr
  , .scalar (.binop rAddr .add (.lit c.qBitBase) .idx)
  , .load rQBit rAddr
  , .scalar (.binop rTarget .mul (.lit 2) .idx)
  , .scalar (.binop rTarget .add (.lit c.evenLo) (.reg rTarget))
  , .scalar (.binop rPLe .le (.reg rP) (.reg rTarget))
  , .scalar (.binop rDiff .sub (.reg rTarget) (.reg rP))
  , .scalar (.binop rQEq .eq (.reg rQ) (.reg rDiff))
  , .scalar (.binop rPBitGood .eq (.reg rPBit) (.lit 1))
  , .scalar (.binop rQBitGood .eq (.reg rQBit) (.lit 1))
  , .scalar (.binop rGood .mul (.reg rPLe) (.reg rQEq))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rPBitGood))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rQBitGood))
  , .scalar (.binop rBad .eq (.reg rGood) (.lit 0))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.count
  init := []
  body := body c
  epilogue := []
  output := rViol
}

set_option maxRecDepth 40000 in
theorem program_wf (c : Cfg) : (program c).WF := by
  simp [AProgram.WF, program, body, AInstr.WF, Instr.WF, Operand.WF,
    regCount, rViol, rAddr, rP, rQ, rPBit, rQBit, rTarget, rPLe, rDiff,
    rQEq, rPBitGood, rQBitGood, rGood, rBad]

/-- Exact source predicate checked in row `k`. -/
def RowGood (c : Cfg) (arr : Nat → Nat) (k : Nat) : Prop :=
  let p := arr (c.pBase + k)
  let q := arr (c.qBase + k)
  p ≤ c.evenAt k ∧ q = c.evenAt k - p ∧
    arr (c.pBitBase + k) = 1 ∧ arr (c.qBitBase + k) = 1

instance (c : Cfg) (arr : Nat → Nat) (k : Nat) :
    Decidable (RowGood c arr k) := by
  unfold RowGood
  infer_instance

/-- Word-room conditions, independent of the number of represented rows. -/
def Ready (c : Cfg) (arr : Nat → Nat) : Prop :=
  c.arrayLen < M ∧ c.evenLo + 2 * c.count < M ∧
    ∀ i, i < c.arrayLen → arr i < M

set_option maxRecDepth 40000 in
theorem body_arr (c : Cfg) (k : Nat) (s : AState) :
    (arun k s (body c)).arr = s.arr := by
  simp [body, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
    denoteOp]

set_option maxRecDepth 40000 in
theorem body_viol (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hready : Ready c arr) (hk : k < c.count) (hsarr : s.arr = arr)
    (hsbit : s.regs rViol ≤ 1) :
    (arun k s (body c)).regs rViol =
      s.regs rViol ||| (if RowGood c arr k then 0 else 1) := by
  rcases hready with ⟨harray, heven, _hwords⟩
  have harray' : 4 * c.count < M := by
    simpa only [Cfg.arrayLen] using harray
  have hkM : k < M := by omega
  have hcountM : c.count < M := by
    omega
  have h2countM : 2 * c.count < M := by
    omega
  have h3countM : 3 * c.count < M := by
    omega
  have hqAddrM : c.count + k < M := by omega
  have hpBitAddrM : 2 * c.count + k < M := by omega
  have hqBitAddrM : 3 * c.count + k < M := by omega
  have h2M : 2 < M := by decide
  have h2kM : 2 * k < M := by omega
  have hevenLoM : c.evenLo < M := by omega
  have htargetM : c.evenLo + 2 * k < M := by omega
  subst hsarr
  simp only [body, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, Nat.reduceEqDiff, if_false,
    if_true, Option.getD_some, rViol, rAddr, rP, rQ, rPBit, rQBit, rTarget,
    rPLe, rDiff, rQEq, rPBitGood, rQBitGood, rGood, rBad,
    Cfg.qBase, Cfg.pBitBase, Cfg.qBitBase,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hcountM,
    Nat.mod_eq_of_lt h2countM, Nat.mod_eq_of_lt h3countM,
    Nat.mod_eq_of_lt hqAddrM, Nat.mod_eq_of_lt hpBitAddrM,
    Nat.mod_eq_of_lt hqBitAddrM, Nat.mod_eq_of_lt h2M,
    Nat.mod_eq_of_lt h2kM, Nat.mod_eq_of_lt hevenLoM,
    Nat.mod_eq_of_lt htargetM]
  by_cases hpLe : s.arr k ≤ c.evenLo + 2 * k
  · have hsub : (c.evenLo + 2 * k + (M - s.arr k)) % M =
        c.evenLo + 2 * k - s.arr k := by
      have heq : c.evenLo + 2 * k + (M - s.arr k) =
          M + (c.evenLo + 2 * k - s.arr k) := by omega
      rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    by_cases hqEq : s.arr (c.count + k) = c.evenLo + 2 * k - s.arr k
    · by_cases hpBit : s.arr (2 * c.count + k) = 1
      · by_cases hqBit : s.arr (3 * c.count + k) = 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
            simp [RowGood, Cfg.pBase, Cfg.qBase, Cfg.pBitBase,
              Cfg.qBitBase, Cfg.evenAt, hpLe, hqEq, hpBit, hqBit, hs, M]
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
            simp [RowGood, Cfg.pBase, Cfg.qBase, Cfg.pBitBase,
              Cfg.qBitBase, Cfg.evenAt, hpLe, hqEq, hpBit, hqBit, hs, M]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
          simp [RowGood, Cfg.pBase, Cfg.qBase, Cfg.pBitBase,
            Cfg.qBitBase, Cfg.evenAt, hpLe, hqEq, hpBit, hs, M]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
        simp [RowGood, Cfg.pBase, Cfg.qBase, Cfg.pBitBase,
          Cfg.qBitBase, Cfg.evenAt, hpLe, hqEq, hs, M]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
      simp [RowGood, Cfg.pBase, Cfg.qBase, Cfg.pBitBase, Cfg.qBitBase,
        Cfg.evenAt, hpLe, hs, M]

theorem body_viol_le_one (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hready : Ready c arr) (hk : k < c.count) (hsarr : s.arr = arr)
    (hsbit : s.regs rViol ≤ 1) :
    (arun k s (body c)).regs rViol ≤ 1 := by
  rw [body_viol c arr k s hready hk hsarr hsbit]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
    by_cases hgood : RowGood c arr k <;> simp [hs, hgood]

/-- Total symbolic machine fold. -/
def checkedState (c : Cfg) (arr : Nat → Nat) : AState :=
  (List.range c.count).foldl (fun s k => arun k s (body c))
    (initialAStateWithArray arr)

private theorem fold_zero_iff (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) (rows : List Nat)
    (hmem : ∀ k ∈ rows, k < c.count) (s : AState) (hsarr : s.arr = arr)
    (hsbit : s.regs rViol ≤ 1) :
    (rows.foldl (fun t k => arun k t (body c)) s).regs rViol = 0 ↔
      s.regs rViol = 0 ∧ ∀ k ∈ rows, RowGood c arr k := by
  induction rows generalizing s with
  | nil => simp
  | cons k rest ih =>
      rw [List.foldl_cons, ih (fun j hj => hmem j (by simp [hj]))
        (arun k s (body c)) (by rw [body_arr, hsarr])
        (body_viol_le_one c arr k s hready (hmem k (by simp)) hsarr hsbit)]
      rw [body_viol c arr k s hready (hmem k (by simp)) hsarr hsbit]
      constructor
      · rintro ⟨hz, hrest⟩
        have hleft : s.regs rViol = 0 := by
          have hle : s.regs rViol ≤ s.regs rViol |||
              (if RowGood c arr k then 0 else 1) := Nat.left_le_or
          omega
        have hgood : RowGood c arr k := by
          by_cases h : RowGood c arr k
          · exact h
          · have hle : 1 ≤ s.regs rViol ||| 1 := Nat.right_le_or
            simp [h] at hz
            omega
        exact ⟨hleft, fun j hj => by
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hgood
          · exact hrest j hj⟩
      · rintro ⟨hszero, hall⟩
        refine ⟨?_, fun j hj => hall j (List.mem_cons_of_mem _ hj)⟩
        simp [hszero, hall k (List.mem_cons_self ..)]

/-- A zero final flag is equivalent to every row being a valid witness. -/
theorem checkedState_zero_iff (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) :
    (checkedState c arr).regs rViol = 0 ↔
      ∀ k, k < c.count → RowGood c arr k := by
  unfold checkedState
  rw [fold_zero_iff c arr hready (List.range c.count)
    (fun k hk => List.mem_range.mp hk) (initialAStateWithArray arr) rfl
    (by simp [initialAStateWithArray, initialState, rViol])]
  constructor
  · rintro ⟨_, hall⟩ k hk
    exact hall k (List.mem_range.mpr hk)
  · intro hall
    exact ⟨rfl, fun k hk => hall k (List.mem_range.mp hk)⟩

/-- A successful source run is the symbolic checked state. -/
theorem run_eq_checkedState (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hRun : (program c).runFromArray arr = some out) :
    out = checkedState c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some (program c) arr out hRun
  simpa [program, checkedState, arun_nil] using h

/-- The two bit planes have the exact primality meaning supplied by preceding
compiled sieve/certificate stages. -/
def PrimeRowsCorrect (c : Cfg) (arr : Nat → Nat) : Prop :=
  ∀ k, k < c.count →
    (arr (c.pBitBase + k) = 1 ↔ IsPrime (arr (c.pBase + k))) ∧
    (arr (c.qBitBase + k) = 1 ↔ IsPrime (arr (c.qBase + k)))

/-- Paper-facing result for the represented consecutive even integers. -/
def Covers (c : Cfg) : Prop :=
  ∀ k, k < c.count →
    ∃ p q, IsPrime p ∧ IsPrime q ∧ p + q = c.evenAt k

/-- A successful compiled witness scan plus compiled primality-bit semantics
proves every represented even integer has a prime-pair decomposition. -/
theorem covers_of_compiled_run (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hready : Ready c arr) (hprime : PrimeRowsCorrect c arr)
    (hRun : (program c).runFromArray arr = some out)
    (hzero : out.regs rViol = 0) : Covers c := by
  have hout := run_eq_checkedState c arr out hRun
  have hall := (checkedState_zero_iff c arr hready).mp (by simpa [hout] using hzero)
  intro k hk
  have row := hall k hk
  have prime := hprime k hk
  let p := arr (c.pBase + k)
  let q := arr (c.qBase + k)
  change p ≤ c.evenAt k ∧ q = c.evenAt k - p ∧
    arr (c.pBitBase + k) = 1 ∧ arr (c.qBitBase + k) = 1 at row
  refine ⟨p, q, prime.1.mp row.2.2.1, prime.2.mp row.2.2.2, ?_⟩
  omega

/-- Fully receipt-facing form. A fail-safe audit receipt first proves that the
partial source program is defined; the ordinary rolled CompCert receipt then
identifies its output as zero. Thus neither the witness scan nor its
definedness is replayed in Lean. -/
def RolledResult (p : AProgram) (base : Int)
    (mem : LeanCompCert.Verified.MemFragment.Mem) (value : Int) : Prop :=
  Option.bind
    (LeanCompCert.Verified.MemFragment.evalMCCSequence
      (p.counterAugment.initialMCCWithMem base mem) p.rolledCompile)
    (fun m : LeanCompCert.Verified.MemFragment.MCCState =>
      m.env ⟨p.output + 1⟩) = some value

def AuditRolledZero (p : AProgram) (base : Int)
    (mem : LeanCompCert.Verified.MemFragment.Mem) : Prop :=
  RolledResult (LeanCompCert.Verified.ArrayAudit.auditProgram p) base mem 0

theorem covers_of_rolled_receipts
    (c : Cfg) (arr : Nat → Nat)
    (hcount : 0 < c.count) (hready : Ready c arr)
    (hprime : PrimeRowsCorrect c arr)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : LeanCompCert.Verified.MemFragment.Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (harr : ∀ k, arr k < M)
    (hAuditReceipt : Option.bind
      (LeanCompCert.Verified.MemFragment.evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (program c)).counterAugment.initialMCCWithMem
          base mem)
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (program c)).rolledCompile)
      (fun m : LeanCompCert.Verified.MemFragment.MCCState =>
        m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (program c)).output + 1⟩) =
          some (0 : Int))
    (hReceipt : Option.bind
      (LeanCompCert.Verified.MemFragment.evalMCCSequence
        ((program c).counterAugment.initialMCCWithMem base mem)
        (program c).rolledCompile)
      (fun m : LeanCompCert.Verified.MemFragment.MCCState =>
        m.env ⟨(program c).output + 1⟩) =
        some (0 : Int)) : Covers c := by
  have hlen : 0 < c.arrayLen := by simp [Cfg.arrayLen]; omega
  have hlenM : c.arrayLen < M := hready.1
  obtain ⟨out, hRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (program c) (program_wf c) base hBase arr mem hCells harr hlen hlenM
      hAuditReceipt
  have hzero : out.regs (program c).output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      (program c) (program_wf c) base hBase arr mem hCells
      (fun k _ => harr k) out hRun 0 hReceipt
  exact covers_of_compiled_run c arr out hready hprime hRun (by
    simpa [program, rViol] using hzero)

/-- Compact manifest-facing package for one independently checked interval. -/
structure RolledReceipt (c : Cfg) (arr : Nat → Nat) where
  count_pos : 0 < c.count
  ready : Ready c arr
  primeRows : PrimeRowsCorrect c arr
  base : Int
  baseOk : BaseOk c.arrayLen base
  mem : LeanCompCert.Verified.MemFragment.Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((arr k : Nat) : Int))
  words : ∀ k, arr k < M
  audit : AuditRolledZero (program c) base mem
  run : RolledResult (program c) base mem 0

theorem RolledReceipt.covers {c : Cfg} {arr : Nat → Nat}
    (receipt : RolledReceipt c arr) : Covers c := by
  apply covers_of_rolled_receipts c arr receipt.count_pos receipt.ready
    receipt.primeRows receipt.base receipt.baseOk receipt.mem receipt.cells
    receipt.words
  · exact receipt.audit
  · exact receipt.run

#print axioms program_wf
#print axioms checkedState_zero_iff
#print axioms covers_of_compiled_run
#print axioms covers_of_rolled_receipts
#print axioms RolledReceipt.covers

end LeanCompCert.Ports.TGEvenGoldbach
