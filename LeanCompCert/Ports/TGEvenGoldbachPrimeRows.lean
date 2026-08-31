import LeanCompCert.Ports.RS62SegmentedPrimeMask
import LeanCompCert.Ports.TGEvenGoldbach
import LeanCompCert.Verified.ArrayPadding
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Compiled prime-row packing for finite even Goldbach

The segmented sieve leaves an exact `0`/`1` primality mask in the first
`segLen` cells of a caller-owned allocation.  External witness values are
archived after the sieve scratch region in the existing `p` and `q` planes.
The rolled program below checks that both witnesses of every row lie in the
mask window and have bit one, then writes the two missing bit planes.  The
resulting suffix is exactly the four-plane array consumed by
`TGEvenGoldbach`; no duplicate witness archive is allocated.

The important theorem is `primeRowsCorrect_of_run_zero`: accepting source
execution, together with the exact mask denotation, produces the *literal*
`TGEvenGoldbach.PrimeRowsCorrect` proposition.  All proofs are symbolic in the
row count and mask length; no production interval is enumerated.
-/

namespace LeanCompCert.Ports.TGEvenGoldbachPrimeRows

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegSieve

/-- One independently runnable prime-row shard.  Both witnesses are required
to lie in this shard's segmented-prime window. -/
structure Cfg where
  sieve : ArraySegSieve.Cfg
  goldbach : TGEvenGoldbach.Cfg
  deriving Repr

def Cfg.outputBase (c : Cfg) : Nat := c.sieve.arrayLen
def Cfg.witnessPBase (c : Cfg) : Nat := c.outputBase + c.goldbach.pBase
def Cfg.witnessQBase (c : Cfg) : Nat := c.outputBase + c.goldbach.qBase
def Cfg.arrayLen (c : Cfg) : Nat := c.outputBase + c.goldbach.arrayLen

/-- Interpret the disjoint output region as the exact four-plane Goldbach
array expected by the existing checker. -/
def outputArray (c : Cfg) (arr : Nat → Nat) : Nat → Nat :=
  fun i => arr (c.outputBase + i)

abbrev rViol : Nat := 0
abbrev rAddr : Nat := 1
abbrev rP : Nat := 2
abbrev rQ : Nat := 3
abbrev rLoLeP : Nat := 4
abbrev rPLtHi : Nat := 5
abbrev rPRange : Nat := 6
abbrev rPOff : Nat := 7
abbrev rPSafe : Nat := 8
abbrev rPBit : Nat := 9
abbrev rLoLeQ : Nat := 10
abbrev rQLtHi : Nat := 11
abbrev rQRange : Nat := 12
abbrev rQOff : Nat := 13
abbrev rQSafe : Nat := 14
abbrev rQBit : Nat := 15
abbrev rPBitGood : Nat := 16
abbrev rQBitGood : Nat := 17
abbrev rGood : Nat := 18
abbrev rBad : Nat := 19
abbrev rOne : Nat := 20
abbrev regCount : Nat := 21

/-- Validate two archived witnesses against the produced mask and materialize
one four-plane output row.  Invalid ranges use mask cell zero as a safe load;
the monotone violation flag still rejects the row. -/
def body (c : Cfg) : List AInstr :=
  [ .scalar (.binop rAddr .add (.lit c.witnessPBase) .idx)
  , .load rP rAddr
  , .scalar (.binop rAddr .add (.lit c.witnessQBase) .idx)
  , .load rQ rAddr
  , .scalar (.binop rLoLeP .le (.lit c.sieve.lo) (.reg rP))
  , .scalar (.binop rPLtHi .lt (.reg rP)
      (.lit (c.sieve.lo + c.sieve.segLen)))
  , .scalar (.binop rPRange .mul (.reg rLoLeP) (.reg rPLtHi))
  , .scalar (.binop rPOff .sub (.reg rP) (.lit c.sieve.lo))
  , .scalar (.binop rPSafe .mul (.reg rPRange) (.reg rPOff))
  , .load rPBit rPSafe
  , .scalar (.binop rLoLeQ .le (.lit c.sieve.lo) (.reg rQ))
  , .scalar (.binop rQLtHi .lt (.reg rQ)
      (.lit (c.sieve.lo + c.sieve.segLen)))
  , .scalar (.binop rQRange .mul (.reg rLoLeQ) (.reg rQLtHi))
  , .scalar (.binop rQOff .sub (.reg rQ) (.lit c.sieve.lo))
  , .scalar (.binop rQSafe .mul (.reg rQRange) (.reg rQOff))
  , .load rQBit rQSafe
  , .scalar (.binop rPBitGood .eq (.reg rPBit) (.lit 1))
  , .scalar (.binop rQBitGood .eq (.reg rQBit) (.lit 1))
  , .scalar (.binop rGood .mul (.reg rPRange) (.reg rQRange))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rPBitGood))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rQBitGood))
  , .scalar (.binop rBad .eq (.reg rGood) (.lit 0))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad))
  , .scalar (.mov rOne (.lit 1))
  , .scalar (.binop rAddr .add
      (.lit (c.outputBase + c.goldbach.pBitBase)) .idx)
  , .store rAddr rOne
  , .scalar (.binop rAddr .add
      (.lit (c.outputBase + c.goldbach.qBitBase)) .idx)
  , .store rAddr rOne ]

def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.goldbach.count
  init := []
  body := body c
  epilogue := []
  output := rViol
}

set_option maxRecDepth 40000 in
theorem program_wf (c : Cfg) : (program c).WF := by
  simp [AProgram.WF, program, body, AInstr.WF, Instr.WF, Operand.WF,
    regCount, rViol, rAddr, rP, rQ, rLoLeP, rPLtHi, rPRange, rPOff,
    rPSafe, rPBit, rLoLeQ, rQLtHi, rQRange, rQOff, rQSafe, rQBit,
    rPBitGood, rQBitGood, rGood, rBad, rOne]

/-- Compact word and allocation guards. -/
def Ready (c : Cfg) (arr : Nat → Nat) : Prop :=
  0 < c.sieve.segLen ∧
  c.sieve.lo + c.sieve.segLen < M ∧
  c.arrayLen < M ∧
  ∀ i, i < c.arrayLen → arr i < M

/-- Exact row predicate accepted by the packer before the writes happen. -/
def RowAccepted (c : Cfg) (arr : Nat → Nat) (k : Nat) : Prop :=
  let p := arr (c.witnessPBase + k)
  let q := arr (c.witnessQBase + k)
  c.sieve.lo ≤ p ∧ p < c.sieve.lo + c.sieve.segLen ∧
    arr (p - c.sieve.lo) = 1 ∧
    c.sieve.lo ≤ q ∧ q < c.sieve.lo + c.sieve.segLen ∧
    arr (q - c.sieve.lo) = 1

instance (c : Cfg) (arr : Nat → Nat) (k : Nat) :
    Decidable (RowAccepted c arr k) := by
  unfold RowAccepted
  infer_instance

set_option maxRecDepth 40000 in
theorem body_result (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hready : Ready c arr) (hk : k < c.goldbach.count)
    (hsarr : s.arr = arr) (hsbit : s.regs rViol ≤ 1) :
    let out := arun k s (body c)
    out.regs rViol =
        s.regs rViol ||| (if RowAccepted c arr k then 0 else 1) ∧
      out.arr (c.outputBase + c.goldbach.pBitBase + k) = 1 ∧
      out.arr (c.outputBase + c.goldbach.qBitBase + k) = 1 := by
  rcases hready with ⟨hsegPos, hhiM, harrayM, hwords⟩
  have hkM : k < M := by
    simp only [Cfg.arrayLen, Cfg.outputBase, Cfg.witnessQBase,
      Cfg.witnessPBase, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    omega
  have hpAddr : c.witnessPBase + k < c.arrayLen := by
    simp only [Cfg.arrayLen, Cfg.witnessPBase,
      TGEvenGoldbach.Cfg.arrayLen, TGEvenGoldbach.Cfg.pBase]
    omega
  have hqAddr : c.witnessQBase + k < c.arrayLen := by
    simp only [Cfg.arrayLen, Cfg.witnessQBase,
      TGEvenGoldbach.Cfg.arrayLen, TGEvenGoldbach.Cfg.qBase]
    omega
  have hpM := hwords _ hpAddr
  have hqM := hwords _ hqAddr
  have hcountM : c.goldbach.count < M := by
    simp only [Cfg.arrayLen, Cfg.outputBase, Cfg.witnessQBase,
      TGEvenGoldbach.Cfg.arrayLen] at harrayM
    omega
  have hscratchLe : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [ArraySegSieve.Cfg.arrayLen, ArraySegSieve.Cfg.resultBase]
    omega
  have hsegM : c.sieve.segLen < M := by omega
  have hbaseM : c.outputBase < M := by
    simp only [Cfg.arrayLen] at harrayM
    omega
  have hpOutM : c.outputBase + c.goldbach.pBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.pBase]
    omega
  have hqOutM : c.outputBase + c.goldbach.qBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.qBase]
    omega
  have hpBitOutM : c.outputBase + c.goldbach.pBitBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hqBitOutM : c.outputBase + c.goldbach.qBitBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.qBitBase]
    omega
  have hpAddrM : c.witnessPBase + k < M := Nat.lt_trans hpAddr harrayM
  have hqAddrM : c.witnessQBase + k < M := Nat.lt_trans hqAddr harrayM
  have hpBaseM : c.witnessPBase < M := by omega
  have hqBaseM : c.witnessQBase < M := by omega
  have hloM : c.sieve.lo < M := by omega
  have hpOutBaseM : c.outputBase + c.goldbach.pBase < M := by omega
  have hqOutBaseM : c.outputBase + c.goldbach.qBase < M := by omega
  have hpBitOutBaseM : c.outputBase + c.goldbach.pBitBase < M := by omega
  have hqBitOutBaseM : c.outputBase + c.goldbach.qBitBase < M := by omega
  have hc0 : c.goldbach.count ≠ 0 := by omega
  have h2c0 : 2 * c.goldbach.count ≠ 0 := by omega
  have h3c0 : 3 * c.goldbach.count ≠ 0 := by omega
  have hc2 : c.goldbach.count ≠ 2 * c.goldbach.count := by omega
  have hc3 : c.goldbach.count ≠ 3 * c.goldbach.count := by omega
  have h2c3 : 2 * c.goldbach.count ≠ 3 * c.goldbach.count := by omega
  subst hsarr
  simp only [body, arun, astep, AState.writeReg, AState.writeArr, sdest,
    sval, denoteOperand, denoteOp, Nat.reduceEqDiff, if_false, if_true,
    Option.getD_some, rViol, rAddr, rP, rQ, rLoLeP, rPLtHi, rPRange,
    rPOff, rPSafe, rPBit, rLoLeQ, rQLtHi, rQRange, rQOff, rQSafe,
    rQBit, rPBitGood, rQBitGood, rGood, rBad, rOne,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hpAddrM,
    Nat.mod_eq_of_lt hqAddrM, Nat.mod_eq_of_lt hhiM,
    Nat.mod_eq_of_lt hpM, Nat.mod_eq_of_lt hqM,
    Nat.mod_eq_of_lt hcountM, Nat.mod_eq_of_lt hsegM,
    Nat.mod_eq_of_lt hbaseM, Nat.mod_eq_of_lt hpOutM,
    Nat.mod_eq_of_lt hqOutM, Nat.mod_eq_of_lt hpBitOutM,
    Nat.mod_eq_of_lt hqBitOutM, Nat.mod_eq_of_lt hpBaseM,
    Nat.mod_eq_of_lt hqBaseM, Nat.mod_eq_of_lt hloM,
    Nat.mod_eq_of_lt hpOutBaseM, Nat.mod_eq_of_lt hqOutBaseM,
    Nat.mod_eq_of_lt hpBitOutBaseM, Nat.mod_eq_of_lt hqBitOutBaseM]
  let p := s.arr (c.witnessPBase + k)
  let q := s.arr (c.witnessQBase + k)
  by_cases hpLo : c.sieve.lo ≤ p
  · by_cases hpHi : p < c.sieve.lo + c.sieve.segLen
    · have hpOff : p - c.sieve.lo < c.sieve.segLen := by omega
      have hpOffM : p - c.sieve.lo < M := Nat.lt_trans hpOff hsegM
      have hpOffM' :
          s.arr (c.witnessPBase + k) - c.sieve.lo < M := by
        simpa only [p] using hpOffM
      have hpSub : (p + (M - c.sieve.lo)) % M = p - c.sieve.lo := by
        have heq : p + (M - c.sieve.lo) = M + (p - c.sieve.lo) := by
          omega
        rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hpOffM]
      rw [hpSub]
      by_cases hpBit : s.arr (p - c.sieve.lo) = 1
      · have hpBitLoad :
            s.arr ((s.arr (c.witnessPBase + k) - c.sieve.lo) % M) = 1 := by
          rw [Nat.mod_eq_of_lt hpOffM']
          simpa only [p] using hpBit
        simp only [M] at hpBitLoad
        by_cases hqLo : c.sieve.lo ≤ q
        · by_cases hqHi : q < c.sieve.lo + c.sieve.segLen
          · have hqOff : q - c.sieve.lo < c.sieve.segLen := by omega
            have hqOffM : q - c.sieve.lo < M := Nat.lt_trans hqOff hsegM
            have hqOffM' :
                s.arr (c.witnessQBase + k) - c.sieve.lo < M := by
              simpa only [q] using hqOffM
            have hqSub : (q + (M - c.sieve.lo)) % M = q - c.sieve.lo := by
              have heq : q + (M - c.sieve.lo) = M + (q - c.sieve.lo) := by
                omega
              rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
                Nat.mod_eq_of_lt hqOffM]
            rw [hqSub]
            by_cases hqBit : s.arr (q - c.sieve.lo) = 1
            · have hqBitLoad :
                  s.arr ((s.arr (c.witnessQBase + k) - c.sieve.lo) % M) = 1 := by
                rw [Nat.mod_eq_of_lt hqOffM']
                simpa only [q] using hqBit
              simp only [M] at hqBitLoad
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
                simp [RowAccepted, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                  hqBit, hpBitLoad, hqBitLoad, hs, M, TGEvenGoldbach.Cfg.pBase,
                  TGEvenGoldbach.Cfg.qBase, TGEvenGoldbach.Cfg.pBitBase,
                  TGEvenGoldbach.Cfg.qBitBase, hc0, h2c0, h3c0, hc2, hc3,
                  h2c3]
            · have hqBitLoad :
                  ¬ s.arr ((s.arr (c.witnessQBase + k) - c.sieve.lo) % M) = 1 := by
                rw [Nat.mod_eq_of_lt hqOffM']
                simpa only [q] using hqBit
              simp only [M] at hqBitLoad
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
                simp [RowAccepted, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                  hqBit, hpBitLoad, hqBitLoad, hs, M, TGEvenGoldbach.Cfg.pBase,
                  TGEvenGoldbach.Cfg.qBase, TGEvenGoldbach.Cfg.pBitBase,
                  TGEvenGoldbach.Cfg.qBitBase, hc0, h2c0, h3c0, hc2, hc3,
                  h2c3]
          · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
              simp [RowAccepted, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                hs, M, TGEvenGoldbach.Cfg.pBase,
                TGEvenGoldbach.Cfg.qBase, TGEvenGoldbach.Cfg.pBitBase,
                TGEvenGoldbach.Cfg.qBitBase, hc0, h2c0, h3c0, hc2, hc3,
                h2c3, hpBitLoad]
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
            simp [RowAccepted, p, q, hpLo, hpHi, hpBit, hqLo, hs, M,
              TGEvenGoldbach.Cfg.pBase, TGEvenGoldbach.Cfg.qBase,
              TGEvenGoldbach.Cfg.pBitBase, TGEvenGoldbach.Cfg.qBitBase,
              hc0, h2c0, h3c0, hc2, hc3, h2c3,
              hpBitLoad]
      · have hpBitLoad :
            ¬ s.arr ((s.arr (c.witnessPBase + k) - c.sieve.lo) % M) = 1 := by
          rw [Nat.mod_eq_of_lt hpOffM']
          simpa only [p] using hpBit
        simp only [M] at hpBitLoad
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
          simp [RowAccepted, p, q, hpLo, hpHi, hpBit, hs, M,
            TGEvenGoldbach.Cfg.pBase, TGEvenGoldbach.Cfg.qBase,
            TGEvenGoldbach.Cfg.pBitBase, TGEvenGoldbach.Cfg.qBitBase,
            hc0, h2c0, h3c0, hc2, hc3, h2c3, hpBitLoad]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
        simp [RowAccepted, p, q, hpLo, hpHi, hs, M,
          TGEvenGoldbach.Cfg.pBase, TGEvenGoldbach.Cfg.qBase,
          TGEvenGoldbach.Cfg.pBitBase, TGEvenGoldbach.Cfg.qBitBase,
          hc0, h2c0, h3c0, hc2, hc3, h2c3]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
      simp [RowAccepted, p, q, hpLo, hs, M,
        TGEvenGoldbach.Cfg.pBase, TGEvenGoldbach.Cfg.qBase,
        TGEvenGoldbach.Cfg.pBitBase, TGEvenGoldbach.Cfg.qBitBase,
        hc0, h2c0, h3c0, hc2, hc3, h2c3]
  all_goals simp_all

def packedState (c : Cfg) (arr : Nat → Nat) : AState :=
  (List.range c.goldbach.count).foldl
    (fun s k => arun k s (body c)) (initialAStateWithArray arr)

theorem run_eq_packedState (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hRun : (program c).runFromArray arr = some out) :
    out = packedState c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some (program c) arr out hRun
  simpa [program, packedState, arun] using h

/- The remaining fold invariants and the physical receipt bridge are kept in
the companion file `TGEvenGoldbachPrimeRowsSound`. -/

#print axioms program_wf
#print axioms body_result
#print axioms run_eq_packedState

end LeanCompCert.Ports.TGEvenGoldbachPrimeRows
