import LeanCompCert.Ports.TGEvenGoldbach

/-!
# A fail-closed two-mask binary-Goldbach checker

The source computation used for the long finite Goldbach verification searches
for a comparatively small prime `p` and sieves the complementary large value
`q`.  Requiring both values to inhabit one segmented-sieve window is therefore
the wrong physical contract.  This module supplies the exact constant-size
checker for the honest two-window layout.

The first mask occupies `[0, largeLen)`.  A caller-owned scratch region may
follow it; the small-prime mask starts at `smallBase`, and the two witness
planes start at `witnessBase`.  A row is accepted only when both witnesses are
in their respective windows, both addressed mask cells are one, and their
ordinary (non-wrapping) sum is the represented even integer.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.TGEvenGoldbachTwoMask

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.PackedSieve

/-- Physical layout for one independently runnable two-mask shard. -/
structure Cfg where
  largeLo : Nat
  largeLen : Nat
  smallBase : Nat
  smallLo : Nat
  smallLen : Nat
  witnessBase : Nat
  goldbach : TGEvenGoldbach.Cfg
  deriving Repr

def Cfg.pBase (c : Cfg) : Nat := c.witnessBase
def Cfg.qBase (c : Cfg) : Nat := c.witnessBase + c.goldbach.count
def Cfg.arrayLen (c : Cfg) : Nat := c.witnessBase + 2 * c.goldbach.count

abbrev rViol : Nat := 0
abbrev rAddr : Nat := 1
abbrev rP : Nat := 2
abbrev rQ : Nat := 3
abbrev rSmallLo : Nat := 4
abbrev rSmallHi : Nat := 5
abbrev rSmallRange : Nat := 6
abbrev rSmallOff : Nat := 7
abbrev rSmallSafe : Nat := 8
abbrev rPBit : Nat := 9
abbrev rLargeLo : Nat := 10
abbrev rLargeHi : Nat := 11
abbrev rLargeRange : Nat := 12
abbrev rLargeOff : Nat := 13
abbrev rLargeSafe : Nat := 14
abbrev rQBit : Nat := 15
abbrev rPBitGood : Nat := 16
abbrev rQBitGood : Nat := 17
abbrev rTarget : Nat := 18
abbrev rSum : Nat := 19
abbrev rSumGood : Nat := 20
abbrev rGood : Nat := 21
abbrev rBad : Nat := 22
abbrev regCount : Nat := 23

/-- One branch-free row.  Failed range tests force a safe in-bounds mask load;
the same failed test remains in `rGood`, so the safe load cannot turn a bad row
into an accepted row. -/
def body (c : Cfg) : List AInstr :=
  [ .scalar (.binop rAddr .add (.lit c.pBase) .idx)
  , .load rP rAddr
  , .scalar (.binop rAddr .add (.lit c.qBase) .idx)
  , .load rQ rAddr
  , .scalar (.binop rSmallLo .le (.lit c.smallLo) (.reg rP))
  , .scalar (.binop rSmallHi .lt (.reg rP)
      (.lit (c.smallLo + c.smallLen)))
  , .scalar (.binop rSmallRange .mul (.reg rSmallLo) (.reg rSmallHi))
  , .scalar (.binop rSmallOff .sub (.reg rP) (.lit c.smallLo))
  , .scalar (.binop rSmallSafe .mul (.reg rSmallRange) (.reg rSmallOff))
  , .scalar (.binop rAddr .add (.lit c.smallBase) (.reg rSmallSafe))
  , .load rPBit rAddr
  , .scalar (.binop rLargeLo .le (.lit c.largeLo) (.reg rQ))
  , .scalar (.binop rLargeHi .lt (.reg rQ)
      (.lit (c.largeLo + c.largeLen)))
  , .scalar (.binop rLargeRange .mul (.reg rLargeLo) (.reg rLargeHi))
  , .scalar (.binop rLargeOff .sub (.reg rQ) (.lit c.largeLo))
  , .scalar (.binop rLargeSafe .mul (.reg rLargeRange) (.reg rLargeOff))
  , .load rQBit rLargeSafe
  , .scalar (.binop rPBitGood .eq (.reg rPBit) (.lit 1))
  , .scalar (.binop rQBitGood .eq (.reg rQBit) (.lit 1))
  , .scalar (.binop rTarget .mul (.lit 2) .idx)
  , .scalar (.binop rTarget .add (.lit c.goldbach.evenLo) (.reg rTarget))
  , .scalar (.binop rSum .add (.reg rP) (.reg rQ))
  , .scalar (.binop rSumGood .eq (.reg rSum) (.reg rTarget))
  , .scalar (.binop rGood .mul (.reg rSmallRange) (.reg rLargeRange))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rPBitGood))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rQBitGood))
  , .scalar (.binop rGood .mul (.reg rGood) (.reg rSumGood))
  , .scalar (.binop rBad .eq (.reg rGood) (.lit 0))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

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
    regCount, rViol, rAddr, rP, rQ, rSmallLo, rSmallHi, rSmallRange,
    rSmallOff, rSmallSafe, rPBit, rLargeLo, rLargeHi, rLargeRange,
    rLargeOff, rLargeSafe, rQBit, rPBitGood, rQBitGood, rTarget, rSum,
    rSumGood, rGood, rBad]

/-- Cheap word/allocation guards.  The sum bound is deliberately a bound on
the two complete mask windows; once both range gates pass, `p+q` is therefore
ordinary addition rather than `u64` wraparound. -/
def Ready (c : Cfg) (arr : Nat → Nat) : Prop :=
  0 < c.largeLen ∧ 0 < c.smallLen ∧
  c.largeLen ≤ c.smallBase ∧
  c.smallBase + c.smallLen ≤ c.witnessBase ∧
  c.largeLo + c.largeLen < M ∧
  c.smallLo + c.smallLen < M ∧
  (c.largeLo + c.largeLen) + (c.smallLo + c.smallLen) < M ∧
  c.goldbach.evenLo + 2 * c.goldbach.count < M ∧
  c.arrayLen < M ∧
  ∀ i, i < c.arrayLen → arr i < M

/-- Exact predicate checked in row `k`. -/
def RowGood (c : Cfg) (arr : Nat → Nat) (k : Nat) : Prop :=
  let p := arr (c.pBase + k)
  let q := arr (c.qBase + k)
  c.smallLo ≤ p ∧ p < c.smallLo + c.smallLen ∧
    arr (c.smallBase + (p - c.smallLo)) = 1 ∧
    c.largeLo ≤ q ∧ q < c.largeLo + c.largeLen ∧
    arr (q - c.largeLo) = 1 ∧
    p + q = c.goldbach.evenAt k

instance (c : Cfg) (arr : Nat → Nat) (k : Nat) :
    Decidable (RowGood c arr k) := by
  unfold RowGood
  infer_instance

set_option maxRecDepth 40000 in
theorem body_arr (c : Cfg) (k : Nat) (s : AState) :
    (arun k s (body c)).arr = s.arr := by
  simp [body, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
    denoteOp]

set_option maxRecDepth 50000 in
theorem body_viol (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hready : Ready c arr) (hk : k < c.goldbach.count)
    (hsarr : s.arr = arr) (hsbit : s.regs rViol ≤ 1) :
    (arun k s (body c)).regs rViol =
      s.regs rViol ||| (if RowGood c arr k then 0 else 1) := by
  rcases hready with
    ⟨hLargePos, hSmallPos, hLayoutLarge, hLayoutSmall, hLargeM, hSmallM,
      hSumM, hEvenM, hArrayM, hWords⟩
  have hkM : k < M := by
    simp only [Cfg.arrayLen] at hArrayM
    omega
  have hCountM : c.goldbach.count < M := by
    simp only [Cfg.arrayLen] at hArrayM
    omega
  have hpAddr : c.pBase + k < c.arrayLen := by
    simp [Cfg.pBase, Cfg.arrayLen]
    omega
  have hqAddr : c.qBase + k < c.arrayLen := by
    simp [Cfg.qBase, Cfg.arrayLen]
    omega
  have hpM : arr (c.pBase + k) < M := hWords _ hpAddr
  have hqM : arr (c.qBase + k) < M := hWords _ hqAddr
  have hpAddrM := Nat.lt_trans hpAddr hArrayM
  have hqAddrM := Nat.lt_trans hqAddr hArrayM
  have hpBaseM : c.pBase < M := by omega
  have hqBaseM : c.qBase < M := by omega
  have hSmallBaseM : c.smallBase < M := by
    change c.witnessBase < M at hpBaseM
    omega
  have hSmallLoM : c.smallLo < M := by omega
  have hLargeLoM : c.largeLo < M := by omega
  have hEvenLoM : c.goldbach.evenLo < M := by omega
  have hTwoM : 2 < M := by decide
  have hTwoKM : 2 * k < M := by omega
  have hTargetM : c.goldbach.evenLo + 2 * k < M := by omega
  subst hsarr
  simp only [body, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, Nat.reduceEqDiff, if_false, if_true,
    Option.getD_some, rViol, rAddr, rP, rQ, rSmallLo, rSmallHi,
    rSmallRange, rSmallOff, rSmallSafe, rPBit, rLargeLo, rLargeHi,
    rLargeRange, rLargeOff, rLargeSafe, rQBit, rPBitGood, rQBitGood,
    rTarget, rSum, rSumGood, rGood, rBad,
    Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hCountM,
    Nat.mod_eq_of_lt hpAddrM, Nat.mod_eq_of_lt hqAddrM,
    Nat.mod_eq_of_lt hpM, Nat.mod_eq_of_lt hqM,
    Nat.mod_eq_of_lt hpBaseM, Nat.mod_eq_of_lt hqBaseM,
    Nat.mod_eq_of_lt hSmallBaseM, Nat.mod_eq_of_lt hSmallLoM,
    Nat.mod_eq_of_lt hLargeLoM, Nat.mod_eq_of_lt hEvenLoM,
    Nat.mod_eq_of_lt hSmallM, Nat.mod_eq_of_lt hLargeM,
    Nat.mod_eq_of_lt hTwoM, Nat.mod_eq_of_lt hTwoKM,
    Nat.mod_eq_of_lt hTargetM]
  let p := s.arr (c.pBase + k)
  let q := s.arr (c.qBase + k)
  by_cases hpLo : c.smallLo ≤ p
  · by_cases hpHi : p < c.smallLo + c.smallLen
    · have hpOff : p - c.smallLo < c.smallLen := by omega
      have hpOffM : p - c.smallLo < M := by omega
      have hpSub : (p + (M - c.smallLo)) % M = p - c.smallLo := by
        have heq : p + (M - c.smallLo) = M + (p - c.smallLo) := by omega
        rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt hpOffM]
      have hpMaskAddr : c.smallBase + (p - c.smallLo) < M := by
        have hlt : c.smallBase + (p - c.smallLo) <
            c.smallBase + c.smallLen := Nat.add_lt_add_left hpOff _
        have hWitnessM : c.witnessBase < M := by
          simpa [Cfg.pBase] using hpBaseM
        omega
      simp only [p, hpLo, hpHi, if_true, Nat.one_mul,
        Nat.mod_eq_of_lt (show 1 < M by decide),
        Nat.mod_eq_of_lt hpOffM]
      rw [hpSub, Nat.mod_eq_of_lt hpOffM, Nat.mod_eq_of_lt hpMaskAddr]
      by_cases hpBit : s.arr (c.smallBase + (p - c.smallLo)) = 1
      · by_cases hqLo : c.largeLo ≤ q
        · by_cases hqHi : q < c.largeLo + c.largeLen
          · have hqOff : q - c.largeLo < c.largeLen := by omega
            have hqOffM : q - c.largeLo < M := by omega
            have hqSub : (q + (M - c.largeLo)) % M = q - c.largeLo := by
              have heq : q + (M - c.largeLo) = M + (q - c.largeLo) := by
                omega
              rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
                Nat.mod_eq_of_lt hqOffM]
            have hpqM : p + q < M := by omega
            simp only [q, hqLo, hqHi, if_true, Nat.one_mul,
              Nat.mod_eq_of_lt (show 1 < M by decide),
              Nat.mod_eq_of_lt hqOffM]
            rw [hqSub, Nat.mod_eq_of_lt hqOffM, Nat.mod_eq_of_lt hpqM]
            by_cases hqBit : s.arr (q - c.largeLo) = 1
            · by_cases hsum : p + q = c.goldbach.evenAt k
              · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
                  simp [RowGood, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                    hqBit, hsum, hs, TGEvenGoldbach.Cfg.evenAt, M]
              · have hsum' : ¬(s.arr (c.pBase + k) + s.arr (c.qBase + k) =
                    c.goldbach.evenLo + 2 * k) := by
                  simpa [p, q, TGEvenGoldbach.Cfg.evenAt] using hsum
                rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
                  simp [RowGood, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                    hqBit, hsum', hs, TGEvenGoldbach.Cfg.evenAt, M]
            · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
                simp [RowGood, p, q, hpLo, hpHi, hpBit, hqLo, hqHi,
                  hqBit, hs, TGEvenGoldbach.Cfg.evenAt, M]
          · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
              simp [RowGood, p, q, hpLo, hpHi, hpBit, hqLo, hqHi, hs,
                TGEvenGoldbach.Cfg.evenAt, M]
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
            simp [RowGood, p, q, hpLo, hpHi, hpBit, hqLo, hs,
              TGEvenGoldbach.Cfg.evenAt, M]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
          simp [RowGood, p, q, hpLo, hpHi, hpBit, hs,
            TGEvenGoldbach.Cfg.evenAt, M]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
        simp [RowGood, p, q, hpLo, hpHi, hs, TGEvenGoldbach.Cfg.evenAt, M]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
      simp [RowGood, p, q, hpLo, hs, TGEvenGoldbach.Cfg.evenAt, M]

theorem body_viol_le_one (c : Cfg) (arr : Nat → Nat) (k : Nat) (s : AState)
    (hready : Ready c arr) (hk : k < c.goldbach.count)
    (hsarr : s.arr = arr) (hsbit : s.regs rViol ≤ 1) :
    (arun k s (body c)).regs rViol ≤ 1 := by
  rw [body_viol c arr k s hready hk hsarr hsbit]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
    by_cases hgood : RowGood c arr k <;> simp [hs, hgood]

def checkedState (c : Cfg) (arr : Nat → Nat) : AState :=
  (List.range c.goldbach.count).foldl
    (fun s k => arun k s (body c)) (initialAStateWithArray arr)

private theorem fold_zero_iff (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) (rows : List Nat)
    (hmem : ∀ k ∈ rows, k < c.goldbach.count) (s : AState)
    (hsarr : s.arr = arr) (hsbit : s.regs rViol ≤ 1) :
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

theorem checkedState_zero_iff (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) :
    (checkedState c arr).regs rViol = 0 ↔
      ∀ k, k < c.goldbach.count → RowGood c arr k := by
  unfold checkedState
  rw [fold_zero_iff c arr hready (List.range c.goldbach.count)
    (fun k hk => List.mem_range.mp hk) (initialAStateWithArray arr) rfl
    (by simp [initialAStateWithArray, initialState, rViol])]
  constructor
  · rintro ⟨_, hall⟩ k hk
    exact hall k (List.mem_range.mpr hk)
  · intro hall
    exact ⟨rfl, fun k hk => hall k (List.mem_range.mp hk)⟩

theorem run_eq_checkedState (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hRun : (program c).runFromArray arr = some out) :
    out = checkedState c arr := by
  have h := AProgram.eq_arun_of_runFromArray_eq_some (program c) arr out hRun
  simpa [program, checkedState, arun_nil] using h

/-- Exact primality meaning of a mask window at an arbitrary array offset. -/
def PrimeMaskCorrect (arr : Nat → Nat) (base lo len : Nat) : Prop :=
  ∀ i, i < len → (arr (base + i) = 1 ↔ IsPrime (lo + i))

/-- The exact paper-facing consequence. -/
def Covers (c : Cfg) : Prop := TGEvenGoldbach.Covers c.goldbach

theorem covers_of_compiled_run (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hready : Ready c arr)
    (hsmall : PrimeMaskCorrect arr c.smallBase c.smallLo c.smallLen)
    (hlarge : PrimeMaskCorrect arr 0 c.largeLo c.largeLen)
    (hRun : (program c).runFromArray arr = some out)
    (hzero : out.regs rViol = 0) : Covers c := by
  have hout := run_eq_checkedState c arr out hRun
  have hall := (checkedState_zero_iff c arr hready).mp (by
    simpa [hout] using hzero)
  intro k hk
  have row := hall k hk
  let p := arr (c.pBase + k)
  let q := arr (c.qBase + k)
  change c.smallLo ≤ p ∧ p < c.smallLo + c.smallLen ∧
    arr (c.smallBase + (p - c.smallLo)) = 1 ∧
    c.largeLo ≤ q ∧ q < c.largeLo + c.largeLen ∧
    arr (q - c.largeLo) = 1 ∧ p + q = c.goldbach.evenAt k at row
  have hpOff : p - c.smallLo < c.smallLen := by omega
  have hqOff : q - c.largeLo < c.largeLen := by omega
  have hp := (hsmall (p - c.smallLo) hpOff).mp row.2.2.1
  have hq := (hlarge (q - c.largeLo) hqOff).mp (by
    simpa using row.2.2.2.2.2.1)
  refine ⟨p, q, ?_, ?_, row.2.2.2.2.2.2⟩
  · simpa only [Nat.add_sub_of_le row.1] using hp
  · simpa only [Nat.add_sub_of_le row.2.2.2.1] using hq

/- The physical rolled bridge is kept in the companion soundness module. -/

#print axioms program_wf
#print axioms checkedState_zero_iff
#print axioms covers_of_compiled_run

end LeanCompCert.Ports.TGEvenGoldbachTwoMask
