import LeanCompCert.Ports.ArraySegMobiusPlattSchedule
import LeanCompCert.Ports.ArraySieveCount
import LeanCompCert.Verified.ArrayComputation

/-!
# Compiled finite evidence for the aligned Platt root schedules

The only expensive arithmetic fact needed by both literal root schedules is
the number of primes through `87903`.  It is computed by the proved
array-backed sieve-count program.  The named physical-run admission below
states only that compiled program's returned word; the denotation theorem and
ordinary Lean lemmas turn it into schedule capacity and final-length facts.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence

set_option maxRecDepth 10000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattConfig
open LeanCompCert.Ports.ArraySegMobiusPlattSchedule

/-- The proved array program that counts primes in `[0, 87904)`. -/
def plattPrimeCountComputation : AComputation where
  program := sieveCountProgram 295 87904
  wellFormed := sieveCountProgram_wf 295 87904
  base := 0
  baseOk := ⟨by decide, by decide⟩
  name := "platt-prime-count-87904"

/-- Physical CompCert result for the 26,019,584-iteration prime-count sweep. -/
axiom plattPrimeCount_compcert_run :
  plattPrimeCountComputation.Returns ((8534 : Nat) : Int)

/-- The compiled sweep establishes the exact prime count used as the root
table capacity. -/
theorem plattPrimeCount_eq : primeCount 87904 = 8534 := by
  have hDenote : plattPrimeCountComputation.program.denote =
      some (primeCount 87904) := by
    exact sieveCountProgram_denote 295 87904 (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have h := AComputation.value_of_returns plattPrimeCountComputation
    hDenote plattPrimeCount_compcert_run
  omega

/-- A smaller compiled count bounds every bootstrap and crossing prefix. -/
def plattCrossingPrimeCountComputation : AComputation where
  program := sieveCountProgram 170 29301
  wellFormed := sieveCountProgram_wf 170 29301
  base := 0
  baseOk := ⟨by decide, by decide⟩
  name := "platt-prime-count-29301"

/-- Physical CompCert result for the crossing-prefix prime count. -/
axiom plattCrossingPrimeCount_compcert_run :
  plattCrossingPrimeCountComputation.Returns ((3183 : Nat) : Int)

theorem plattCrossingPrimeCount_eq : primeCount 29301 = 3183 := by
  have hDenote : plattCrossingPrimeCountComputation.program.denote =
      some (primeCount 29301) := by
    exact sieveCountProgram_denote 170 29301 (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have h := AComputation.value_of_returns plattCrossingPrimeCountComputation
    hDenote plattCrossingPrimeCount_compcert_run
  omega

/-- The predicate counted by `ArraySieveCount` is the package's finite prime
predicate. -/
theorem countedPrime_iff (n : Nat) :
    (2 ≤ n ∧ Sieve.leastFactor n = n) ↔ IsPrime n := by
  rw [isPrime_iff_bounded]
  constructor
  · rintro ⟨hn2, hlf⟩
    refine ⟨hn2, fun d hdLt hd2 hdvd => ?_⟩
    exact (leastFactor_eq_self_iff n hn2).mp hlf d hd2 hdLt
      (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  · rintro ⟨hn2, hn⟩
    refine ⟨hn2, (leastFactor_eq_self_iff n hn2).mpr ?_⟩
    intro d hd2 hdLt hdmod
    exact hn d hdLt hd2 (Nat.dvd_of_mod_eq_zero hdmod)

/-- Every exact finite prime table has the length counted by the verified
sieve program at the successor of its bound. -/
theorem primeTable_length_eq_primeCount {ps : List Nat} {bound : Nat}
    (h : PrimeTableInv ps bound) : ps.length = primeCount (bound + 1) := by
  let pred : Nat → Bool :=
    fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n)
  let canonical := (List.range (bound + 1)).filter pred
  have hpsNodup : ps.Nodup :=
    h.ordered.imp (by intro a b hab; omega)
  have hcanonicalNodup : canonical.Nodup := by
    exact List.nodup_range.filter pred
  have hmem : ∀ n, n ∈ ps ↔ n ∈ canonical := by
    intro n
    simp only [canonical, List.mem_filter, List.mem_range, pred,
      decide_eq_true_eq]
    constructor
    · intro hn
      exact ⟨by have := h.upper n hn; omega,
        (countedPrime_iff n).mpr (h.sound n hn)⟩
    · rintro ⟨hnBound, hnPrime⟩
      exact h.complete n ((countedPrime_iff n).mp hnPrime) (by omega)
  have hperm : List.Perm ps canonical := by
    rw [List.perm_iff_count]
    intro n
    rw [hpsNodup.count, hcanonicalNodup.count]
    simp only [hmem n]
  have hlen := hperm.length_eq
  simpa [primeCount, canonical, pred, List.countP_eq_length_filter] using hlen

/-- Sequential scanning preserves the exact prime-table invariant. -/
theorem rootScanFrom_primeTable {ps : List Nat} {bound w fuel : Nat}
    (hInv : PrimeTableInv ps bound) (hw : w = bound + 1) (hw2 : 2 ≤ w) :
    PrimeTableInv (rootScanFrom ps w fuel) (w + fuel - 1) := by
  induction fuel with
  | zero => simpa [hw] using hInv
  | succ k ih =>
      rw [rootScanFrom_succ]
      exact rootTableStep_preserves ih (by omega) (by omega)

/-- A mixed bootstrap/sequential scan preserves the exact prime table. -/
theorem rootScanMixed_primeTable {boot : List Nat} {bootBound w fuel : Nat}
    (hInv : PrimeTableInv boot bootBound) (hw : w - 1 ≤ bootBound)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound) :
    PrimeTableInv (rootScanMixed boot bootBound w fuel)
      (max bootBound (w + fuel - 1)) := by
  induction fuel with
  | zero => simpa [Nat.max_eq_left hw] using hInv
  | succ k ih =>
      rw [rootScanMixed_succ]
      by_cases hk : w + k ≤ bootBound
      · rw [if_pos hk]
        have hprev : max bootBound (w + k - 1) = bootBound := by omega
        have hnext : max bootBound (w + k) = bootBound := by omega
        rw [hprev] at ih
        simpa [hnext] using ih
      · rw [if_neg hk]
        have hprev : max bootBound (w + k - 1) = w + k - 1 := by omega
        have hnext : max bootBound (w + k) = w + k := by omega
        rw [hprev] at ih
        simpa [hnext] using
          rootTableStep_preserves ih (by omega) (by omega)

/-- Consecutive later windows preserve the same exact table invariant. -/
theorem rootLaterWindows_primeTable {c : Cfg} {ps : List Nat}
    {bound w fuel : Nat} (hInv : PrimeTableInv ps bound)
    (hw : w = bound + 1) (hw2 : 2 ≤ w) :
    PrimeTableInv (rootLaterWindows c ps w fuel)
      (w + fuel * c.segLen - 1) := by
  induction fuel with
  | zero => simpa [hw] using hInv
  | succ k ih =>
      rw [rootLaterWindows_succ]
      have hbase : w + k * c.segLen =
          (w + k * c.segLen - 1) + 1 := by omega
      simpa [Nat.add_mul, Nat.add_assoc] using
        rootScanFrom_primeTable ih hbase (by omega)

/-- Any exact prefix through the Platt root cap fits the compiled 8,534-slot
table, and an actually unmarked next candidate has room for its store. -/
theorem roomForStep_of_primeTable {c : Cfg} {ps : List Nat} {bound n : Nat}
    (htable : c.tableLen = 8534) (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1) (hn2 : 2 ≤ n) (hnCap : n ≤ 87903) :
    RoomForStep c ps n := by
  have hRange : List.Sublist (List.range (bound + 1)) (List.range 87904) :=
    (List.range_sublist).mpr (by omega)
  have hLen : ps.length ≤ 8534 := by
    rw [primeTable_length_eq_primeCount hInv, ← plattPrimeCount_eq]
    exact hRange.countP_le
  refine ⟨by rw [htable]; exact hLen, ?_⟩
  intro hu
  have hNextInv : PrimeTableInv (rootTableStep ps n) n :=
    rootTableStep_preserves hInv hnext hn2
  have hNextRange : List.Sublist (List.range (n + 1)) (List.range 87904) :=
    (List.range_sublist).mpr (by omega)
  have hNextLen : (rootTableStep ps n).length ≤ 8534 := by
    rw [primeTable_length_eq_primeCount hNextInv, ← plattPrimeCount_eq]
    exact hNextRange.countP_le
  simp [rootTableStep, hu] at hNextLen
  rw [htable]
  omega

/-- Every bootstrap or crossing prefix is strictly shorter than the final
table, via the smaller compiled count through `29300`. -/
theorem strictFit_of_primeTable {c : Cfg} {ps : List Nat} {bound : Nat}
    (htable : c.tableLen = 8534) (hInv : PrimeTableInv ps bound)
    (hbound : bound < 29301) : ps.length < c.tableLen := by
  have hRange : List.Sublist (List.range (bound + 1)) (List.range 29301) :=
    (List.range_sublist).mpr (by omega)
  have hCount : primeCount (bound + 1) ≤ primeCount 29301 :=
    hRange.countP_le
  rw [plattCrossingPrimeCount_eq] at hCount
  rw [htable, primeTable_length_eq_primeCount hInv]
  omega

private theorem plattBootPrime :
    PrimeTableInv plattBootPrimes plattBootBound := by
  have h := rootScanFrom_primeTable (fuel := 295)
    (LeanCompCert.Ports.ArraySegMobiusPrimeTable.empty)
    (w := 2) (by decide) (by decide)
  have heq : rootScanFrom [] 2 295 = plattBootPrimes := by decide
  simpa [heq, plattBootBound] using h

private theorem plattFirstCrossPrime :
    PrimeTableInv
      (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
      29301 := by
  simpa [crossingTable, crossingBase, plattAlignedFirst,
    plattFirstBootFuel, plattBootBound] using
    (rootScanMixed_primeTable (fuel := 29301) plattBootPrime
      (w := 1) (by decide) (by decide) (by decide))

private theorem plattTailCrossPrime :
    PrimeTableInv
      (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
      297 := by
  simpa [crossingTable, crossingBase, plattAlignedTail,
    plattTailBootFuel, plattBootBound] using
    (rootScanMixed_primeTable (fuel := 3) plattBootPrime
      (w := 295) (by decide) (by decide) (by decide))

/-- Complete finite evidence for the opening aligned schedule. -/
theorem plattAlignedFirst_finiteEvidence :
    ScheduleFiniteEvidence plattAlignedFirst plattBootBound
      plattFirstBootFuel plattFirstLaterFuel := by
  constructor
  case bootPrime => exact plattBootPrime
  case markBudget => decide
  case bootstrapFit =>
    intro n hn
    simp [plattFirstBootFuel] at hn
  case crossingFit =>
    intro k hk
    have hk' : k < 29301 := by simpa [plattAlignedFirst] using hk
    have hInv : PrimeTableInv
        (rootScanMixed plattBootPrimes plattBootBound 1 k)
        (max 296 k) := by
      simpa [plattBootBound] using
        (rootScanMixed_primeTable (fuel := k) plattBootPrime
          (w := 1) (by decide) (by decide) (by decide))
    have hFit := strictFit_of_primeTable (c := plattAlignedFirst)
      (by decide) hInv (by omega)
    simpa [crossingBase, plattFirstBootFuel, plattAlignedFirst] using hFit
  case laterRoom =>
    intro n hn k hk
    have hn' : n < 1 := by simpa [plattFirstLaterFuel] using hn
    have hk' : k < 29301 := by simpa [plattAlignedFirst] using hk
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedFirst
          (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
          29302 n)
        (29302 + n * 29301 - 1) := by
      simpa [plattAlignedFirst] using
        (rootLaterWindows_primeTable (c := plattAlignedFirst) (fuel := n)
          plattFirstCrossPrime (w := 29302) (by decide) (by decide))
    have hPrefix : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedFirst
            (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
            29302 n)
          (29302 + n * 29301) k)
        (29302 + n * 29301 + k - 1) := by
      exact rootScanFrom_primeTable (fuel := k) hWindows
        (w := 29302 + n * 29301) (by omega) (by omega)
    have hRoom := roomForStep_of_primeTable (c := plattAlignedFirst)
      (ps := rootScanFrom
        (rootLaterWindows plattAlignedFirst
          (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
          29302 n)
        (29302 + n * 29301) k)
      (bound := 29302 + n * 29301 + k - 1)
      (n := 29302 + n * 29301 + k) (by decide) hPrefix
      (by omega) (by omega) (by omega)
    simpa [laterBase, crossingBase, plattFirstBootFuel, plattAlignedFirst]
      using hRoom
  case finalRoom =>
    intro k hk
    have hk' : k < 29301 := by simpa [plattAlignedFirst] using hk
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedFirst
          (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
          29302 plattFirstLaterFuel)
        58602 := by
      simpa [plattAlignedFirst, plattFirstLaterFuel] using
        (rootLaterWindows_primeTable (c := plattAlignedFirst)
          (fuel := plattFirstLaterFuel) plattFirstCrossPrime
          (w := 29302) (by decide) (by decide))
    have hPrefix : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedFirst
            (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
            29302 plattFirstLaterFuel)
          58603 k)
        (58603 + k - 1) :=
      rootScanFrom_primeTable (fuel := k) hWindows
        (w := 58603) (by decide) (by decide)
    have hRoom := roomForStep_of_primeTable (c := plattAlignedFirst)
      (bound := 58603 + k - 1) (n := 58603 + k)
      (by decide) hPrefix (by omega) (by omega) (by omega)
    simpa [laterBase, crossingBase, plattFirstBootFuel,
      plattFirstLaterFuel, plattAlignedFirst] using hRoom
  case finalLen =>
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedFirst
          (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
          29302 plattFirstLaterFuel)
        58602 := by
      simpa [plattAlignedFirst, plattFirstLaterFuel] using
        (rootLaterWindows_primeTable (c := plattAlignedFirst)
          (fuel := plattFirstLaterFuel) plattFirstCrossPrime
          (w := 29302) (by decide) (by decide))
    have hFinal : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedFirst
            (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
            29302 plattFirstLaterFuel)
          58603 29301)
        87903 := by
      simpa using rootScanFrom_primeTable (fuel := 29301) hWindows
        (w := 58603) (by decide) (by decide)
    have hLen := primeTable_length_eq_primeCount hFinal
    rw [plattPrimeCount_eq] at hLen
    simpa [finalRootTable, laterBase, crossingBase, plattFirstBootFuel,
      plattFirstLaterFuel, plattAlignedFirst, Cfg.tableLen] using hLen

/-- Complete finite evidence for the aligned three-cell tail schedule. -/
theorem plattAlignedTail_finiteEvidence :
    ScheduleFiniteEvidence plattAlignedTail plattBootBound
      plattTailBootFuel plattTailLaterFuel := by
  constructor
  case bootPrime => exact plattBootPrime
  case markBudget => decide
  case bootstrapFit =>
    intro n hn k hk
    have hn' : n < 98 := by simpa [plattTailBootFuel] using hn
    have hk' : k < 3 := by simpa [plattAlignedTail] using hk
    have hInv : PrimeTableInv
        (rootScanMixed plattBootPrimes plattBootBound (1 + n * 3) k)
        (max 296 (1 + n * 3 + k - 1)) := by
      simpa [plattBootBound] using
        (rootScanMixed_primeTable (fuel := k) plattBootPrime
          (w := 1 + n * 3) (by simp [plattBootBound]; omega)
          (by omega) (by decide))
    have hFit := strictFit_of_primeTable (c := plattAlignedTail)
      (by decide) hInv (by omega)
    simpa [plattAlignedTail] using hFit
  case crossingFit =>
    intro k hk
    have hk' : k < 3 := by simpa [plattAlignedTail] using hk
    have hInv : PrimeTableInv
        (rootScanMixed plattBootPrimes plattBootBound 295 k)
        (max 296 (295 + k - 1)) := by
      simpa [plattBootBound] using
        (rootScanMixed_primeTable (fuel := k) plattBootPrime
          (w := 295) (by decide) (by decide) (by decide))
    have hFit := strictFit_of_primeTable (c := plattAlignedTail)
      (by decide) hInv (by omega)
    simpa [crossingBase, plattTailBootFuel, plattAlignedTail] using hFit
  case laterRoom =>
    intro n hn k hk
    have hn' : n < 29201 := by simpa [plattTailLaterFuel] using hn
    have hk' : k < 3 := by simpa [plattAlignedTail] using hk
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedTail
          (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
          298 n)
        (298 + n * 3 - 1) := by
      simpa [plattAlignedTail] using
        (rootLaterWindows_primeTable (c := plattAlignedTail) (fuel := n)
          plattTailCrossPrime (w := 298) (by decide) (by decide))
    have hPrefix : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedTail
            (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
            298 n)
          (298 + n * 3) k)
        (298 + n * 3 + k - 1) :=
      rootScanFrom_primeTable (fuel := k) hWindows
        (w := 298 + n * 3) (by omega) (by omega)
    have hRoom := roomForStep_of_primeTable (c := plattAlignedTail)
      (bound := 298 + n * 3 + k - 1) (n := 298 + n * 3 + k)
      (by decide) hPrefix (by omega) (by omega) (by omega)
    simpa [laterBase, crossingBase, plattTailBootFuel, plattAlignedTail]
      using hRoom
  case finalRoom =>
    intro k hk
    have hk' : k < 3 := by simpa [plattAlignedTail] using hk
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedTail
          (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
          298 plattTailLaterFuel)
        87900 := by
      simpa [plattAlignedTail, plattTailLaterFuel] using
        (rootLaterWindows_primeTable (c := plattAlignedTail)
          (fuel := plattTailLaterFuel) plattTailCrossPrime
          (w := 298) (by decide) (by decide))
    have hPrefix : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedTail
            (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
            298 plattTailLaterFuel)
          87901 k)
        (87901 + k - 1) :=
      rootScanFrom_primeTable (fuel := k) hWindows
        (w := 87901) (by decide) (by decide)
    have hRoom := roomForStep_of_primeTable (c := plattAlignedTail)
      (bound := 87901 + k - 1) (n := 87901 + k)
      (by decide) hPrefix (by omega) (by omega) (by omega)
    simpa [laterBase, crossingBase, plattTailBootFuel,
      plattTailLaterFuel, plattAlignedTail] using hRoom
  case finalLen =>
    have hWindows : PrimeTableInv
        (rootLaterWindows plattAlignedTail
          (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
          298 plattTailLaterFuel)
        87900 := by
      simpa [plattAlignedTail, plattTailLaterFuel] using
        (rootLaterWindows_primeTable (c := plattAlignedTail)
          (fuel := plattTailLaterFuel) plattTailCrossPrime
          (w := 298) (by decide) (by decide))
    have hFinal : PrimeTableInv
        (rootScanFrom
          (rootLaterWindows plattAlignedTail
            (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
            298 plattTailLaterFuel)
          87901 3)
        87903 := by
      simpa using rootScanFrom_primeTable (fuel := 3) hWindows
        (w := 87901) (by decide) (by decide)
    have hLen := primeTable_length_eq_primeCount hFinal
    rw [plattPrimeCount_eq] at hLen
    simpa [finalRootTable, laterBase, crossingBase, plattTailBootFuel,
      plattTailLaterFuel, plattAlignedTail, Cfg.tableLen] using hLen

/-- The exact opening campaign's completed root table contains precisely the
primes through its source-shaped final bound. -/
theorem plattAlignedFirst_finalPrime :
    PrimeTableInv
      (finalRootTable plattAlignedFirst plattBootBound
        plattFirstBootFuel plattFirstLaterFuel)
      (finalRootBound plattAlignedFirst plattFirstBootFuel
        plattFirstLaterFuel) := by
  have hWindows : PrimeTableInv
      (rootLaterWindows plattAlignedFirst
        (crossingTable plattAlignedFirst plattBootBound plattFirstBootFuel)
        29302 plattFirstLaterFuel)
      58602 := by
    simpa [plattAlignedFirst, plattFirstLaterFuel] using
      (rootLaterWindows_primeTable (c := plattAlignedFirst)
        (fuel := plattFirstLaterFuel) plattFirstCrossPrime
        (w := 29302) (by decide) (by decide))
  have hFinal : PrimeTableInv
      (rootScanFrom
        (rootLaterWindows plattAlignedFirst
          (crossingTable plattAlignedFirst plattBootBound
            plattFirstBootFuel)
          29302 plattFirstLaterFuel)
        58603 29301)
      87903 := by
    simpa using rootScanFrom_primeTable (fuel := 29301) hWindows
      (w := 58603) (by decide) (by decide)
  simpa [finalRootTable, finalRootBound, laterBase, crossingBase,
    plattFirstBootFuel, plattFirstLaterFuel, plattAlignedFirst] using hFinal

/-- The exact tail campaign reconstructs the same complete prime table and
final bound with its three-cell root windows. -/
theorem plattAlignedTail_finalPrime :
    PrimeTableInv
      (finalRootTable plattAlignedTail plattBootBound
        plattTailBootFuel plattTailLaterFuel)
      (finalRootBound plattAlignedTail plattTailBootFuel
        plattTailLaterFuel) := by
  have hWindows : PrimeTableInv
      (rootLaterWindows plattAlignedTail
        (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
        298 plattTailLaterFuel)
      87900 := by
    simpa [plattAlignedTail, plattTailLaterFuel] using
      (rootLaterWindows_primeTable (c := plattAlignedTail)
        (fuel := plattTailLaterFuel) plattTailCrossPrime
        (w := 298) (by decide) (by decide))
  have hFinal : PrimeTableInv
      (rootScanFrom
        (rootLaterWindows plattAlignedTail
          (crossingTable plattAlignedTail plattBootBound plattTailBootFuel)
          298 plattTailLaterFuel)
        87901 3)
      87903 := by
    simpa using rootScanFrom_primeTable (fuel := 3) hWindows
      (w := 87901) (by decide) (by decide)
  simpa [finalRootTable, finalRootBound, laterBase, crossingBase,
    plattTailBootFuel, plattTailLaterFuel, plattAlignedTail] using hFinal

/-- The opening literal configuration now has a complete production schedule
whose only finite admissions are the two named CompCert return receipts. -/
theorem plattAlignedFirst_productionSchedule :
    ProductionCoreSchedule plattAlignedFirst plattBootBound
      plattFirstBootFuel plattFirstLaterFuel plattFirstMainFuel
      plattFirstDelta :=
  plattAlignedFirst_schedule plattAlignedFirst_finiteEvidence

/-- The tail literal configuration has the corresponding complete production
schedule. -/
theorem plattAlignedTail_productionSchedule :
    ProductionCoreSchedule plattAlignedTail plattBootBound
      plattTailBootFuel plattTailLaterFuel plattTailMainFuel
      plattTailDelta :=
  plattAlignedTail_schedule plattAlignedTail_finiteEvidence

end LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
