import LeanCompCert.Ports.CDEMAbelProductionSieveWindow
import LeanCompCert.Ports.CDEMAbelProductionMarkWindow

/-! # First production CDEM marking-window cell -/

namespace LeanCompCert.Ports.CDEMAbelProductionFirstWindow

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveWindow
open LeanCompCert.Ports.CDEMAbelProductionMarkWindow

private def deltaOneStep (kBound acc d : Nat) : Nat :=
  if 1 % d ≠ 0 then acc
  else let c := Ref.muCodeFor kBound d
    if c = 1 then (acc + 1) % M
    else if c = 2 then (acc + (M - 1)) % M else acc

private theorem deltaOneTail (kBound n : Nat) :
    (List.range' 2 n).foldl (deltaOneStep kBound) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range'_1_concat, List.foldl_append, ih]
      have hm : 1 % (2 + n) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [deltaOneStep, hm]

private theorem dropOneRangeSucc (n : Nat) :
    (List.range (n + 1)).drop 1 = List.range' 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        List.range_succ, List.drop_append_of_le_length]
      · rw [ih, List.range'_1_concat]
        simp [Nat.add_comm]
      · simp

private theorem rangeOneSplit (n : Nat) :
    List.range' 1 (n + 1) = 1 :: List.range' 2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range'_1_concat, ih, List.range'_1_concat]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The pure finite divisor fold at the first key is exactly one. -/
theorem deltaF_one (kBound : Nat) (hk : 0 < kBound) :
    Ref.deltaF kBound 1 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : kBound ≠ 0)
  unfold Ref.deltaF
  rw [show k + 1 + 1 = (k + 1) + 1 by omega,
    dropOneRangeSucc, rangeOneSplit]
  simp only [List.foldl_cons, Nat.mod_self, ne_eq, not_true_eq_false,
    if_false, LeanCompCert.Ports.CDEMAbelMarkPlane.muCodeFor_one]
  rw [show (0 + 1) % M = 1 by decide]
  change (List.range' 2 k).foldl (deltaOneStep (k + 1)) 1 = 1
  exact deltaOneTail (k + 1) k

private def deltaTwoStep (kBound acc d : Nat) : Nat :=
  if 2 % d ≠ 0 then acc
  else let c := Ref.muCodeFor kBound d
    if c = 1 then (acc + 1) % M
    else if c = 2 then (acc + (M - 1)) % M else acc

private theorem deltaTwoTail (kBound acc n : Nat) :
    (List.range' 3 n).foldl (deltaTwoStep kBound) acc = acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range'_1_concat, List.foldl_append, ih]
      have hm : 2 % (3 + n) = 2 := Nat.mod_eq_of_lt (by omega)
      simp [deltaTwoStep, hm]

private theorem rangeTwoSplit (n : Nat) :
    List.range' 1 (n + 2) = 1 :: 2 :: List.range' 3 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        List.range'_1_concat, ih, List.range'_1_concat]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The second pure divisor fold vanishes once the resident table gives the
paper value `mu(2) = -1`.  The long tail is framed symbolically because every
divisor there is larger than two. -/
theorem deltaF_two_of_muCode_two (kBound : Nat) (hk : 2 ≤ kBound)
    (hcode : Ref.muCodeFor kBound 2 = 2) :
    Ref.deltaF kBound 2 = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, kBound = n + 2 := by
    exact ⟨kBound - 2, by omega⟩
  subst kBound
  unfold Ref.deltaF
  rw [show n + 2 + 1 = (n + 2) + 1 by omega,
    dropOneRangeSucc, rangeTwoSplit]
  simp only [List.foldl_cons, Nat.mod_one, ne_eq, not_true_eq_false,
    if_false, LeanCompCert.Ports.CDEMAbelMarkPlane.muCodeFor_one, hcode,
    Nat.reduceEqDiff, if_true]
  rw [show (0 + 1) % M = 1 by decide,
    show (1 + (M - 1)) % M = 0 by decide]
  change (List.range' 3 n).foldl (deltaTwoStep (n + 2)) 0 = 0
  exact deltaTwoTail (n + 2) 0 n

theorem firstCell_of_window (c : Cfg)
    (before after : LeanCompCert.Verified.ArrayState.AState)
    (hwindow : after.arr (0 + c.winBase) =
      (before.arr (0 + c.winBase) + Ref.deltaF c.kBound (1 + 0)) % M)
    (hbefore : before.arr c.winBase = 0)
    (hdelta : Ref.deltaF c.kBound 1 = 1) :
    after.arr c.winBase = 1 := by
  simpa only [Nat.zero_add, hbefore, hdelta,
    show 1 % M = 1 by decide] using hwindow

theorem zeroCell_of_window (before after :
    LeanCompCert.Verified.ArrayState.AState) (addr delta : Nat)
    (hwindow : after.arr addr = (before.arr addr + delta) % M)
    (hbefore : before.arr addr = 0) (hdelta : delta = 0) :
    after.arr addr = 0 := by
  simpa only [hbefore, hdelta, Nat.zero_add, Nat.zero_mod] using hwindow

set_option maxRecDepth 4096 in
/-- The first post-mark window cell is the exact first floor-convolution
increment, hence one. -/
theorem productionAfterMark_first_cell
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.arr productionCfg.winBase = 1 := by
  let out := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  exact firstCell_of_window productionCfg productionAfterSieve out
    (production_full_mark_first_cell hbudget)
    productionAfterSieve_window_zero
    (deltaF_one productionCfg.kBound (by change 0 < 199330; decide))

set_option maxRecDepth 4096 in
/-- Once the finite paper computation for key two is supplied, the complete
production marking prefix installs its exact value in the second resident
window cell. -/
theorem productionAfterMark_second_cell
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.arr (1 + productionCfg.winBase) = 0 := by
  let out := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  exact zeroCell_of_window productionAfterSieve out
    (1 + productionCfg.winBase) (Ref.deltaF productionCfg.kBound (1 + 1))
    (production_full_mark_second_cell hbudget)
    productionAfterSieve_second_window_zero (by simpa only [Nat.reduceAdd])

end LeanCompCert.Ports.CDEMAbelProductionFirstWindow
