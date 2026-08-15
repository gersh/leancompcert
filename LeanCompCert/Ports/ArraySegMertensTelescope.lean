import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Symbolic Mertens telescope for the complete live residue

The first two instructions of `mertensLiveResidue` update the biased Mertens
word.  This file proves their exact ordinary-arithmetic meaning, frames the
rest of the complete emitted residue, and telescopes arbitrary schedules.
No production sieve or schedule is evaluated by Lean.
-/

namespace LeanCompCert.Ports.ArraySegMertensTelescope

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve

def mBlock : List Instr :=
  [ .binop 101 .add (.reg rM) (.reg 79)
  , .binop rM .sub (.reg 101) (.reg 80) ]

theorem live_m_slice_eq (bNum bDen : Nat) :
    (mertensLiveResidue bNum bDen).take 2 = lift mBlock := by rfl

private theorem addStage_run (index : Nat) (s : RegState) (m pos : Nat)
    (hm : s rM = m) (hpos : s 79 = pos) (hsum : m + pos < M) :
    (srun index s [.binop 101 .add (.reg rM) (.reg 79)]) 101 = m + pos := by
  change (s rM + s 79) % M = m + pos
  rw [hm, hpos, Nat.mod_eq_of_lt hsum]

private theorem subStage_run (index : Nat) (s : RegState) (a neg : Nat)
    (ha : s 101 = a) (hneg : s 80 = neg)
    (haM : a < M) (hnegM : neg < M) (hle : neg ≤ a) :
    (srun index s [.binop rM .sub (.reg 101) (.reg 80)]) rM = a - neg := by
  have hsub : (a + (M - neg)) % M = a - neg := by
    rw [show a + (M - neg) = M + (a - neg) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  change (s 101 + (M - s 80)) % M = a - neg
  rw [ha, hneg, hsub]

/-- Exact ordinary semantics of the first two live instructions. -/
theorem mBlock_run_main_nowrap (index : Nat) (s : RegState)
    (m pos neg : Nat) (hm : s rM = m) (hpos : s 79 = pos)
    (hneg : s 80 = neg) (hsum : m + pos < M)
    (hnegM : neg < M) (hle : neg ≤ m + pos) :
    (srun index s mBlock) rM = m + pos - neg := by
  let added := srun index s [.binop 101 .add (.reg rM) (.reg 79)]
  have ha := addStage_run index s m pos hm hpos hsum
  have haneg : added 80 = neg :=
    (srun_frame index 80 [.binop 101 .add (.reg rM) (.reg 79)]
      (by decide) s).trans hneg
  have hs := subStage_run index added (m + pos) neg ha haneg hsum hnegM hle
  rw [show mBlock =
      [.binop 101 .add (.reg rM) (.reg 79)] ++
        [.binop rM .sub (.reg 101) (.reg 80)] by rfl,
    srun_append]
  exact hs

def afterM (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).drop 2

theorem mertensLiveResidue_eq_m_decomp (bNum bDen : Nat) :
    mertensLiveResidue bNum bDen = lift mBlock ++ afterM bNum bDen := by
  rw [afterM, ← live_m_slice_eq]
  exact (List.take_append_drop 2 (mertensLiveResidue bNum bDen)).symm

/-- The complete live residue performs the exact Mertens update; its suffix
only reads the resulting word. -/
theorem mertensLiveResidue_m_main_nowrap
    (bNum bDen index : Nat) (s : AState) (m pos neg : Nat)
    (hm : s.regs rM = m) (hpos : s.regs 79 = pos)
    (hneg : s.regs 80 = neg) (hsum : m + pos < M)
    (hnegM : neg < M) (hle : neg ≤ m + pos) :
    (arun index s (mertensLiveResidue bNum bDen)).regs rM =
      m + pos - neg := by
  let updated := arun index s (lift mBlock)
  have hu : updated.regs rM = m + pos - neg := by
    change (arun index s (lift mBlock)).regs rM = _
    rw [arun_lift_regs]
    exact mBlock_run_main_nowrap index s.regs m pos neg hm hpos hneg
      hsum hnegM hle
  have hout : (arun index updated (afterM bNum bDen)).regs rM =
      m + pos - neg :=
    (arun_frame index rM (afterM bNum bDen) (by rfl) updated).trans hu
  rw [mertensLiveResidue_eq_m_decomp, arun_append]
  exact hout

structure MDatum where
  index : Nat
  pos : Nat
  neg : Nat

structure MInvariant (value : Int) (s : AState) : Prop where
  value_eq : Int.ofNat (s.regs rM) - Int.ofNat mertensBias = value

structure MStepReady (d : MDatum) (s : AState) : Prop where
  pos_eq : s.regs 79 = d.pos
  neg_eq : s.regs 80 = d.neg
  sum_lt : s.regs rM + d.pos < M
  neg_lt : d.neg < M
  neg_le : d.neg ≤ s.regs rM + d.pos

def runLiveM (bNum bDen : Nat) : List MDatum → AState → AState
  | [], s => s
  | d :: ds, s => runLiveM bNum bDen ds
      (arun d.index s (mertensLiveResidue bNum bDen))

def MTraceReady (bNum bDen : Nat) : List MDatum → AState → Prop
  | [], _ => True
  | d :: ds, s =>
      MStepReady d s ∧ MTraceReady bNum bDen ds
        (arun d.index s (mertensLiveResidue bNum bDen))

theorem mertensLiveResidue_preserves_m_invariant
    (bNum bDen : Nat) (value : Int) (d : MDatum) (s : AState)
    (hinv : MInvariant value s) (h : MStepReady d s) :
    MInvariant (value + d.pos - d.neg)
      (arun d.index s (mertensLiveResidue bNum bDen)) := by
  have hout := mertensLiveResidue_m_main_nowrap bNum bDen d.index s
    (s.regs rM) d.pos d.neg rfl h.pos_eq h.neg_eq h.sum_lt h.neg_lt h.neg_le
  constructor
  rw [hout]
  change (↑(s.regs rM + d.pos - d.neg) : Int) -
    (↑mertensBias : Int) = value + (↑d.pos : Int) - (↑d.neg : Int)
  rw [Int.ofNat_sub h.neg_le]
  push_cast
  have hvalue : (↑(s.regs rM) : Int) - (↑mertensBias : Int) = value :=
    hinv.value_eq
  omega

/-- Whole-run signed-prefix invariant for the complete emitted residue. -/
theorem runLiveM_invariant
    (bNum bDen : Nat) (value : Int) (ds : List MDatum) (s : AState)
    (hinv : MInvariant value s) (htrace : MTraceReady bNum bDen ds s) :
    MInvariant
      (value + (ds.map (fun d => (d.pos : Int))).sum -
        (ds.map (fun d => (d.neg : Int))).sum)
      (runLiveM bNum bDen ds s) := by
  induction ds generalizing value s with
  | nil => simpa [runLiveM] using hinv
  | cons d ds ih =>
      have hstep := mertensLiveResidue_preserves_m_invariant
        bNum bDen value d s hinv htrace.1
      have htail := ih (value := value + d.pos - d.neg)
        (s := arun d.index s (mertensLiveResidue bNum bDen)) hstep htrace.2
      change MInvariant
        (value + ((d.pos : Int) + (ds.map (fun d => (d.pos : Int))).sum) -
          ((d.neg : Int) + (ds.map (fun d => (d.neg : Int))).sum))
        (runLiveM bNum bDen ds
          (arun d.index s (mertensLiveResidue bNum bDen)))
      have hvalue :
          value + (d.pos : Int) - (d.neg : Int) +
              (ds.map (fun d => (d.pos : Int))).sum -
              (ds.map (fun d => (d.neg : Int))).sum =
            value + ((d.pos : Int) + (ds.map (fun d => (d.pos : Int))).sum) -
              ((d.neg : Int) + (ds.map (fun d => (d.neg : Int))).sum) := by
        omega
      rw [← hvalue]
      exact htail

#print axioms live_m_slice_eq
#print axioms mBlock_run_main_nowrap
#print axioms mertensLiveResidue_m_main_nowrap
#print axioms mertensLiveResidue_preserves_m_invariant
#print axioms runLiveM_invariant

end LeanCompCert.Ports.ArraySegMertensTelescope
