import LeanCompCert.Ports.ArraySegSquarefreeAccumulator
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Symbolic whole-run telescope for the CDEM squarefree accumulators

The live segmented residue maintains

* `Q`, the squarefree count, and
* `G = gBias + Q * 2^cdemScale - cdemC * n`.

`qgBlock_run_main_nowrap` proves one actual emitted five-instruction update.
This file proves preservation of that invariant and composes it over an
arbitrary list of updates.  The list is never evaluated by Lean, so the proof
cost is independent of the production endpoint.
-/

namespace LeanCompCert.Ports.ArraySegSquarefreeTelescope

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegSquarefreeAccumulator

/-- One scheduled main-phase residue update. -/
structure QGDatum where
  index : Nat
  squarefree : Nat

/-- Exact mathematical meaning of the two live accumulator words after `n`
main-phase updates.  The inequality records that the biased subtraction is
an ordinary natural subtraction rather than an underflow convention. -/
structure QGInvariant (n q : Nat) (s : RegState) : Prop where
  q_eq : s rQ = q
  g_eq : s rG = gBias + q * 2 ^ cdemScale - n * cdemC
  bias_le : n * cdemC ≤ gBias + q * 2 ^ cdemScale

/-- Fixed-width obligations at one actual pre-state. -/
structure QGStepReady (d : QGDatum) (s : RegState) : Prop where
  squarefree_eq : s 81 = d.squarefree
  gate_eq : s 133 = 1
  q_lt : s rQ + d.squarefree < M
  shift_lt : d.squarefree * 2 ^ cdemScale < M
  coefficient_le : cdemC ≤ s rG + d.squarefree * 2 ^ cdemScale
  g_lt : s rG + d.squarefree * 2 ^ cdemScale < M

/-- Execute the literal `Q,G` slice for a symbolic schedule. -/
def runQG : List QGDatum → RegState → RegState
  | [], s => s
  | d :: ds, s => runQG ds (srun d.index s qgBlock)

/-- Every scheduled update satisfies its guards at its actual pre-state. -/
def QGTraceReady : List QGDatum → RegState → Prop
  | [], _ => True
  | d :: ds, s =>
      QGStepReady d s ∧ QGTraceReady ds (srun d.index s qgBlock)

/-- One actual emitted update preserves the source accumulator invariant. -/
theorem qgBlock_preserves_invariant
    (n q : Nat) (d : QGDatum) (s : RegState)
    (hinv : QGInvariant n q s) (h : QGStepReady d s) :
    QGInvariant (n + 1) (q + d.squarefree) (srun d.index s qgBlock) := by
  have hq_lt : q + d.squarefree < M := by
    rw [← hinv.q_eq]
    exact h.q_lt
  have hrun := qgBlock_run_main_nowrap d.index s q d.squarefree (s rG)
    hinv.q_eq h.squarefree_eq rfl h.gate_eq hq_lt h.shift_lt
    h.coefficient_le h.g_lt
  have hbias : n * cdemC ≤ gBias + q * 2 ^ cdemScale :=
    hinv.bias_le
  refine {
    q_eq := hrun.1
    g_eq := ?_
    bias_le := ?_
  }
  · calc
      (srun d.index s qgBlock) rG =
          s rG + d.squarefree * 2 ^ cdemScale - cdemC := hrun.2
      _ = (gBias + q * 2 ^ cdemScale - n * cdemC) +
          d.squarefree * 2 ^ cdemScale - cdemC := by rw [hinv.g_eq]
      _ = gBias + (q + d.squarefree) * 2 ^ cdemScale -
          (n + 1) * cdemC := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
  · have hcoeff : cdemC ≤ s rG + d.squarefree * 2 ^ cdemScale :=
      h.coefficient_le
    rw [hinv.g_eq] at hcoeff
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- The actual emitted updates preserve the closed `Q,G` formula over any
finite symbolic schedule.  No production list is reduced by the kernel. -/
theorem runQG_invariant
    (n q : Nat) (ds : List QGDatum) (s : RegState)
    (hinv : QGInvariant n q s) (htrace : QGTraceReady ds s) :
    QGInvariant (n + ds.length)
      (q + (ds.map QGDatum.squarefree).sum) (runQG ds s) := by
  induction ds generalizing n q s with
  | nil => simpa [runQG] using hinv
  | cons d ds ih =>
      have hstep := qgBlock_preserves_invariant n q d s hinv htrace.1
      have htail := ih (n := n + 1) (q := q + d.squarefree)
        (s := srun d.index s qgBlock) hstep htrace.2
      simpa only [runQG, List.length_cons, List.map_cons, List.sum_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Register projections of the symbolic telescope, in the form consumed by
campaign receipt bridges. -/
theorem runQG_outputs
    (n q : Nat) (ds : List QGDatum) (s : RegState)
    (hinv : QGInvariant n q s) (htrace : QGTraceReady ds s) :
    (runQG ds s) rQ = q + (ds.map QGDatum.squarefree).sum ∧
      (runQG ds s) rG =
        gBias + (q + (ds.map QGDatum.squarefree).sum) * 2 ^ cdemScale -
          (n + ds.length) * cdemC := by
  have hout := runQG_invariant n q ds s hinv htrace
  exact ⟨hout.q_eq, hout.g_eq⟩

/-! ## The complete live residue -/

def beforeQG (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).take 2

def afterQG (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).drop 7

/-- The five proved instructions are the literal middle slice of the complete
live residue. -/
theorem mertensLiveResidue_eq_qg_decomp (bNum bDen : Nat) :
    mertensLiveResidue bNum bDen =
      beforeQG bNum bDen ++ lift qgBlock ++ afterQG bNum bDen := by
  rw [beforeQG, afterQG]
  change mertensLiveResidue bNum bDen =
    (mertensLiveResidue bNum bDen).take 2 ++
      qgBlock.map AInstr.scalar ++
        (mertensLiveResidue bNum bDen).drop 7
  rw [← live_qg_slice_eq]
  let xs := mertensLiveResidue bNum bDen
  change xs = xs.take 2 ++ (xs.drop 2).take 5 ++ xs.drop 7
  calc
    xs = xs.take 2 ++ xs.drop 2 := (List.take_append_drop 2 xs).symm
    _ = xs.take 2 ++ ((xs.drop 2).take 5 ++ (xs.drop 2).drop 5) := by
      congr 1
    _ = xs.take 2 ++ (xs.drop 2).take 5 ++ xs.drop 7 := by
      rw [List.drop_drop]
      rfl

/-- One complete emitted live residue has exactly the proved `Q,G` update;
all instructions before and after the literal slice frame both accumulators. -/
theorem mertensLiveResidue_qg_main_nowrap
    (bNum bDen index : Nat) (s : AState) (q squarefree g : Nat)
    (hq : s.regs rQ = q) (hsq : s.regs 81 = squarefree)
    (hg : s.regs rG = g) (hgate : s.regs 133 = 1)
    (hqM : q + squarefree < M)
    (hshiftM : squarefree * 2 ^ cdemScale < M)
    (hcoeffLe : cdemC ≤ g + squarefree * 2 ^ cdemScale)
    (hgM : g + squarefree * 2 ^ cdemScale < M) :
    let out := arun index s (mertensLiveResidue bNum bDen)
    out.regs rQ = q + squarefree ∧
      out.regs rG = g + squarefree * 2 ^ cdemScale - cdemC := by
  let before := arun index s (beforeQG bNum bDen)
  let middle := arun index before (lift qgBlock)
  have hbQ : before.regs rQ = q :=
    (arun_frame index rQ (beforeQG bNum bDen) (by rfl) s).trans hq
  have hbSq : before.regs 81 = squarefree :=
    (arun_frame index 81 (beforeQG bNum bDen) (by rfl) s).trans hsq
  have hbG : before.regs rG = g :=
    (arun_frame index rG (beforeQG bNum bDen) (by rfl) s).trans hg
  have hbGate : before.regs 133 = 1 :=
    (arun_frame index 133 (beforeQG bNum bDen) (by rfl) s).trans hgate
  have hm := qgBlock_run_main_nowrap index before.regs q squarefree g
    hbQ hbSq hbG hbGate hqM hshiftM hcoeffLe hgM
  have hmQ : middle.regs rQ = q + squarefree := by
    change (arun index before (lift qgBlock)).regs rQ = _
    rw [arun_lift_regs]
    exact hm.1
  have hmG : middle.regs rG =
      g + squarefree * 2 ^ cdemScale - cdemC := by
    change (arun index before (lift qgBlock)).regs rG = _
    rw [arun_lift_regs]
    exact hm.2
  have haQ : (arun index middle (afterQG bNum bDen)).regs rQ =
      q + squarefree :=
    (arun_frame index rQ (afterQG bNum bDen) (by rfl) middle).trans hmQ
  have haG : (arun index middle (afterQG bNum bDen)).regs rG =
      g + squarefree * 2 ^ cdemScale - cdemC :=
    (arun_frame index rG (afterQG bNum bDen) (by rfl) middle).trans hmG
  rw [mertensLiveResidue_eq_qg_decomp, arun_append, arun_append]
  exact ⟨haQ, haG⟩

structure LiveQGInvariant (n q : Nat) (s : AState) : Prop where
  q_eq : s.regs rQ = q
  g_eq : s.regs rG = gBias + q * 2 ^ cdemScale - n * cdemC
  bias_le : n * cdemC ≤ gBias + q * 2 ^ cdemScale

structure LiveQGStepReady (d : QGDatum) (s : AState) : Prop where
  squarefree_eq : s.regs 81 = d.squarefree
  gate_eq : s.regs 133 = 1
  q_lt : s.regs rQ + d.squarefree < M
  shift_lt : d.squarefree * 2 ^ cdemScale < M
  coefficient_le : cdemC ≤ s.regs rG + d.squarefree * 2 ^ cdemScale
  g_lt : s.regs rG + d.squarefree * 2 ^ cdemScale < M

def runLiveQG (bNum bDen : Nat) : List QGDatum → AState → AState
  | [], s => s
  | d :: ds, s => runLiveQG bNum bDen ds
      (arun d.index s (mertensLiveResidue bNum bDen))

def LiveQGTraceReady (bNum bDen : Nat) : List QGDatum → AState → Prop
  | [], _ => True
  | d :: ds, s =>
      LiveQGStepReady d s ∧ LiveQGTraceReady bNum bDen ds
        (arun d.index s (mertensLiveResidue bNum bDen))

theorem mertensLiveResidue_preserves_qg_invariant
    (bNum bDen n q : Nat) (d : QGDatum) (s : AState)
    (hinv : LiveQGInvariant n q s) (h : LiveQGStepReady d s) :
    LiveQGInvariant (n + 1) (q + d.squarefree)
      (arun d.index s (mertensLiveResidue bNum bDen)) := by
  have hqM : q + d.squarefree < M := by
    rw [← hinv.q_eq]
    exact h.q_lt
  have hrun := mertensLiveResidue_qg_main_nowrap bNum bDen d.index s q
    d.squarefree (s.regs rG) hinv.q_eq h.squarefree_eq rfl h.gate_eq
    hqM h.shift_lt h.coefficient_le h.g_lt
  have hbias : n * cdemC ≤ gBias + q * 2 ^ cdemScale := hinv.bias_le
  refine { q_eq := hrun.1, g_eq := ?_, bias_le := ?_ }
  · calc
      _ = s.regs rG + d.squarefree * 2 ^ cdemScale - cdemC := hrun.2
      _ = (gBias + q * 2 ^ cdemScale - n * cdemC) +
          d.squarefree * 2 ^ cdemScale - cdemC := by rw [hinv.g_eq]
      _ = gBias + (q + d.squarefree) * 2 ^ cdemScale -
          (n + 1) * cdemC := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
  · have hcoeff : cdemC ≤ s.regs rG +
        d.squarefree * 2 ^ cdemScale := h.coefficient_le
    rw [hinv.g_eq] at hcoeff
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Whole-run induction for the complete live emitted residue.  The theorem
is symbolic in the schedule and therefore does not execute the campaign. -/
theorem runLiveQG_invariant
    (bNum bDen n q : Nat) (ds : List QGDatum) (s : AState)
    (hinv : LiveQGInvariant n q s)
    (htrace : LiveQGTraceReady bNum bDen ds s) :
    LiveQGInvariant (n + ds.length)
      (q + (ds.map QGDatum.squarefree).sum) (runLiveQG bNum bDen ds s) := by
  induction ds generalizing n q s with
  | nil => simpa [runLiveQG] using hinv
  | cons d ds ih =>
      have hstep := mertensLiveResidue_preserves_qg_invariant
        bNum bDen n q d s hinv htrace.1
      have htail := ih (n := n + 1) (q := q + d.squarefree)
        (s := arun d.index s (mertensLiveResidue bNum bDen)) hstep htrace.2
      simpa only [runLiveQG, List.length_cons, List.map_cons, List.sum_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

#print axioms qgBlock_preserves_invariant
#print axioms runQG_invariant
#print axioms runQG_outputs
#print axioms mertensLiveResidue_eq_qg_decomp
#print axioms mertensLiveResidue_qg_main_nowrap
#print axioms mertensLiveResidue_preserves_qg_invariant
#print axioms runLiveQG_invariant

end LeanCompCert.Ports.ArraySegSquarefreeTelescope
