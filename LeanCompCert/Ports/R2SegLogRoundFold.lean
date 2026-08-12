import LeanCompCert.Ports.R2SegLogRound
import LeanCompCert.Verified.LogFixedBounds

/-!
# Finite telescope of the relocated `R₂*` logarithm round

The production loop executes one relocated fixed-log block per live round.
This module telescopes any finite list of those literal blocks.  The theorem
is indexed by the number of rounds already completed, which makes it usable
inside a later whole-body schedule invariant without re-associating folds.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.LogFixed

theorem logIter_fst_range (x0 : Nat)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) : ∀ n : Nat,
    B62 ≤ (logIter x0 n).1 ∧ (logIter x0 n).1 < B63 := by
  intro n
  induction n with
  | zero => exact ⟨hxlo, hxhi⟩
  | succ n ih =>
      simpa only [logIter, logStep] using logMant_range ih.1 ih.2

/-- An arbitrary finite continuation of relocated rounds agrees with
`logIter`.  `j` records the rounds represented by the input registers. -/
theorem foldl_logRoundBody_from_iter (indices : List Nat) (s : AState)
    (x0 : Nat) (j : Nat)
    (hx : s.regs rXm = (logIter x0 j).1)
    (ha : s.regs rAa = (logIter x0 j).2)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hcount : j + indices.length ≤ 62) :
    let out := indices.foldl (fun st k => arun k st logRoundBody) s
    out.regs rXm = (logIter x0 (j + indices.length)).1 ∧
      out.regs rAa = (logIter x0 (j + indices.length)).2 ∧
      out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [List.foldl, List.length_nil, Nat.add_zero]
      exact ⟨hx, ha, trivial⟩
  | cons k ks ih =>
      have hj : j < 62 := by
        simp only [List.length_cons] at hcount
        omega
      have hjPow : 2 ^ j ≤ 2 ^ 61 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have haLt := logIter_snd_lt_two_pow x0 j
      have haBound : (logIter x0 j).2 < B62 := by
        have hpow : (2 : Nat) ^ 61 < B62 := by decide
        omega
      have hrange := logIter_fst_range x0 hxlo hxhi j
      let next := arun k s logRoundBody
      have hstep := logRoundBody_arun_of_range k s
        (logIter x0 j).1 (logIter x0 j).2 hx ha
        hrange.1 hrange.2 haBound
      dsimp only at hstep
      have hxNext : next.regs rXm = (logIter x0 (j + 1)).1 := by
        simpa only [next, logIter, logStep] using hstep.1
      have haNext : next.regs rAa = (logIter x0 (j + 1)).2 := by
        simpa only [next, logIter, logStep, Nat.shiftLeft_eq,
          Nat.pow_one, Nat.mul_comm] using hstep.2.1
      have hrest : j + 1 + ks.length ≤ 62 := by
        simp only [List.length_cons] at hcount
        omega
      have hout := ih next (j + 1) hxNext haNext hrest
      dsimp only at hout
      simp only [List.foldl, List.length_cons]
      have hindex : j + 1 + ks.length = j + (ks.length + 1) := by omega
      exact ⟨hout.1.trans (congrArg (fun z => (logIter x0 z).1) hindex),
        hout.2.1.trans (congrArg (fun z => (logIter x0 z).2) hindex),
        hout.2.2.trans hstep.2.2⟩

/-- Starting from the normalized mantissa and a zero accumulator, any list
of at most 62 relocated rounds emits exactly `logFrac`. -/
theorem foldl_logRoundBody (indices : List Nat) (s : AState) (x0 : Nat)
    (hx : s.regs rXm = x0) (ha : s.regs rAa = 0)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hcount : indices.length ≤ 62) :
    let out := indices.foldl (fun st k => arun k st logRoundBody) s
    out.regs rXm = (logIter x0 indices.length).1 ∧
      out.regs rAa = logFrac indices.length x0 ∧ out.arr = s.arr := by
  have h := foldl_logRoundBody_from_iter indices s x0 0
    (by simpa [logIter] using hx) (by simpa [logIter] using ha)
    hxlo hxhi (by simpa using hcount)
  simpa only [Nat.zero_add, logFrac] using h

/-- Production-scale specialization: 24 rounds leave the exact 24-bit
fractional logarithm in `rAa`. -/
theorem foldl_logRoundBody_24 (indices : List Nat) (s : AState) (x0 : Nat)
    (hlen : indices.length = 24)
    (hx : s.regs rXm = x0) (ha : s.regs rAa = 0)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) :
    let out := indices.foldl (fun st k => arun k st logRoundBody) s
    out.regs rXm = (logIter x0 24).1 ∧
      out.regs rAa = logFrac 24 x0 ∧ out.arr = s.arr := by
  simpa only [hlen] using foldl_logRoundBody indices s x0 hx ha hxlo hxhi
    (by omega)

#print axioms foldl_logRoundBody_from_iter
#print axioms logIter_fst_range
#print axioms foldl_logRoundBody
#print axioms foldl_logRoundBody_24

end LeanCompCert.Ports.R2SegSieve
