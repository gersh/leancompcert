import LeanCompCert.Ports.G1215CheckSpec
import LeanCompCert.Ports.G1215CheckProgram

/-!
# Acceptance yields every candidate's check, and the two exact final sums

Layer four of the `G1215Check` port, and the last one that lives upstream.
`Ports/G1215CheckDenote.lean` proved that the program denotes the
epilogue-corrected good flag of the flat `gRound` fold;
`Ports/G1215CheckSpec.lean` proved that the flat fold re-blocks per candidate
and that one block is one candidate.  This module joins the two:

```text
(gProgram c).denote = some 1 →
  (∀ j < c.len, gAccU c j ≤ ACAP ∧ gAccL c j ≤ ACAP ∧
     candPass c (c.lo + j) (gAccU c j) (gAccL c j) = true) ∧
  gAccU c (c.len - 1) ≤ c.finU ∧ c.finL ≤ gAccL c (c.len - 1)
```

The good flag is only ever multiplied by `0/1` quantities, so a `1` at the end
forces a `1` at every block *and* at both of the epilogue's final-sum tests —
which is the one thing this port owes that the sibling `GFoldCheckSpec` does
not, its epilogue being empty.  The two accumulator caps come from the
`capOK` bit that a firing check re-tests, and they are what makes the `% M` in
`bAccU`/`bAccL` a no-op.

Nothing here evaluates a fold and nothing here is a certificate.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

set_option maxRecDepth 4000

/-! ## §7 From acceptance to the rows -/

/-- A check that fires re-tests **both** running caps. -/
theorem hitOf_cap (c : Params) (n b accU accL xU kU xL kL : Nat)
    (h : hitOf c n b accU accL xU kU xL kL = 1) :
    accU ≤ ACAP ∧ accL ≤ ACAP := by
  refine ⟨?_, ?_⟩
  · by_cases hcap : accU ≤ ACAP
    · exact hcap
    · exact absurd (by simpa only [hitOf, if_neg hcap, Nat.zero_mul] using h)
        (by decide)
  · by_cases hcap : accL ≤ ACAP
    · exact hcap
    · exact absurd
        (by simpa only [hitOf, if_neg hcap, Nat.mul_zero, Nat.zero_mul] using h)
        (by decide)

theorem hitAt_cap (c : Params) (n i accU accL : Nat)
    (h : hitAt c n i accU accL = 1) : accU ≤ ACAP ∧ accL ≤ ACAP :=
  hitOf_cap c n (i + 1) accU accL _ _ _ _ h

/-- The exact upper accumulator **before** candidate `j`. -/
def accUBefore (c : Params) (j : Nat) : Nat :=
  (List.range j).foldl (fun a i => a + gTermU (c.tdiv + 1) (c.lo + i)) 0

/-- The exact lower accumulator **before** candidate `j`. -/
def accLBefore (c : Params) (j : Nat) : Nat :=
  (List.range j).foldl (fun a i => a + gTermL (c.tdiv + 1) (c.lo + i)) 0

theorem accUBefore_succ (c : Params) (j : Nat) :
    accUBefore c (j + 1) = accUBefore c j + gTermU (c.tdiv + 1) (c.lo + j) := by
  unfold accUBefore
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem accLBefore_succ (c : Params) (j : Nat) :
    accLBefore c (j + 1) = accLBefore c j + gTermL (c.tdiv + 1) (c.lo + j) := by
  unfold accLBefore
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem gAccU_eq_accUBefore (c : Params) (j : Nat) :
    gAccU c j = accUBefore c (j + 1) := rfl

theorem gAccL_eq_accLBefore (c : Params) (j : Nat) :
    gAccL c j = accLBefore c (j + 1) := rfl

/-- The per-candidate fold of blocks. -/
def blockFold (c : Params) (j : Nat) : Vals :=
  (List.range j).foldl (BlockedFold.block c.R (fun v k => gRound c k v))
    (initVals c)

theorem blockFold_succ (c : Params) (j : Nat) :
    blockFold c (j + 1) =
      BlockedFold.block c.R (fun v k => gRound c k v) (blockFold c j) j := by
  unfold blockFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Both accumulators stay words.  The two are proved together because
`block_eq_candidate_lt` needs both to describe one block. -/
theorem blockFold_word (c : Params) (hc : c.Sane) :
    ∀ j, (blockFold c j).accU < M ∧ (blockFold c j).accL < M := by
  intro j
  induction j with
  | zero => exact ⟨(by decide : (0:Nat) < M), (by decide : (0:Nat) < M)⟩
  | succ j ih =>
      obtain ⟨hU, hL⟩ := ih
      obtain ⟨_, _, _, hb⟩ := block_eq_candidate_lt c hc j (blockFold c j) hU hL
      rw [blockFold_succ, hb]
      exact ⟨Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos⟩

theorem blockFold_good_succ (c : Params) (hc : c.Sane) (j : Nat) :
    (blockFold c (j + 1)).good =
      (blockFold c j).good *
        orFold c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
          (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax := by
  obtain ⟨hU, hL⟩ := blockFold_word c hc j
  obtain ⟨_, _, _, hb⟩ := block_eq_candidate_lt c hc j (blockFold c j) hU hL
  rw [blockFold_succ, hb]

theorem blockFold_accU_succ (c : Params) (hc : c.Sane) (j : Nat) :
    (blockFold c (j + 1)).accU = bAccU c (c.lo + j) (blockFold c j).accU := by
  obtain ⟨hU, hL⟩ := blockFold_word c hc j
  obtain ⟨_, _, _, hb⟩ := block_eq_candidate_lt c hc j (blockFold c j) hU hL
  rw [blockFold_succ, hb]

theorem blockFold_accL_succ (c : Params) (hc : c.Sane) (j : Nat) :
    (blockFold c (j + 1)).accL = bAccL c (c.lo + j) (blockFold c j).accL := by
  obtain ⟨hU, hL⟩ := blockFold_word c hc j
  obtain ⟨_, _, _, hb⟩ := block_eq_candidate_lt c hc j (blockFold c j) hU hL
  rw [blockFold_succ, hb]

/-- The good flag is a bit. -/
theorem blockFold_good_le (c : Params) (hc : c.Sane) :
    ∀ j, (blockFold c j).good ≤ 1 := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
      rw [blockFold_good_succ c hc j]
      have h1 := orFold_le c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
        (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax
      have h2 : (blockFold c j).good *
          orFold c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
            (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax
          ≤ 1 * 1 := Nat.mul_le_mul ih h1
      omega

/-- The good flag never recovers. -/
theorem blockFold_good_anti (c : Params) (hc : c.Sane) :
    ∀ d j, (blockFold c (j + d)).good ≤ (blockFold c j).good := by
  intro d
  induction d with
  | zero => intro j; exact Nat.le_refl _
  | succ d ih =>
      intro j
      have h1 : (blockFold c (j + (d + 1))).good =
          (blockFold c (j + d)).good *
            orFold c (c.lo + (j + d))
              (bAccU c (c.lo + (j + d)) (blockFold c (j + d)).accU)
              (bAccL c (c.lo + (j + d)) (blockFold c (j + d)).accL) c.bmax := by
        rw [show j + (d + 1) = (j + d) + 1 from rfl]
        exact blockFold_good_succ c hc (j + d)
      have h2 := orFold_le c (c.lo + (j + d))
        (bAccU c (c.lo + (j + d)) (blockFold c (j + d)).accU)
        (bAccL c (c.lo + (j + d)) (blockFold c (j + d)).accL) c.bmax
      have h3 := ih j
      have h4 : (blockFold c (j + d)).good *
          orFold c (c.lo + (j + d))
            (bAccU c (c.lo + (j + d)) (blockFold c (j + d)).accU)
            (bAccL c (c.lo + (j + d)) (blockFold c (j + d)).accL) c.bmax
          ≤ (blockFold c (j + d)).good * 1 := Nat.mul_le_mul_left _ h2
      rw [Nat.mul_one] at h4
      omega

/-- Every candidate's disjunction fires. -/
theorem orFold_of_good (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j < c.len →
      orFold c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
        (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax = 1 := by
  intro j hj
  have hgs := blockFold_good_succ c hc j
  have hmono := blockFold_good_anti c hc (c.len - (j + 1)) (j + 1)
  rw [show j + 1 + (c.len - (j + 1)) = c.len by omega] at hmono
  have h1 := orFold_le c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
    (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax
  rcases (show orFold c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
      (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax = 0 ∨
      orFold c (c.lo + j) (bAccU c (c.lo + j) (blockFold c j).accU)
      (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax = 1
      by omega) with h0 | h1'
  · rw [h0, Nat.mul_zero] at hgs
    omega
  · exact h1'

/-- Every candidate's accumulators are under the running cap. -/
theorem blockFold_acc_le (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j ≤ c.len →
      (blockFold c j).accU ≤ ACAP ∧ (blockFold c j).accL ≤ ACAP := by
  intro j
  induction j with
  | zero => intro _; exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ j ih =>
      intro hj
      have h1 := orFold_of_good c hc hgood j (by omega)
      obtain ⟨i, _, hi⟩ := orFold_extract c (c.lo + j)
        (bAccU c (c.lo + j) (blockFold c j).accU)
        (bAccL c (c.lo + j) (blockFold c j).accL) c.bmax h1
      obtain ⟨hcU, hcL⟩ := hitAt_cap c (c.lo + j) i _ _ hi
      rw [blockFold_accU_succ c hc j, blockFold_accL_succ c hc j]
      exact ⟨hcU, hcL⟩

/-- Every candidate's accumulators are the exact `Nat` sums. -/
theorem blockFold_acc_eq (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j ≤ c.len →
      (blockFold c j).accU = accUBefore c j ∧
      (blockFold c j).accL = accLBefore c j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨iU, iL⟩ := ih (by omega)
      obtain ⟨cU, cL⟩ := blockFold_acc_le c hc hgood j (by omega)
      have hlo : 1 ≤ c.lo + j := by have := hc.loPos; omega
      refine ⟨?_, ?_⟩
      · rw [blockFold_accU_succ c hc j, bAccU_eq c (c.lo + j) _ hlo cU, iU,
          accUBefore_succ]
      · rw [blockFold_accL_succ c hc j, bAccL_eq c (c.lo + j) _ hlo cL, iL,
          accLBefore_succ]

/-- A product of three bits is `1` only if each is. -/
private theorem three_bits_one {a b d : Nat} (ha : a ≤ 1) (hb : b ≤ 1)
    (hd : d ≤ 1) (h : a * (b * d) = 1) : a = 1 ∧ b = 1 ∧ d = 1 := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;>
    simp_all

/-- **Acceptance yields every candidate's check, and the two final sums.** -/
theorem rows_of_denote (c : Params) (hc : c.Sane)
    (h : (gProgram c).denote = some 1) :
    (∀ j, j < c.len →
        gAccU c j ≤ ACAP ∧ gAccL c j ≤ ACAP ∧
          candPass c (c.lo + j) (gAccU c j) (gAccL c j) = true) ∧
      gAccU c (c.len - 1) ≤ c.finU ∧ c.finL ≤ gAccL c (c.len - 1) := by
  have hflat : gFinal c ((List.range (c.len * c.R)).foldl
      (fun v k => gRound c k v) (initVals c)) = 1 :=
    Option.some.inj ((gProgram_denote c hc).symm.trans h)
  have hblk : gFinal c (blockFold c c.len) = 1 := by
    unfold blockFold
    rw [← gFold_blocked c]
    exact hflat
  -- the epilogue's product splits
  obtain ⟨hgood, hU, hL⟩ :=
    three_bits_one (blockFold_good_le c hc c.len) (bitLe _) (bitLe _) hblk
  have hfinU : (blockFold c c.len).accU ≤ c.finU := by
    by_cases hx : (blockFold c c.len).accU ≤ c.finU
    · exact hx
    · rw [if_neg hx] at hU; exact absurd hU (by decide)
  have hfinL : c.finL ≤ (blockFold c c.len).accL := by
    by_cases hx : c.finL ≤ (blockFold c c.len).accL
    · exact hx
    · rw [if_neg hx] at hL; exact absurd hL (by decide)
  have hlen : c.len - 1 + 1 = c.len := by have := hc.lenPos; omega
  obtain ⟨heU, heL⟩ := blockFold_acc_eq c hc hgood c.len (Nat.le_refl _)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hjU, hjL⟩ := blockFold_acc_eq c hc hgood (j + 1) (by omega)
    obtain ⟨hcU, hcL⟩ := blockFold_acc_le c hc hgood (j + 1) (by omega)
    have haU : gAccU c j = (blockFold c (j + 1)).accU := by
      rw [gAccU_eq_accUBefore, hjU]
    have haL : gAccL c j = (blockFold c (j + 1)).accL := by
      rw [gAccL_eq_accLBefore, hjL]
    refine ⟨by rw [haU]; exact hcU, by rw [haL]; exact hcL, ?_⟩
    rw [haU, haL, blockFold_accU_succ c hc j, blockFold_accL_succ c hc j]
    exact candPass_of_orFold c (c.lo + j) _ _ (orFold_of_good c hc hgood j hj)
  · rw [gAccU_eq_accUBefore, hlen, ← heU]
    exact hfinU
  · rw [gAccL_eq_accLBefore, hlen, ← heL]
    exact hfinL

end LeanCompCert.Ports.G1215Check
