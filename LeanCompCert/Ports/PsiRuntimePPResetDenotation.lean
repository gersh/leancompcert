import LeanCompCert.Ports.PsiRuntimePPReset
import LeanCompCert.Verified.ArrayPipeline

/-!
# Exact denotation of the runtime psi prime-power reset

Between consecutive psi shards the resident prime table and the seven carry
cells are shared.  Only the shard-local prime-power pair table and its
permanent cursor sentinel must be empty before the existing generator is run
again.  This file proves that the small compiled reset loop has exactly that
effect.  Its proofs are symbolic in `ppCount`: Lean never evaluates a
production table or shard schedule.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

/-- Static facts making every reset address both a machine word and a valid
cell of the shared array.  The half-open region is
`[ppBase, ppBase + 2 * (ppCount + 1))`; the last pair is the total cursor's
permanent zero sentinel. -/
structure PsiPPResetReady (m : PsiRuntimeMeta) : Prop where
  region_in_array : m.cfg.ppBase + 2 * (m.ppCount + 1) <= m.arrayLen
  region_in_word : m.cfg.ppBase + 2 * (m.ppCount + 1) < M

private theorem reset_addr_lt (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (k : Nat) (hk : k < m.ppCount + 1) :
    k * 2 + m.cfg.ppBase + 1 < M := by
  have := hready.region_in_word
  omega

private theorem reset_addr_array_lt (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (k : Nat) (hk : k < m.ppCount + 1) :
    k * 2 + m.cfg.ppBase + 1 < m.arrayLen := by
  have := hready.region_in_array
  omega

/-- One reset iteration writes zero to exactly its two pair cells. -/
theorem arun_psiPPResetBody_arr (m : PsiRuntimeMeta) (k j : Nat) (s : AState)
    (haddr : k * 2 + m.cfg.ppBase + 1 < M)
    (hz : s.regs rZero = 0) :
    (arun k s (psiPPResetBody m)).arr j =
      if j = k * 2 + m.cfg.ppBase then 0 else
      if j = k * 2 + m.cfg.ppBase + 1 then 0 else s.arr j := by
  have ha0 : k * 2 + m.cfg.ppBase < M := by omega
  have hm0 : (k * 2 + m.cfg.ppBase) % 18446744073709551616 =
      k * 2 + m.cfg.ppBase := by
    apply Nat.mod_eq_of_lt
    simpa [M] using ha0
  have hm1 : (k * 2 + m.cfg.ppBase + 1) % 18446744073709551616 =
      k * 2 + m.cfg.ppBase + 1 := by
    apply Nat.mod_eq_of_lt
    simpa [M] using haddr
  have hz' : s.regs 7 = 0 := by simpa [rZero] using hz
  simp [psiPPResetBody, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, denoteOp, Nat.shiftLeft_eq, M, rZero,
    hm0, hm1, hz']
  by_cases h0 : j = k * 2 + m.cfg.ppBase <;>
    by_cases h1 : j = k * 2 + m.cfg.ppBase + 1 <;> simp [h0, h1]

/-- The loop body does not use its scratch registers to overwrite the seeded
zero register. -/
theorem arun_psiPPResetBody_rZero (m : PsiRuntimeMeta) (k : Nat) (s : AState) :
    (arun k s (psiPPResetBody m)).regs rZero = s.regs rZero := by
  simp [psiPPResetBody, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, denoteOp, rZero]

private theorem fold_reset_exact (m : PsiRuntimeMeta) (ks : List Nat)
    (s : AState) (j : Nat)
    (hbound : forall k, k ∈ ks ->
      k * 2 + m.cfg.ppBase + 1 < M)
    (hz : s.regs rZero = 0) :
    ((ks.foldl (fun st k => arun k st (psiPPResetBody m)) s).arr j =
      if exists k, k ∈ ks /\
          (j = k * 2 + m.cfg.ppBase \/
           j = k * 2 + m.cfg.ppBase + 1) then
        0
      else s.arr j) /\
    (ks.foldl (fun st k => arun k st (psiPPResetBody m)) s).regs rZero = 0 := by
  induction ks generalizing s with
  | nil => simp [hz]
  | cons k ks ih =>
      let s' := arun k s (psiPPResetBody m)
      have hk : k * 2 + m.cfg.ppBase + 1 < M :=
        hbound k (by simp)
      have htail : forall x, x ∈ ks ->
          x * 2 + m.cfg.ppBase + 1 < M := by
        intro x hx
        exact hbound x (by simp [hx])
      have hz' : s'.regs rZero = 0 := by
        simpa [s'] using arun_psiPPResetBody_rZero m k s |>.trans hz
      have hrec := ih s' htail hz'
      constructor
      · simp only [List.foldl_cons]
        rw [hrec.1]
        rw [arun_psiPPResetBody_arr m k j s hk hz]
        by_cases hrest : exists x, x ∈ ks /\
            (j = x * 2 + m.cfg.ppBase \/
             j = x * 2 + m.cfg.ppBase + 1)
        · simp [hrest]
        · by_cases h0 : j = k * 2 + m.cfg.ppBase
          · simp [hrest, h0]
          · by_cases h1 : j = k * 2 + m.cfg.ppBase + 1
            · simp [hrest, h0, h1]
            · simp [hrest, h0, h1]
      · simpa only [List.foldl_cons] using hrec.2

/-- Successful source execution clears every reserved pair. -/
theorem psiPPResetProgram_pair_zero (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (input : Nat -> Nat) (out : AState)
    (hRun : (psiPPResetProgram m).runFromArray input = some out)
    (rank : Nat) (hrank : rank < m.ppCount + 1) :
    out.arr (m.cfg.ppBase + 2 * rank) = 0 /\
      out.arr (m.cfg.ppBase + 2 * rank + 1) = 0 := by
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (psiPPResetProgram m) input out hRun
  have hentryArr :
      (arun 0 (initialAStateWithArray input)
        (psiPPResetProgram m).init).arr = input := by
    simp [psiPPResetProgram, seedRegs, arun, astep, AState.writeReg,
      initialAStateWithArray]
  have hentryZero :
      (arun 0 (initialAStateWithArray input)
        (psiPPResetProgram m).init).regs rZero = 0 := by
    simp [psiPPResetProgram, seedRegs, arun, astep, AState.writeReg,
      initialAStateWithArray, initialState, sdest, sval, denoteOperand,
      M, rZero]
  let entry := arun 0 (initialAStateWithArray input)
    (psiPPResetProgram m).init
  have hfold (j : Nat) := (fold_reset_exact m (List.range (m.ppCount + 1))
    entry j (by
      intro k hk
      exact reset_addr_lt m hready k (List.mem_range.mp hk))
    (by simpa [entry] using hentryZero)).1
  have hout' : out = (List.range (m.ppCount + 1)).foldl
      (fun st k => arun k st (psiPPResetBody m)) entry := by
    simpa [psiPPResetProgram, entry, arun] using hout
  constructor
  · have hex : exists k, k ∈ List.range (m.ppCount + 1) /\
        (m.cfg.ppBase + 2 * rank = k * 2 + m.cfg.ppBase \/
         m.cfg.ppBase + 2 * rank = k * 2 + m.cfg.ppBase + 1) := by
      refine ⟨rank, List.mem_range.mpr hrank, Or.inl ?_⟩
      omega
    rw [hout', hfold, if_pos hex]
  · have hex : exists k, k ∈ List.range (m.ppCount + 1) /\
        (m.cfg.ppBase + 2 * rank + 1 = k * 2 + m.cfg.ppBase \/
         m.cfg.ppBase + 2 * rank + 1 = k * 2 + m.cfg.ppBase + 1) := by
      refine ⟨rank, List.mem_range.mpr hrank, Or.inr ?_⟩
      omega
    rw [hout', hfold, if_pos hex]

/-- Successful source execution frames every cell outside the reset region.
This includes both the resident-prime region below it and all result/carry
cells above it. -/
theorem psiPPResetProgram_arr_frame (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (input : Nat -> Nat) (out : AState)
    (hRun : (psiPPResetProgram m).runFromArray input = some out)
    (j : Nat)
    (houtside : j < m.cfg.ppBase \/
      m.cfg.ppBase + 2 * (m.ppCount + 1) <= j) :
    out.arr j = input j := by
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (psiPPResetProgram m) input out hRun
  let entry := arun 0 (initialAStateWithArray input)
    (psiPPResetProgram m).init
  have hentryArr : entry.arr = input := by
    simp [entry, psiPPResetProgram, seedRegs, arun, astep,
      AState.writeReg, initialAStateWithArray]
  have hentryZero : entry.regs rZero = 0 := by
    simp [entry, psiPPResetProgram, seedRegs, arun, astep,
      AState.writeReg, initialAStateWithArray, initialState,
      sdest, sval, denoteOperand, M, rZero]
  have hfold := (fold_reset_exact m (List.range (m.ppCount + 1))
    entry j (by
      intro k hk
      exact reset_addr_lt m hready k (List.mem_range.mp hk))
    hentryZero).1
  have hout' : out = (List.range (m.ppCount + 1)).foldl
      (fun st k => arun k st (psiPPResetBody m)) entry := by
    simpa [psiPPResetProgram, entry, arun] using hout
  rw [hout', hfold]
  have hnone : ¬ (exists k, k ∈ List.range (m.ppCount + 1) /\
      (j = k * 2 + m.cfg.ppBase \/
       j = k * 2 + m.cfg.ppBase + 1)) := by
    rintro ⟨k, hk, h0 | h1⟩
    · have hk' := List.mem_range.mp hk
      rcases houtside with hlo | hhi <;> omega
    · have hk' := List.mem_range.mp hk
      rcases houtside with hlo | hhi <;> omega
  rw [if_neg hnone, hentryArr]

/-- The explicit readiness proposition also proves that every loop store is
in bounds.  This is the fixed-width/address side condition consumed by an
audited source run; it is independent of any production schedule. -/
theorem psiPPResetProgram_store_in_bounds (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (k : Nat) (hk : k < m.ppCount + 1) :
    k * 2 + m.cfg.ppBase < m.arrayLen /\
      k * 2 + m.cfg.ppBase + 1 < m.arrayLen := by
  have h := reset_addr_array_lt m hready k hk
  omega

/-- The extra reset iteration establishes the permanent `(0,0)` cursor
sentinel from source execution, independently of the caller array. -/
theorem psiPPResetProgram_sentinel_zero (m : PsiRuntimeMeta)
    (hready : PsiPPResetReady m) (input : Nat -> Nat) (out : AState)
    (hRun : (psiPPResetProgram m).runFromArray input = some out) :
    out.arr (m.cfg.ppBase + 2 * m.ppCount) = 0 /\
      out.arr (m.cfg.ppBase + 2 * m.ppCount + 1) = 0 := by
  have h := psiPPResetProgram_pair_zero m hready input out hRun m.ppCount
    (by omega)
  simpa only [Nat.mul_comm m.ppCount 2] using h

#print axioms arun_psiPPResetBody_arr
#print axioms fold_reset_exact
#print axioms psiPPResetProgram_pair_zero
#print axioms psiPPResetProgram_arr_frame
#print axioms psiPPResetProgram_store_in_bounds
#print axioms psiPPResetProgram_sentinel_zero

end LeanCompCert.Ports.PsiSegSieve
