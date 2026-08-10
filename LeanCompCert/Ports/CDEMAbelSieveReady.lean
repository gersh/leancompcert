import LeanCompCert.Ports.CDEMAbelSieveTelescope

/-! # Readiness and closed cursor trace for the finite CDEM sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveReady

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSievePrefix
open LeanCompCert.Ports.CDEMAbelSieveTelescope

def sieveRank (c : Cfg) (s : SieveState) : Nat :=
  s.n * c.pn + s.pj

structure SieveCursorInv (c : Cfg) (s : SieveState) : Prop where
  pjBound : s.pj < c.pn
  primePos : ∀ j, j < c.pn → 0 < s.arr j

theorem sieve_step_rank (c : Cfg) (s : SieveState)
    (hpj : s.pj < c.pn) :
    sieveRank c (s.step c) = sieveRank c s + 1 := by
  have hpnPos : 0 < c.pn := by omega
  by_cases hlast : s.pj = c.pn - 1
  · simp [SieveState.step, sieveRank, hlast, Nat.add_mul]
    omega
  · simp [SieveState.step, sieveRank, hlast, Nat.add_assoc]

theorem sieve_cursor_step (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) : SieveCursorInv c (s.step c) := by
  have hpnPos : 0 < c.pn := Nat.lt_of_le_of_lt (Nat.zero_le _) h.pjBound
  by_cases hlast : s.pj = c.pn - 1
  · refine
      { pjBound := by simp [SieveState.step, hlast, hpnPos]
        primePos := ?_ }
    intro j hj
    have hne : j ≠ s.n + c.muBase := by
      unfold Cfg.muBase
      omega
    simpa [SieveState.step, hlast, writeCell, hne] using h.primePos j hj
  · have hpjLe : s.pj + 1 ≤ c.pn := Nat.succ_le_iff.mpr h.pjBound
    have hpjNext : s.pj + 1 < c.pn := by
      rcases Nat.lt_or_eq_of_le hpjLe with hlt | heq
      · exact hlt
      · exact (hlast (Nat.eq_sub_of_add_eq heq)).elim
    refine
      { pjBound := by simpa [SieveState.step, hlast] using hpjNext
        primePos := ?_ }
    intro j hj
    have hne : j ≠ c.sink := by
      unfold Cfg.sink Cfg.winBase Cfg.k1 Cfg.muBase
      omega
    simpa [SieveState.step, hlast, writeCell, hne] using h.primePos j hj

theorem sieve_cursor_iter (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) (count : Nat) :
    SieveCursorInv c (s.iter c count) := by
  induction count with
  | zero => simpa [SieveState.iter] using h
  | succ count ih =>
      simpa [SieveState.iter] using
        sieve_cursor_step c (s.iter c count) ih

theorem sieve_iter_rank (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) (count : Nat) :
    sieveRank c (s.iter c count) = sieveRank c s + count := by
  induction count with
  | zero => simp [SieveState.iter]
  | succ count ih =>
      rw [SieveState.iter, sieve_step_rank c _
        (sieve_cursor_iter c s h count).pjBound, ih]
      omega

theorem sieve_iter_rank_from_zero (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0)
    (count : Nat) :
    sieveRank c (s.iter c count) = count := by
  rw [sieve_iter_rank c s h count]
  simp [sieveRank, hn, hpj]

theorem sieve_iter_ready_from_zero (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0)
    (hpnM : c.pn < M) (hsinkM : c.sink < M)
    (i : Nat) (hi : i < c.sieveLen) :
    SieveStepReady c (s.iter c i) := by
  let t := s.iter c i
  have hinv : SieveCursorInv c t := sieve_cursor_iter c s h i
  have hrank : sieveRank c t = i :=
    sieve_iter_rank_from_zero c s h hn hpj i
  have hmul : t.n * c.pn < c.k1 * c.pn := by
    calc
      t.n * c.pn ≤ sieveRank c t := by simp [sieveRank]
      _ = i := hrank
      _ < c.sieveLen := hi
      _ = c.k1 * c.pn := rfl
  have hnBound : t.n < c.k1 := Nat.lt_of_mul_lt_mul_right hmul
  refine
    { pjBound := hinv.pjBound
      primePos := hinv.primePos t.pj hinv.pjBound
      pnWord := hpnM
      sinkWord := hsinkM
      addressWord := ?_
      nNextWord := ?_
      pjNextWord := ?_ }
  · calc
      t.n + c.muBase < c.k1 + c.muBase :=
        Nat.add_lt_add_right hnBound c.muBase
      _ ≤ c.sink := by
        unfold Cfg.sink Cfg.winBase
        omega
      _ < M := hsinkM
  · have hk1M : c.k1 < M := by
      calc
        c.k1 ≤ c.sink := by
          unfold Cfg.sink Cfg.winBase Cfg.muBase
          omega
        _ < M := hsinkM
    change t.n + 1 < M
    exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hnBound) hk1M
  · exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hinv.pjBound) hpnM

theorem sieveIter_state_refines_from_zero (c : Cfg) (idx count : Nat)
    (machine : AState) (model : SieveState)
    (hrep : SieveStateRep model machine) (hinv : SieveCursorInv c model)
    (hn : model.n = 0) (hpj : model.pj = 0)
    (hpnM : c.pn < M) (hsinkM : c.sink < M)
    (hcount : count ≤ c.sieveLen) :
    SieveStateRep (model.iter c count) (sieveIter c idx count machine) := by
  apply sieveIter_state_refines c idx count machine model hrep
  intro i hi
  exact sieve_iter_ready_from_zero c model hinv hn hpj hpnM hsinkM i
    (Nat.lt_of_lt_of_le hi hcount)

theorem sieve_iter_full_cursors (c : Cfg) (s : SieveState)
    (h : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0) :
    let out := s.iter c c.sieveLen
    out.n = c.k1 ∧ out.pj = 0 := by
  let out := s.iter c c.sieveLen
  have hinv := sieve_cursor_iter c s h c.sieveLen
  have hrank : sieveRank c out = c.sieveLen :=
    sieve_iter_rank_from_zero c s h hn hpj c.sieveLen
  have hpnPos : 0 < c.pn := Nat.lt_of_le_of_lt (Nat.zero_le _) h.pjBound
  have hlo : out.n * c.pn ≤ sieveRank c out := by simp [sieveRank]
  have hhi : sieveRank c out < (out.n + 1) * c.pn := by
    simpa [sieveRank, Nat.add_mul, Nat.add_assoc] using
      Nat.add_lt_add_left hinv.pjBound (out.n * c.pn)
  have hnDiv : sieveRank c out / c.pn = out.n :=
    Nat.div_eq_of_lt_le hlo hhi
  have hkDiv : sieveRank c out / c.pn = c.k1 := by
    rw [hrank]
    change (c.k1 * c.pn) / c.pn = c.k1
    rw [Nat.mul_comm]
    exact Nat.mul_div_right c.k1 hpnPos
  have hnEq : out.n = c.k1 := hnDiv.symm.trans hkDiv
  constructor
  · exact hnEq
  · unfold sieveRank at hrank
    change out.n * c.pn + out.pj = c.k1 * c.pn at hrank
    rw [hnEq] at hrank
    exact Nat.add_left_cancel hrank

end LeanCompCert.Ports.CDEMAbelSieveReady
