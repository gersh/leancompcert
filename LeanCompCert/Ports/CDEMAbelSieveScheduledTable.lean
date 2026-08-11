import LeanCompCert.Ports.CDEMAbelSieveSchedule

/-! # The resident Möbius table after the actual scheduled prefix -/

namespace LeanCompCert.Ports.CDEMAbelSieveScheduledTable

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveTable
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveSchedule

def bodySieveIter (c : Cfg) : Nat → AState → AState
  | 0, st => st
  | i + 1, st => arun i (bodySieveIter c i st) c.body

theorem sieveRank_resync (c : Cfg) (s : SieveState) (machine : AState) :
    sieveRank c (resync s machine) = sieveRank c s := by
  rfl

theorem bodySieveIter_eq_fold (c : Cfg) (count : Nat) (st : AState) :
    bodySieveIter c count st =
      (List.range count).foldl (fun s idx => arun idx s c.body) st := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [bodySieveIter, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ← ih]

theorem sieve_cursor_resync (c : Cfg) (s : SieveState) (machine : AState)
    (hcursor : SieveCursorInv c s)
    (hlive : ∀ j, j ≠ c.sink → machine.arr j = s.arr j) :
    SieveCursorInv c (resync s machine) := by
  refine
    { pjBound := by simpa [resync] using hcursor.pjBound
      primePos := ?_ }
  intro j hj
  have hne : j ≠ c.sink := by
    unfold Cfg.sink Cfg.winBase Cfg.muBase Cfg.k1
    omega
  rw [show (resync s machine).arr j = machine.arr j by rfl,
    hlive j hne]
  exact hcursor.primePos j hj

theorem sieve_table_resync (c : Cfg) (s : SieveState) (machine : AState)
    (htable : SieveTableInv c s)
    (hlive : ∀ j, j ≠ c.sink → machine.arr j = s.arr j) :
    SieveTableInv c (resync s machine) := by
  refine
    { primeCells := ?_
      completed := ?_
      carry := ?_
      nBound := by simpa [resync] using htable.nBound
      nWord := by simpa [resync] using htable.nWord
      mWord := by simpa [resync] using htable.mWord
      parWord := by simpa [resync] using htable.parWord
      sqfWord := by simpa [resync] using htable.sqfWord }
  · intro j hj
    have hne : j ≠ c.sink := by
      unfold Cfg.sink Cfg.winBase Cfg.muBase Cfg.k1
      omega
    rw [show (resync s machine).arr j = machine.arr j by rfl,
      hlive j hne]
    exact htable.primeCells j hj
  · intro d hd
    have hd' : d < s.n := by simpa [resync] using hd
    have hne : d + c.muBase ≠ c.sink := by
      have hn := htable.nBound
      unfold Cfg.sink Cfg.winBase
      omega
    rw [show (resync s machine).arr (d + c.muBase) =
        machine.arr (d + c.muBase) by rfl,
      hlive (d + c.muBase) hne]
    exact htable.completed d hd'
  · intro hpj
    have hpj' : s.pj ≠ 0 := by simpa [resync] using hpj
    simpa [resync] using htable.carry hpj'

theorem sieve_ready_of_rank (c : Cfg) (s : SieveState)
    (hcursor : SieveCursorInv c s) (hrank : sieveRank c s = i)
    (hi : i < c.sieveLen) (hpnM : c.pn < M) (hsinkM : c.sink < M) :
    SieveStepReady c s := by
  have hnBound : s.n < c.k1 := by
    have hmul : s.n * c.pn < c.k1 * c.pn := by
      calc
        s.n * c.pn ≤ sieveRank c s := by simp [sieveRank]
        _ = i := hrank
        _ < c.sieveLen := hi
        _ = c.k1 * c.pn := rfl
    exact Nat.lt_of_mul_lt_mul_right hmul
  refine
    { pjBound := hcursor.pjBound
      primePos := hcursor.primePos s.pj hcursor.pjBound
      pnWord := hpnM
      sinkWord := hsinkM
      addressWord := ?_
      nNextWord := ?_
      pjNextWord := ?_ }
  · calc
      s.n + c.muBase < c.k1 + c.muBase := Nat.add_lt_add_right hnBound _
      _ ≤ c.sink := by unfold Cfg.sink Cfg.winBase; omega
      _ < M := hsinkM
  · have hk1M : c.k1 < M := by
      calc
        c.k1 ≤ c.sink := by
          unfold Cfg.sink Cfg.winBase Cfg.muBase
          omega
        _ < M := hsinkM
    exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hnBound) hk1M
  · exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hcursor.pjBound) hpnM

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bodySieveIter_invariant (c : Cfg) (count : Nat) (machine : AState)
    (model : SieveState) (hrep : SievePreRep model machine)
    (hcursor : SieveCursorInv c model) (htable : SieveTableInv c model)
    (hrank : sieveRank c model = 0) (hcount : count ≤ c.sieveLen)
    (hsieveM : c.sieveLen < M) (hpnM : c.pn < M)
    (hsinkM : c.sink < M) :
    ∃ outModel : SieveState,
      SievePreRep outModel (bodySieveIter c count machine) ∧
      SieveCursorInv c outModel ∧ SieveTableInv c outModel ∧
      sieveRank c outModel = count := by
  induction count with
  | zero =>
      exact ⟨model, hrep, hcursor, htable, hrank⟩
  | succ count ih =>
      have hcountLt : count < c.sieveLen := by omega
      rcases ih (by omega) with ⟨preModel, hpreRep, hpreCursor, hpreTable,
        hpreRank⟩
      have hready := sieve_ready_of_rank c preModel hpreCursor hpreRank
        hcountLt hpnM hsinkM
      let before := bodySieveIter c count machine
      let after := arun count before c.body
      have hstep := body_sieve_state_step c count before preModel hpreRep
        (Nat.lt_trans hcountLt hsieveM) hsieveM hcountLt hready hsinkM
      change SievePreRep (resync (preModel.step c) after) after ∧
          (∀ j, j ≠ c.sink →
            after.arr j = (preModel.step c).arr j) at hstep
      have hcursorStep := sieve_cursor_step c preModel hpreCursor
      have hnlt : preModel.n < c.k1 := by
        have hmul : preModel.n * c.pn < c.k1 * c.pn := by
          calc
            preModel.n * c.pn ≤ sieveRank c preModel := by simp [sieveRank]
            _ = count := hpreRank
            _ < c.sieveLen := hcountLt
            _ = c.k1 * c.pn := rfl
        exact Nat.lt_of_mul_lt_mul_right hmul
      have htableStep := sieve_table_step c preModel hpreTable hpreCursor
        hnlt hready.nNextWord
      have hcursorNext := sieve_cursor_resync c (preModel.step c) after
        hcursorStep hstep.2
      have htableNext := sieve_table_resync c (preModel.step c) after
        htableStep hstep.2
      have hrankNext :
          sieveRank c (resync (preModel.step c) after) = count + 1 := by
        rw [sieveRank_resync,
          sieve_step_rank c preModel hpreCursor.pjBound, hpreRank]
      have hafter : after = bodySieveIter c (count + 1) machine := by
        rfl
      refine ⟨resync (preModel.step c) after, ?_, hcursorNext, htableNext,
        hrankNext⟩
      rw [← hafter]
      exact hstep.1

theorem sieveEntry_preRep (c : Cfg) :
    SievePreRep (initialSieveModel c) (sieveEntry c) := by
  have hseed := sieveEntry_seed c
  have hword := sieveEntry_word c
  exact
    { arr := rfl
      n := hseed.2.1
      pj := hseed.2.2.1
      m := hseed.2.2.2.1
      par := hseed.2.2.2.2.1
      sqf := hseed.2.2.2.2.2
      zero := hseed.1
      regsWord := hword.1
      arrWord := hword.2 }

theorem initialized_scheduled_sieve_full_muCodeFor (c : Cfg)
    (hpnPos : 0 < c.pn) (hpnM : c.pn < M)
    (hsieveM : c.sieveLen < M) (hsinkM : c.sink < M)
    (hprimePos : ∀ p ∈ c.primes, 0 < p)
    (hprimeM : ∀ p ∈ c.primes, p < M)
    (hprimes : c.primes = Ref.muPrimes c.kBound) :
    let out := (List.range c.sieveLen).foldl
      (fun s idx => arun idx s c.body) (sieveEntry c)
    ∀ d, d < c.k1 → out.arr (d + c.muBase) =
      Ref.muCodeFor c.kBound d := by
  rcases bodySieveIter_invariant c c.sieveLen (sieveEntry c)
    (initialSieveModel c) (sieveEntry_preRep c)
    (initialSieveModel_cursor c hpnPos hprimePos hpnM hprimeM)
    (initialSieveModel_table c hpnM hprimeM)
    (by simp [sieveRank, initialSieveModel]) (by omega)
    hsieveM hpnM hsinkM with ⟨finalModel, hfinalRep, hfinalCursor,
      hfinalTable, hfinalRank⟩
  have hn : finalModel.n = c.k1 := by
    have hlo : finalModel.n * c.pn ≤ sieveRank c finalModel := by
      simp [sieveRank]
    have hhi : sieveRank c finalModel < (finalModel.n + 1) * c.pn := by
      simpa [sieveRank, Nat.add_mul, Nat.add_assoc] using
        Nat.add_lt_add_left hfinalCursor.pjBound (finalModel.n * c.pn)
    have hnDiv : sieveRank c finalModel / c.pn = finalModel.n :=
      Nat.div_eq_of_lt_le hlo hhi
    have hkDiv : sieveRank c finalModel / c.pn = c.k1 := by
      rw [hfinalRank]
      change (c.k1 * c.pn) / c.pn = c.k1
      rw [Nat.mul_comm]
      exact Nat.mul_div_right c.k1 hpnPos
    exact hnDiv.symm.trans hkDiv
  have hfold := bodySieveIter_eq_fold c c.sieveLen (sieveEntry c)
  dsimp only
  intro d hd
  rw [← hfold, hfinalRep.arr,
    hfinalTable.completed d (by rw [hn]; exact hd),
    Ref.muCodeFor, ← hprimes]

end LeanCompCert.Ports.CDEMAbelSieveScheduledTable
