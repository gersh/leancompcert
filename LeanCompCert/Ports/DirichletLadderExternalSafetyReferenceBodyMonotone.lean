import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodySource
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptance

/-! Counter bounds for one literal historical body execution on a live record. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem maxPinnedUpper_pair_word :
    maxPinnedUpper + maxPinnedUpper < M := by decide

theorem historicalBody_machine_bounds
    (c : Cfg) (words : List Nat) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (harray : HistoricalArrayMatches c words s)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hstatic : StaticBounds c) (hidx : idx < c.records)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hprevLast : s.regs rPrevLast ≤ 1)
    (hprevBlk : s.regs rPrevBlk + 1 < M)
    (hNoWrap : n + 25 < M) :
    n ≤ (arun idx s c.bodyBlock).regs rViol ∧
      (arun idx s c.bodyBlock).regs rViol ≤ n + 25 := by
  let loaded := arun idx s (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  have loaded_eq : loaded = arun idx s (historicalLoad c) := rfl
  have early_eq : early = arun idx loaded (historicalEarly c) := rfl
  have hloaded : HistoricalLoaded c words idx s loaded := by
    exact historicalLoad_loaded c words idx s harray hstatic hidx
  have hwordLoaded := arun_word idx (historicalLoad c) s hregs harr
  have hvLoaded : loaded.regs rViol = n := by
    dsimp [loaded]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalLoad c) (by rfl) s]
    exact hv
  let st := refStateOf s
  have hstViol : st.viol = n := by
    simpa [st, refStateOf] using hv
  have hstLast : st.prevLast ≤ 1 := by
    simpa [st, refStateOf] using hprevLast
  have hstBlk : st.prevBlk + 1 < M := by
    simpa [st, refStateOf] using hprevBlk
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := hsafe.2.1
    have hslots := hsafe.2.2.1
    simp only [wordsArray_apply] at hlo hslots
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hslots)
      maxPinnedUpper_pair_word
  have hearly := historicalEarly_viol c words idx s loaded st hloaded rfl
    hwordLoaded.1 hstLast hstBlk hslot (by omega)
  have eLower : n ≤ early.regs rViol := by
    rw [hearly, ← hstViol]
    exact bumps_ge _ _
  have eUpper : early.regs rViol ≤ n + 8 := by
    rw [hearly, ← hstViol]
    have hb := bumps_le_length (earlyConditions words st idx) st.viol
    simpa [earlyConditions] using hb
  have gates := historicalEarly_gate_bits c idx loaded
  change early.regs 33 ≤ 1 ∧ early.regs 34 ≤ 1 ∧ early.regs 48 ≤ 1 at gates
  have post := historicalPostEarly_machine_bounds c idx (early.regs rViol)
    early rfl gates.1 gates.2.1 gates.2.2 (by omega)
  rw [historicalBody_eq_load_early_post, arun_append, arun_append]
  rw [← loaded_eq, ← early_eq]
  constructor <;> omega

theorem historicalEarly_zero_of_body_zero
    (c : Cfg) (words : List Nat) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n)
    (harray : HistoricalArrayMatches c words s)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hstatic : StaticBounds c) (hidx : idx < c.records)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hprevLast : s.regs rPrevLast ≤ 1)
    (hprevBlk : s.regs rPrevBlk + 1 < M)
    (hNoWrap : n + 25 < M)
    (hbody : (arun idx s c.bodyBlock).regs rViol = 0) :
    (arun idx (arun idx s (historicalLoad c))
      (historicalEarly c)).regs rViol = 0 := by
  let loaded := arun idx s (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  have loaded_eq : loaded = arun idx s (historicalLoad c) := rfl
  have early_eq : early = arun idx loaded (historicalEarly c) := rfl
  have hloaded : HistoricalLoaded c words idx s loaded :=
    historicalLoad_loaded c words idx s harray hstatic hidx
  have hwordLoaded := arun_word idx (historicalLoad c) s hregs harr
  have hvLoaded : loaded.regs rViol = n := by
    dsimp [loaded]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalLoad c) (by rfl) s]
    exact hv
  let st := refStateOf s
  have hstViol : st.viol = n := by simpa [st, refStateOf] using hv
  have hstLast : st.prevLast ≤ 1 := by
    simpa [st, refStateOf] using hprevLast
  have hstBlk : st.prevBlk + 1 < M := by
    simpa [st, refStateOf] using hprevBlk
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := hsafe.2.1
    have hslots := hsafe.2.2.1
    simp only [wordsArray_apply] at hlo hslots
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hslots)
      maxPinnedUpper_pair_word
  have hearly := historicalEarly_viol c words idx s loaded st hloaded rfl
    hwordLoaded.1 hstLast hstBlk hslot (by omega)
  have eUpper : early.regs rViol ≤ n + 8 := by
    rw [hearly, ← hstViol]
    have hb := bumps_le_length (earlyConditions words st idx) st.viol
    simpa [earlyConditions] using hb
  have gates := historicalEarly_gate_bits c idx loaded
  change early.regs 33 ≤ 1 ∧ early.regs 34 ≤ 1 ∧ early.regs 48 ≤ 1 at gates
  have post := historicalPostEarly_machine_bounds c idx (early.regs rViol)
    early rfl gates.1 gates.2.1 gates.2.2 (by omega)
  rw [historicalBody_eq_load_early_post, arun_append, arun_append] at hbody
  rw [← loaded_eq, ← early_eq] at hbody
  rw [← loaded_eq, ← early_eq]
  omega

end LeanCompCert.Ports.DirichletLadderExternalSafety
