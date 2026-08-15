import LeanCompCert.Ports.PsiRuntimePrimeLogStoreSemantics

/-!
# Complete final iteration of the compiled psi prime-log producer

This module composes the literal read, recurrence, conversion, and conditional
store blocks.  It proves symbolically that a final grid round writes exactly
the fixed-point natural logarithm of its resident prime.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.LogFixed

theorem psiPrimeLogBody_eq_stages (m : PsiRuntimeMeta) :
    psiPrimeLogBody m =
      psiPrimeLogReadBody m ++ psiPrimeLogCore m ++
        psiPrimeLogFinish m ++ psiPrimeLogStore m := by rfl

/-- One final literal body iteration writes exactly `lnFix sc p` to the
resident mark-table slot.  For a continuation round the hypotheses expose
the exact recurrence state produced by preceding compiled rounds; the first
round initializes that state itself. -/
theorem psiPrimeLogBody_final_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (p e j : Nat)
    (hIndexM : index < M) (hsc : 0 < m.cfg.sc) (hscM : m.cfg.sc < M)
    (hsc62 : m.cfg.sc ≤ 62)
    (hround : psiPrimeLogRoundIndex m index = j)
    (hfinal : j + 1 = m.cfg.sc)
    (hPrimeAddr : psiPrimeLogRank m index + m.cfg.primeBase < M)
    (hMarkAddr : psiPrimeLogRank m index + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + psiPrimeLogRank m index) = p)
    (he : s.arr (m.markBase + psiPrimeLogRank m index) = e)
    (helog : e = Nat.log2 p) (he62 : e ≤ 62)
    (hxlo : B62 ≤ p <<< (62 - e))
    (hxhi : p <<< (62 - e) < B63)
    (hx : j ≠ 0 →
      s.regs primeXm = (logIter (p <<< (62 - e)) j).1)
    (ha : j ≠ 0 →
      s.regs primeAa = (logIter (p <<< (62 - e)) j).2)
    (hfix : logFix m.cfg.sc p < 2 ^ 30) :
    let target := psiPrimeLogRank m index + m.markBase
    let out := arun index s (psiPrimeLogBody m)
    out.arr = fun x => if x = target then lnFix m.cfg.sc p else s.arr x := by
  let read := arun index s (psiPrimeLogReadBody m)
  have hr := psiPrimeLogReadBody_run m index s p e hIndexM hsc hscM
    hPrimeAddr hMarkAddr hp he
  rcases hr with ⟨hr10, hr11, hr12, hr14, hr16, hr17, hr18, hrArr⟩
  have hrRound : read.regs 11 = j := hr11.trans hround
  have hrFinal : read.regs 14 = 1 := by
    simpa only [hround, if_pos hfinal] using hr14
  have hrXm : j ≠ 0 →
      read.regs primeXm = (logIter (p <<< (62 - e)) j).1 := by
    intro hj
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame index primeXm
      (psiPrimeLogReadBody m) (by rfl) s).trans (hx hj)
  have hrAa : j ≠ 0 →
      read.regs primeAa = (logIter (p <<< (62 - e)) j).2 := by
    intro hj
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame index primeAa
      (psiPrimeLogReadBody m) (by rfl) s).trans (ha hj)
  let core := arun index read (psiPrimeLogCore m)
  have hc :
      core.regs primeXm = (logIter (p <<< (62 - e)) m.cfg.sc).1 ∧
      core.regs primeAa = (logIter (p <<< (62 - e)) m.cfg.sc).2 ∧
      core.arr = read.arr := by
    by_cases hj0 : j = 0
    · have hstart : read.regs 12 = 1 := by
        calc
          read.regs 12 =
              (if psiPrimeLogRoundIndex m index = 0 then 1 else 0) := hr12
          _ = 1 := by rw [hround, hj0]; rfl
      have hc0 := psiPrimeLogCore_start_run m index read p e hstart
        hr16 hr18 he62 hxlo hxhi
      have hsc1 : m.cfg.sc = 1 := by omega
      simpa only [core, hsc1] using hc0
    · have hstart : read.regs 12 = 0 := by
        simpa only [hround, if_neg hj0] using hr12
      have hnormM : p <<< (62 - e) < M :=
        Nat.lt_trans hxhi (by decide)
      have hcj := psiPrimeLogCore_continue_run m index read p e
        (p <<< (62 - e)) j hstart hr16 hr18 (hrXm hj0) (hrAa hj0)
        he62 hnormM hxlo hxhi (by omega)
      simpa only [core, hfinal] using hcj
  have hc18 : core.regs 18 = Nat.log2 p := by
    calc
      core.regs 18 = read.regs 18 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 18
          (psiPrimeLogCore m) (by rfl) read
      _ = e := hr18
      _ = Nat.log2 p := helog
  have hc14 : core.regs 14 = 1 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 14
      (psiPrimeLogCore m) (by rfl) read).trans hrFinal
  have hc17 : core.regs 17 = psiPrimeLogRank m index + m.markBase :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 17
      (psiPrimeLogCore m) (by rfl) read).trans hr17
  let finish := arun index core (psiPrimeLogFinish m)
  have hfinish := psiPrimeLogFinish_logFix_run m index core p hc18
    (by simpa only [logFrac, helog] using hc.2.1) hscM hfix
  have hf14 : finish.regs 14 = 1 :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 14
      (psiPrimeLogFinish m) (by rfl) core).trans hc14
  have hf17 : finish.regs 17 = psiPrimeLogRank m index + m.markBase :=
    (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 17
      (psiPrimeLogFinish m) (by rfl) core).trans hc17
  have hs := psiPrimeLogStore_final_run m index finish
    (psiPrimeLogRank m index + m.markBase) (lnFix m.cfg.sc p)
    hf14 hf17 hfinish.1 hMarkAddr
  rw [psiPrimeLogBody_eq_stages, arun_append, arun_append, arun_append]
  simpa only [finish, core, read, hfinish.2, hc.2.2, hrArr] using hs

#print axioms psiPrimeLogBody_final_run

end LeanCompCert.Ports.PsiSegSieve
