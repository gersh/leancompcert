import LeanCompCert.Ports.RamareCombined100MLambdaPsiSelection

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M

def lowerEndpointBody : List AInstr :=
  copyEndpointBody rPsiLQ rPsiLR ++
  advanceBody 220 221 rLamL 132 222 ++
  commitEndpointBody rPsiLQ rPsiLR

def upperEndpointBody : List AInstr :=
  copyEndpointBody rPsiUQ rPsiUR ++
  advanceBody 220 221 rLamU 132 222 ++
  commitEndpointBody rPsiUQ rPsiUR

/-- The complete lower-endpoint shell copies, advances, and commits exactly,
while retaining the old endpoint when the phase gate is zero. -/
theorem lowerEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiLQ < M) (hr : s.regs rPsiLR < M)
    (hlam : s.regs rLamL < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs rPsiLR + s.regs rLamL < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M) :
    let out := arun k s lowerEndpointBody
    out.regs rPsiLQ =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamL)
            ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q
        else s.regs rPsiLQ) ∧
      out.regs rPsiLR =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamL)
            ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r
        else s.regs rPsiLR) ∧
      out.arr = s.arr := by
  let copied := arun k s (copyEndpointBody rPsiLQ rPsiLR)
  let advanced := arun k copied (advanceBody 220 221 rLamL 132 222)
  have hcopy := copyLowerEndpointBody_run k s
  have hcq : copied.regs 220 = s.regs rPsiLQ := hcopy.1
  have hcr : copied.regs 221 = s.regs rPsiLR := hcopy.2.1
  have hcsrcQ : copied.regs rPsiLQ = s.regs rPsiLQ := hcopy.2.2.1
  have hcsrcR : copied.regs rPsiLR = s.regs rPsiLR := hcopy.2.2.2.1
  have hcarr : copied.arr = s.arr := hcopy.2.2.2.2
  have hclam : copied.regs rLamL = s.regs rLamL :=
    arun_reg_frame k rLamL _ s (by decide)
  have hcn : copied.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by decide)
  have hcg : copied.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by decide)
  have hadv := advanceBody_lower_run k copied
    (by simpa [hcq] using hq) (by simpa [hcr] using hr)
    (by simpa [hclam] using hlam) (by simpa [hcn] using hn)
    (by simpa [hcr, hclam] using ha)
    (by simpa [hcq, hcr, hclam, hcn] using houtQ)
  have haQ : advanced.regs 220 =
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q := by
    simpa [hcq, hcr, hclam, hcn] using hadv.1
  have haR : advanced.regs 221 =
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r := by
    simpa [hcq, hcr, hclam, hcn] using hadv.2
  have hasrcQ : advanced.regs rPsiLQ = s.regs rPsiLQ := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 rPsiLQ (by decide),
      hcsrcQ]
  have hasrcR : advanced.regs rPsiLR = s.regs rPsiLR := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 rPsiLR (by decide),
      hcsrcR]
  have hag : advanced.regs 11 = s.regs 11 := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 11 (by decide), hcg]
  have haarr : advanced.arr = s.arr := by
    rw [advanceBody_arr k copied 220 221 rLamL 132 222, hcarr]
  have hrem :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r < M :=
    Nat.lt_trans
      (PsiQR.advance_rem_lt (n := s.regs 132) (lam := s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩) hn
  have hcommit := commitLowerEndpointBody_run k advanced
    (by simpa [hag] using hgate) (by simpa [hasrcQ] using hq)
    (by simpa [hasrcR] using hr) (by simpa [haQ] using houtQ)
    (by simpa [haR] using hrem)
  rw [lowerEndpointBody, arun_append, arun_append]
  change
    (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).regs rPsiLQ = _ ∧
      (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).regs rPsiLR = _ ∧
      (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).arr = s.arr
  rcases hcommit with ⟨hcommitQ, hcommitR, hcommitArr⟩
  exact ⟨by simpa [hag, haQ, hasrcQ] using hcommitQ,
    by simpa [hag, haR, hasrcR] using hcommitR,
    by simpa [haarr] using hcommitArr⟩

/-- The complete upper-endpoint shell has the same exact copy/advance/commit
semantics and array frame. -/
theorem upperEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiUQ < M) (hr : s.regs rPsiUR < M)
    (hlam : s.regs rLamU < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs rPsiUR + s.regs rLamU < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M) :
    let out := arun k s upperEndpointBody
    out.regs rPsiUQ =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamU)
            ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q
        else s.regs rPsiUQ) ∧
      out.regs rPsiUR =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamU)
            ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r
        else s.regs rPsiUR) ∧
      out.arr = s.arr := by
  let copied := arun k s (copyEndpointBody rPsiUQ rPsiUR)
  let advanced := arun k copied (advanceBody 220 221 rLamU 132 222)
  have hcopy := copyUpperEndpointBody_run k s
  have hcq : copied.regs 220 = s.regs rPsiUQ := hcopy.1
  have hcr : copied.regs 221 = s.regs rPsiUR := hcopy.2.1
  have hcsrcQ : copied.regs rPsiUQ = s.regs rPsiUQ := hcopy.2.2.1
  have hcsrcR : copied.regs rPsiUR = s.regs rPsiUR := hcopy.2.2.2.1
  have hcarr : copied.arr = s.arr := hcopy.2.2.2.2
  have hclam : copied.regs rLamU = s.regs rLamU :=
    arun_reg_frame k rLamU _ s (by decide)
  have hcn : copied.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by decide)
  have hcg : copied.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by decide)
  have hadv := advanceBody_upper_run k copied
    (by simpa [hcq] using hq) (by simpa [hcr] using hr)
    (by simpa [hclam] using hlam) (by simpa [hcn] using hn)
    (by simpa [hcr, hclam] using ha)
    (by simpa [hcq, hcr, hclam, hcn] using houtQ)
  have haQ : advanced.regs 220 =
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q := by
    simpa [hcq, hcr, hclam, hcn] using hadv.1
  have haR : advanced.regs 221 =
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r := by
    simpa [hcq, hcr, hclam, hcn] using hadv.2
  have hasrcQ : advanced.regs rPsiUQ = s.regs rPsiUQ := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 rPsiUQ (by decide),
      hcsrcQ]
  have hasrcR : advanced.regs rPsiUR = s.regs rPsiUR := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 rPsiUR (by decide),
      hcsrcR]
  have hag : advanced.regs 11 = s.regs 11 := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 11 (by decide), hcg]
  have haarr : advanced.arr = s.arr := by
    rw [advanceBody_arr k copied 220 221 rLamU 132 222, hcarr]
  have hrem :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r < M :=
    Nat.lt_trans
      (PsiQR.advance_rem_lt (n := s.regs 132) (lam := s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩) hn
  have hcommit := commitUpperEndpointBody_run k advanced
    (by simpa [hag] using hgate) (by simpa [hasrcQ] using hq)
    (by simpa [hasrcR] using hr) (by simpa [haQ] using houtQ)
    (by simpa [haR] using hrem)
  rw [upperEndpointBody, arun_append, arun_append]
  change
    (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).regs rPsiUQ = _ ∧
      (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).regs rPsiUR = _ ∧
      (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).arr = s.arr
  rcases hcommit with ⟨hcommitQ, hcommitR, hcommitArr⟩
  exact ⟨by simpa [hag, haQ, hasrcQ] using hcommitQ,
    by simpa [hag, haR, hasrcR] using hcommitR,
    by simpa [haarr] using hcommitArr⟩


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep
