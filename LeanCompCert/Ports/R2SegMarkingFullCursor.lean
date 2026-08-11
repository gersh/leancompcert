import LeanCompCert.Ports.R2SegMarkingPost

/-! # Cursor transitions across the complete `R₂*` marking block -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- Away from a window boundary, the proved prelude frame and resident suffix
transition compose into one exact cursor theorem for all 101 `markBody`
instructions. -/
theorem markFullBody_nonstart_resident_cursor_run (c : R2Cfg) (k : Nat)
    (s : AState) (r : Nat)
    (hr : s.regs rR = r) (hr0 : r ≠ 0) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hpiK : s.regs rPi ≤ c.tableLen)
    (hqM : s.regs rQ < M) (hqNZ : s.regs rQ ≠ 0)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M) (hjM : s.regs rJ < M)
    (hjL : s.regs rJ < c.segLen)
    (haddr : s.regs rJ + 2 * c.segLen < M)
    (hmul : s.regs rQ * s.regs rBp < M) (hhi : c.hi < M)
    (htableAddr : s.regs rPi + c.tableBase < M)
    (hword : (arun k (arun k s (markPreludeBody c))
      (markAddressCellBody c)).arr (s.regs rPi + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.budgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s c.markBody
    out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rWt = s.regs rWt ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ + s.regs rQ ∧
      out.regs rPi = s.regs rPi ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure := by
  let pre := arun k s (markPreludeBody c)
  have hp := markPreludeBody_nonstart_run c k s r hr hr0 hrT hperiod
    hq0 hq0M hpiM hqM hbpM hwtM hfsM hjM
  dsimp only at hp
  rcases hp with ⟨h8, _h14, _h9, _h15, hpi, hq, hbp, hwt, hfs, hj,
    hpr, hpw, _harr⟩
  have hpViol : pre.regs rViol = s.regs rViol :=
    arun_frame k rViol (markPreludeBody c) (by rfl) s
  have hpVMark : pre.regs rVMark = s.regs rVMark :=
    arun_frame k rVMark (markPreludeBody c) (by rfl) s
  have run := markResidentBody_resident_cursor_run c k pre (s.regs rJ)
    hj h8 hjL haddr (by rw [hq, hbp]; exact hmul) hhi
    (by rw [hpi]; exact hpiM) (by rw [hpi]; exact hpiK)
    (by rw [hpi]; exact htableAddr) (by rw [hpi]; exact hword)
    (by rw [hj, hq]; exact hjQ) (by rw [hq]; exact hqNZ)
    (by rw [hq]; exact hqM) (by rw [hbp]; exact hbpM)
    (by rw [hwt]; exact hwtM) (by rw [hfs]; exact hfsM)
    hT hK hL1
    (by rw [hpViol, hpr, hpi]; simpa [hr] using hviol)
    (by rw [hpVMark, hpr, hpi]; simpa [hr] using hvmark)
  dsimp only at run
  rcases run with ⟨oq, obp, owt, ofs, oj, opi, ow, orr, ov, ovm⟩
  rw [← markFullBody_eq_markBody]
  simp only [markFullBody, arun_append]
  exact ⟨oq.trans hq, obp.trans hbp, owt.trans hwt, ofs.trans hfs,
    oj.trans (by rw [hj, hq]), opi.trans hpi, ow.trans hpw,
    orr.trans (hpr.trans hr.symm),
    ov.trans (by rw [hpViol, hpr, hpi, hr]),
    ovm.trans (by rw [hpVMark, hpr, hpi, hr])⟩

/-- At a window boundary, the same composition installs the first table row
before applying the resident cursor transition. -/
theorem markFullBody_start_resident_cursor_run (c : R2Cfg) (k : Nat)
    (s : AState) (w : Nat)
    (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hT0 : 0 < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M)
    (hjL : resetOffset c.q0 w < c.segLen)
    (haddr : resetOffset c.q0 w + 2 * c.segLen < M)
    (hmul : c.q0 * c.q0 < M) (hhi : c.hi < M)
    (htableAddr : c.tableBase < M)
    (hword : (arun k (arun k s (markPreludeBody c))
      (markAddressCellBody c)).arr c.tableBase < M)
    (hjQ : resetOffset c.q0 w + c.q0 < M)
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure 0 0 < M)
    (hvmark : s.regs rVMark + c.budgetFailure 0 0 < M) :
    let failure := c.budgetFailure 0 0
    let out := arun k s c.markBody
    out.regs rQ = c.q0 ∧ out.regs rBp = c.q0 ∧
      out.regs rWt = c.w0 ∧ out.regs rFs = 1 ∧
      out.regs rJ = resetOffset c.q0 w + c.q0 ∧
      out.regs rPi = 0 ∧ out.regs rW = w ∧ out.regs rR = 0 ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure := by
  let pre := arun k s (markPreludeBody c)
  have hp := markPreludeBody_start_run c k s w hr hw hT0 hperiod
    hq0 hq0M hw0M
  dsimp only at hp
  rcases hp with ⟨h8, _h14, _h9, _h15, hpi, hq, hbp, hwt, hfs, hj,
    hpr, hpw, _harr⟩
  have hpViol : pre.regs rViol = s.regs rViol :=
    arun_frame k rViol (markPreludeBody c) (by rfl) s
  have hpVMark : pre.regs rVMark = s.regs rVMark :=
    arun_frame k rVMark (markPreludeBody c) (by rfl) s
  have hzeroM : 0 < M := by decide
  have honeM : 1 < M := by decide
  have run := markResidentBody_resident_cursor_run c k pre
    (resetOffset c.q0 w) hj h8 hjL haddr
    (by rw [hq, hbp]; exact hmul) hhi
    (by rw [hpi]; exact hzeroM) (by rw [hpi]; exact Nat.zero_le _)
    (by rw [hpi]; simpa using htableAddr)
    (by rw [hpi]; simpa [pre] using hword)
    (by rw [hj, hq]; exact hjQ) (by rw [hq]; omega)
    (by rw [hq]; exact hq0M) (by rw [hbp]; exact hq0M)
    (by rw [hwt]; exact hw0M) (by rw [hfs]; exact honeM)
    (by omega) hK hL1
    (by rw [hpViol, hpr, hpi]; simpa using hviol)
    (by rw [hpVMark, hpr, hpi]; simpa using hvmark)
  dsimp only at run
  rcases run with ⟨oq, obp, owt, ofs, oj, opi, ow, orr, ov, ovm⟩
  rw [← markFullBody_eq_markBody]
  simp only [markFullBody, arun_append]
  exact ⟨oq.trans hq, obp.trans hbp, owt.trans hwt, ofs.trans hfs,
    oj.trans (by rw [hj, hq]), opi.trans hpi, ow.trans hpw,
    orr.trans hpr,
    ov.trans (by rw [hpViol, hpr, hpi]),
    ovm.trans (by rw [hpVMark, hpr, hpi])⟩

#print axioms markFullBody_nonstart_resident_cursor_run
#print axioms markFullBody_start_resident_cursor_run

end LeanCompCert.Ports.R2SegSieve
