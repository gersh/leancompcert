import LeanCompCert.Ports.R2SegMarkingInstrCellRaw

/-!
# Logical refinement of the literal marking-cell slice

The machine-level three-plane update is connected here to `MarkCell.markPower`.
All arithmetic headroom assumptions remain explicit; no wraparound behavior is
used to close the refinement.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- One execution of the literal 22-instruction cell slice writes exactly the
encoding of the logical prime-power update. -/
theorem markCellBody_markPower_run (k : Nat) (s : AState) (x : MarkCell)
    (p wt : Nat) (first : Bool)
    (hloaded : loadedPlaneWords s = x.encode)
    (hx : x.Inv)
    (h30ne31 : s.regs 30 ≠ s.regs 31)
    (h30ne32 : s.regs 30 ≠ s.regs 32)
    (h31ne32 : s.regs 31 ≠ s.regs 32)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (s.regs 30) +
      markBit (s.arr (s.regs 30) = 0)) * p < M)
    (hlsum : s.arr (s.regs 31) + wt < M)
    (hweights : s.arr (s.regs 32) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s markCellBody
    out.arr =
      (writeLoadedPlaneWords s ((x.markPower p wt first).encode)).arr := by
  have hdecode : s.arr (s.regs 32) >>> 56 = x.count := by
    have hc := packWeights_count x.count x.w1 x.w2 hx.2.1 hx.2.2
    have hw := congrArg PlaneWords.weights hloaded
    change s.arr (s.regs 32) = packWeights x.count x.w1 x.w2 at hw
    rw [hw]
    exact hc
  have hraw := markCellBody_rawMarkCount_run k s x.count p wt first
    h30ne31 h30ne32 h31ne32 hp hwt hfirst hdecode hp0 hpM hx.1.1
    hwtBound hprod hlsum hweights
  dsimp only at hraw
  have hnext :
      (loadedPlaneWords s).rawMarkCount x.count p wt first =
        (x.markPower p wt first).encode := by
    rw [hloaded]
    have h := rawMark_encode x p wt first hx
    unfold PlaneWords.rawMark at h
    have hc : x.encode.count = x.count :=
      packWeights_count x.count x.w1 x.w2 hx.2.1 hx.2.2
    rw [hc] at h
    exact h
  rw [hnext] at hraw
  exact hraw

/-- Production-layout specialization: the three planes for cell `j` are at
`j`, `j + L`, and `j + 2L`.  Positivity of `L` discharges all aliasing
conditions required by the literal slice theorem. -/
theorem markCellBody_markPower_addressed_run (k : Nat) (s : AState)
    (x : MarkCell) (L j p wt : Nat) (first : Bool)
    (hL : 0 < L)
    (h30 : s.regs 30 = j)
    (h31 : s.regs 31 = j + L)
    (h32 : s.regs 32 = j + 2 * L)
    (hloaded : loadedPlaneWords s = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (s.regs 30) +
      markBit (s.arr (s.regs 30) = 0)) * p < M)
    (hlsum : s.arr (s.regs 31) + wt < M)
    (hweights : s.arr (s.regs 32) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s markCellBody
    out.arr =
      (writeLoadedPlaneWords s ((x.markPower p wt first).encode)).arr := by
  have h30ne31 : s.regs 30 ≠ s.regs 31 := by rw [h30, h31]; omega
  have h30ne32 : s.regs 30 ≠ s.regs 32 := by rw [h30, h32]; omega
  have h31ne32 : s.regs 31 ≠ s.regs 32 := by rw [h31, h32]; omega
  exact markCellBody_markPower_run k s x p wt first hloaded hx
    h30ne31 h30ne32 h31ne32 hp hwt hfirst hp0 hpM hwtBound hprod hlsum
    hweights

#print axioms markCellBody_markPower_run
#print axioms markCellBody_markPower_addressed_run

end LeanCompCert.Ports.R2SegSieve
