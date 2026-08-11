import LeanCompCert.Ports.R2SegMarkingAddress

/-!
# Active production marking hit

This module composes the production address selector with the literal
three-plane marking-cell slice.  It is the first theorem whose input is the
pre-address state used by `R2Cfg.markBody` and whose output is the logical
prime-power update at an explicit segment cell.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)

def planeWordsAt (s : AState) (L j : Nat) : PlaneWords :=
  ⟨s.arr j, s.arr (j + L), s.arr (j + 2 * L)⟩

def writePlaneWordsAt (s : AState) (L j : Nat) (x : PlaneWords) : AState :=
  ((s.writeArr j x.prod).writeArr (j + L) x.lsum).writeArr
    (j + 2 * L) x.weights

def markAddressCellBody (c : R2Cfg) : List AInstr :=
  markAddressBody c ++ markCellBody

/-- The composed helper is definitionally the 30-instruction active-hit slice
of the production marking body. -/
theorem markAddressCellBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 23).take (markAddressCellBody c).length =
      markAddressCellBody c := by
  rfl

/-- On an active in-window hit, the production address and cell stages update
exactly the logical cell at `j`. -/
theorem markAddressCellBody_markPower_run (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen j = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr j + markBit (s.arr j = 0)) * p < M)
    (hlsum : s.arr (j + c.segLen) + wt < M)
    (hweights : s.arr (j + 2 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s (markAddressCellBody c)
    out.arr =
      (writePlaneWordsAt s c.segLen j
        ((x.markPower p wt first).encode)).arr := by
  let addressed := arun k s (markAddressBody c)
  have ha := markAddressBody_run c k s j hj hactive hjL haddr
  dsimp only at ha
  rcases ha with ⟨h30, h31, h32, harr⟩
  change addressed.regs 30 = j at h30
  change addressed.regs 31 = j + c.segLen at h31
  change addressed.regs 32 = j + 2 * c.segLen at h32
  change addressed.arr = s.arr at harr
  have frameAddr (r : Nat) (h : writes r (markAddressBody c) = false) :
      addressed.regs r = s.regs r :=
    arun_frame k r (markAddressBody c) h s
  have hp' : addressed.regs rBp = p :=
    (frameAddr rBp (by rfl)).trans hp
  have hwt' : addressed.regs rWt = wt :=
    (frameAddr rWt (by rfl)).trans hwt
  have hfirst' : addressed.regs rFs = if first then 1 else 0 :=
    (frameAddr rFs (by rfl)).trans hfirst
  have hloaded' : loadedPlaneWords addressed = x.encode := by
    simpa [loadedPlaneWords, planeWordsAt, h30, h31, h32, harr] using
      hloaded
  have hcell := markCellBody_markPower_addressed_run k addressed x
    c.segLen j p wt first hL h30 h31 h32 hloaded' hx hp' hwt' hfirst'
    hp0 hpM hwtBound (by rw [h30, harr]; exact hprod)
    (by rw [h31, harr]; exact hlsum)
    (by rw [h32, harr]; exact hweights)
  dsimp only at hcell
  simp only [markAddressCellBody, arun_append]
  simp only [writeLoadedPlaneWords, writePlaneWordsAt, AState.writeArr]
    at hcell ⊢
  rw [h30, h31, h32, harr] at hcell
  exact hcell

/-- On an active cursor already past the window, the same literal cell block
updates only the three scratch sinks. -/
theorem markAddressCellBody_past_run (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : c.segLen ≤ j) (haddr : 5 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen (3 * c.segLen) = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr (3 * c.segLen) +
      markBit (s.arr (3 * c.segLen) = 0)) * p < M)
    (hlsum : s.arr (4 * c.segLen) + wt < M)
    (hweights : s.arr (5 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    let out := arun k s (markAddressCellBody c)
    out.arr =
      (writePlaneWordsAt s c.segLen (3 * c.segLen)
        ((x.markPower p wt first).encode)).arr := by
  let addressed := arun k s (markAddressBody c)
  have ha := markAddressBody_past_run c k s j hj hactive hjL haddr
  dsimp only at ha
  rcases ha with ⟨h30, h31, h32, harr⟩
  change addressed.regs 30 = 3 * c.segLen at h30
  change addressed.regs 31 = 4 * c.segLen at h31
  change addressed.regs 32 = 5 * c.segLen at h32
  change addressed.arr = s.arr at harr
  have frameAddr (r : Nat) (h : writes r (markAddressBody c) = false) :
      addressed.regs r = s.regs r :=
    arun_frame k r (markAddressBody c) h s
  have hp' : addressed.regs rBp = p :=
    (frameAddr rBp (by rfl)).trans hp
  have hwt' : addressed.regs rWt = wt :=
    (frameAddr rWt (by rfl)).trans hwt
  have hfirst' : addressed.regs rFs = if first then 1 else 0 :=
    (frameAddr rFs (by rfl)).trans hfirst
  have h31' : addressed.regs 31 = 3 * c.segLen + c.segLen := by
    rw [h31]
    omega
  have h32' : addressed.regs 32 = 3 * c.segLen + 2 * c.segLen := by
    rw [h32]
    omega
  have hloaded' : loadedPlaneWords addressed = x.encode := by
    simpa [loadedPlaneWords, planeWordsAt, h30, h31', h32', harr] using
      hloaded
  have hcell := markCellBody_markPower_addressed_run k addressed x
    c.segLen (3 * c.segLen) p wt first hL h30 h31' h32' hloaded' hx hp'
    hwt' hfirst' hp0 hpM hwtBound
    (by rw [h30, harr]; exact hprod)
    (by rw [h31', harr]; simpa only [show 3 * c.segLen + c.segLen =
      4 * c.segLen by omega] using hlsum)
    (by rw [h32', harr]; simpa only [show 3 * c.segLen + 2 * c.segLen =
      5 * c.segLen by omega] using hweights)
  dsimp only at hcell
  simp only [markAddressCellBody, arun_append]
  simp only [writeLoadedPlaneWords, writePlaneWordsAt, AState.writeArr]
    at hcell ⊢
  rw [h30, h31', h32', harr] at hcell
  exact hcell

#print axioms markAddressCellBody_markPower_run
#print axioms markAddressCellBody_past_run

end LeanCompCert.Ports.R2SegSieve
