import LeanCompCert.Ports.RamareMStar140MPre
import LeanCompCert.Ports.RamareMStar140MPost1
import LeanCompCert.Ports.RamareMStar140MPost2

/-!
# One flat round of the `m★` body, in ordinary mathematics

`Pre`, `Post1` and `Post2` say what each of the fifteen blocks computes.  This
module puts them together into one statement about **one iteration**:

```text
obsR (arun k s (msBody c)) = msRound c k (obsR s)
```

`msRound` is written entirely in `MA`/`MS`/`MMul`/`bitOf` and the `sem…`
functions, so it carries the machine's `% 2⁶⁴` at every point the machine has
one; no wrap-freedom claim is made here.  Re-blocking `len · B` of these into
`len` candidates, and identifying a block with `msStep`, is
`Ports/RamareMStar140MDenote.lean`.

★ **The array is part of the observation.**  `Ports/RamareWM217.lean`'s array is
read-only, so its observation is registers only; this body has a `store`, so
`obsR` carries `arr` and `msRound` updates it.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.RS62
open LeanCompCert.Verified.InstrBlock
  (srun sval sdest SDefined SAllDefined NoDivI srun_append SAllDefined_append)

/-! ## The observation -/

/-- Everything one flat round carries to the next: ten registers and the
array.  (`msRef`'s `St` is the same thing at *candidate* granularity, where
`acc`, `sc` and `muQ` have been consumed.) -/
structure RSt where
  /-- Violation counter. -/
  bad : Nat
  /-- `2⁶² + L(n−1)`. -/
  lb : Nat
  /-- The RS62 ladder accumulator. -/
  lam : Nat
  /-- The log-constant slot. -/
  idx : Nat
  /-- The dyadic block start. -/
  bs : Nat
  /-- The dyadic block maximum. -/
  mx : Nat
  /-- The packed cell to store. -/
  cell : Nat
  /-- The partial `w`-sum. -/
  acc : Nat
  /-- The trial-scan accumulator. -/
  sc : Nat
  /-- `μ(q) + 1`, latched. -/
  muQ : Nat
  /-- The array. -/
  arr : Nat → Nat

/-- The machine state, observed. -/
def obsR (s : AState) : RSt :=
  { bad := s.regs rBad, lb := s.regs rLb, lam := s.regs rLam, idx := s.regs rIdx
  , bs := s.regs rBs, mx := s.regs rMax, cell := s.regs rCell
  , acc := s.regs rAcc, sc := s.regs rS, muQ := s.regs rMuQ, arr := s.arr }

/-! ## One round -/

/-- **One flat round**, transcribed block by block from the body.  Every
`% 2⁶⁴` the machine has is here. -/
def msRound (c : Cfg) (k : Nat) (st : RSt) : RSt :=
  let r := k % c.B
  let n := c.n0 + k / c.B
  let d := r + 2
  let sq := MMul d d
  let w := bitOf (r < c.B - 2)
  let qg := bitOf (r = c.B - 2)
  let cc := bitOf (r = c.B - 1)
  let z := bitOf (r ≠ 0)
  let S0 := MMul st.sc z
  let acc0 := MMul st.acc z
  let S1 := semScanS S0 sq n d w
  let p := semP S1 n
  let qn := semQ S1 n
  let qq := n / sq
  let i := semI w qq qg qn cc (c.limit + 1) st.idx
  let v := st.arr i
  let mu1 := semMu1 v
  let ab := semAbs v
  let acc1 := semAcc acc0 ab qq sq w
  let muQ1 := semMuQ qg st.muQ mu1
  let mun := semMun qn p muQ1
  let lb1 := semLb st.lb mun cc n
  let absN := semAbsN lb1
  let star := semStar acc1 absN n
  let mx1 := semMx st.mx star
  let cv := semCv n star st.mx
  let fire := semFire n c.limit st.bs
  let lam1 := semLam st.lam c.handoff n cc
  let lu := semLU n c.handoff v lam1
  let ok := semOk (MMul 5 cv) lu
  let cell1 := semCell mun absN cc st.cell
  { bad := semBadC (semBadW (semBadRow st.bad ok fire cc) acc1 ab c.capS c.capL w)
      star absN lam1 c.capS c.capL c.capLog cc
  , lb := lb1
  , lam := lam1
  , idx := semIdx st.idx cc fire c.tab
  , bs := semBs n fire st.bs cc
  , mx := semMax fire mx1 cc st.mx
  , cell := cell1
  , acc := acc1
  , sc := S1
  , muQ := muQ1
  , arr := fun j => if j = n then cell1 else st.arr j }

/-! ## The loop invariant -/

/-- What the body needs to know about the state it starts in: every register
and every cell is a word, and the log slot is in the table. -/
def MSInv (c : Cfg) (s : AState) : Prop :=
  (∀ j, s.regs j < M) ∧ (∀ i, s.arr i < M) ∧ s.regs rIdx < c.tab

/-! ## The body as one step -/

/-- The body's `arun`: one scalar stage, one `load`, one scalar stage, one
`store`.  `ArrayScalarBlock.arun_lift` carries the array through each scalar
stage untouched. -/
theorem msBody_arun (c : Cfg) (k : Nat) (s : AState) :
    arun k s (msBody c) =
      ⟨srun k (RegState.set (srun k s.regs (msPre c)) rV
          (s.arr (srun k s.regs (msPre c) rI))) (msPost c),
       fun j => if j = srun k (RegState.set (srun k s.regs (msPre c)) rV
            (s.arr (srun k s.regs (msPre c) rI))) (msPost c) rN
         then srun k (RegState.set (srun k s.regs (msPre c)) rV
            (s.arr (srun k s.regs (msPre c) rI))) (msPost c) rCell
         else s.arr j⟩ := by
  sorry

/-- **The pre-load stage, as values.** -/
theorem msPre_vals (c : Cfg) (hok : msOK c = true) (k : Nat) (hk : k < c.len * c.B)
    (s : RegState) (hs : ∀ j, s j < M) :
    srun k s (msPre c) rN = c.n0 + k / c.B ∧
      srun k s (msPre c) rSq = MMul (k % c.B + 2) (k % c.B + 2) ∧
      srun k s (msPre c) rW = bitOf (k % c.B < c.B - 2) ∧
      srun k s (msPre c) rQg = bitOf (k % c.B = c.B - 2) ∧
      srun k s (msPre c) rC = bitOf (k % c.B = c.B - 1) ∧
      srun k s (msPre c) rS =
        semScanS (MMul (s rS) (bitOf (k % c.B ≠ 0)))
          (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
          (bitOf (k % c.B < c.B - 2)) ∧
      srun k s (msPre c) rAcc = MMul (s rAcc) (bitOf (k % c.B ≠ 0)) ∧
      srun k s (msPre c) rP =
        semP (srun k s (msPre c) rS) (c.n0 + k / c.B) ∧
      srun k s (msPre c) rQ =
        semQ (srun k s (msPre c) rS) (c.n0 + k / c.B) ∧
      srun k s (msPre c) rQq =
        (c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2) ∧
      srun k s (msPre c) rI =
        semI (bitOf (k % c.B < c.B - 2))
          ((c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2))
          (bitOf (k % c.B = c.B - 2)) (srun k s (msPre c) rQ)
          (bitOf (k % c.B = c.B - 1)) (c.limit + 1) (s rIdx) := by
  sorry

/-- **The load index is in range**, and it never points at the cell this
candidate is about to write. -/
theorem msPre_index (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    srun k s.regs (msPre c) rI < c.limit + 1 + c.tab ∧
      srun k s.regs (msPre c) rI ≠ c.n0 + k / c.B := by
  sorry

/-- **The body is defined** at every index the loop visits. -/
theorem msBody_defined (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    AllDefined (c.limit + 1 + c.tab) k s (msBody c) := by
  sorry

/-- **The body computes `msRound`.** -/
theorem msBody_obs (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    obsR (arun k s (msBody c)) = msRound c k (obsR s) := by
  sorry

/-- **The invariant is preserved.** -/
theorem msBody_inv (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    MSInv c (arun k s (msBody c)) := by
  sorry

end LeanCompCert.Ports.RamareMStar140M
