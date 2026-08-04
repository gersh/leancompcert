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
@[ext] structure RSt where
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
and every cell is a word, the log slot is in the table, and the trial scan
holds either nothing or a genuine trial divisor.

★ The last conjunct is load-bearing rather than cosmetic.  The Möbius round's
load index is `n / p` with `p = if s = 0 then n else s`, so an incoming scan
value of `1` would make the index `n` itself — the very cell the round is
about to write.  `1` is unreachable (the scan register only ever holds `0` or
a trial divisor `d = r + 2 ≥ 2`), but nothing weaker than this conjunct rules
it out, and `msPre_index` is false without it. -/
def MSInv (c : Cfg) (s : AState) : Prop :=
  (∀ j, s.regs j < M) ∧ (∀ i, s.arr i < M) ∧ s.regs rIdx < c.tab ∧
    (s.regs rS = 0 ∨ 2 ≤ s.regs rS)

/-! ## The body as one step -/

/-- The `store` at the end, on a state whose register file is a variable: the
one place the final equation has to be checked, kept away from
`srun _ (msPost c)` so that no unifier ever walks the 107 instructions. -/
private theorem arun_store (k : Nat) (u : RegState) (a : Nat → Nat) (di si : Nat) :
    arun k ⟨u, a⟩ [AInstr.store di si]
      = ⟨u, fun j => if j = u di then u si else a j⟩ := rfl

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
  -- The `load` step, normalised *before* the second `arun_lift`: otherwise the
  -- final `rfl` has to unify two syntactically different register files under
  -- `srun _ (msPost c)`, which unfolds all 107 instructions.
  have hload : astep k (⟨srun k s.regs (msPre c), s.arr⟩ : AState)
        (AInstr.load rV rI)
      = ⟨RegState.set (srun k s.regs (msPre c)) rV
          (s.arr (srun k s.regs (msPre c) rI)), s.arr⟩ := rfl
  rw [show msBody c =
      lift (msPre c) ++ ((.load rV rI :: lift (msPost c)) ++ [.store rN rCell])
    from rfl,
    arun_append k (lift (msPre c)),
    arun_lift k (msPre c) s,
    arun_append k (AInstr.load rV rI :: lift (msPost c)) [AInstr.store rN rCell],
    arun_cons k _ (AInstr.load rV rI) (lift (msPost c)),
    hload,
    arun_lift k (msPost c)]
  exact arun_store k _ s.arr rN rCell

/-- The scalar post-stage, including the store it feeds, expressed only in
the values present immediately after the load. -/
private def msPostR (c : Cfg) (u : RegState) (a : Nat → Nat) : RSt :=
  let mu1 := semMu1 (u rV)
  let ab := semAbs (u rV)
  let acc1 := semAcc (u rAcc) ab (u rQq) (u rSq) (u rW)
  let muQ1 := semMuQ (u rQg) (u rMuQ) mu1
  let mun := semMun (u rQ) (u rP) muQ1
  let lb1 := semLb (u rLb) mun (u rC) (u rN)
  let absN := semAbsN lb1
  let star := semStar acc1 absN (u rN)
  let mx1 := semMx (u rMax) star
  let cv := semCv (u rN) star (u rMax)
  let fire := semFire (u rN) c.limit (u rBs)
  let lam1 := semLam (u rLam) c.handoff (u rN) (u rC)
  let lu := semLU (u rN) c.handoff (u rV) lam1
  let ok := semOk (MMul 5 cv) lu
  let cell1 := semCell mun absN (u rC) (u rCell)
  { bad := semBadC (semBadW (semBadRow (u rBad) ok fire (u rC))
      acc1 ab c.capS c.capL (u rW)) star absN lam1
      c.capS c.capL c.capLog (u rC)
  , lb := lb1
  , lam := lam1
  , idx := semIdx (u rIdx) (u rC) fire c.tab
  , bs := semBs (u rN) fire (u rBs) (u rC)
  , mx := semMax fire mx1 (u rC) (u rMax)
  , cell := cell1
  , acc := acc1
  , sc := u rS
  , muQ := muQ1
  , arr := fun j => if j = u rN then cell1 else a j }

/-- Carrying a **named** value across a block that does not write its register.
Every `have` below goes through this, so the register is always determined
before the frame check runs and no `srun` is ever whnf'd through a prefix. -/
private theorem carry {k j : Nat} {l : List Instr} {u v : RegState} {a : Nat}
    (hv : srun k u l = v) (hu : u j = a)
    (hw : writes j l = false := by rfl) : v j = a := by
  rw [← hv]; exact (read_frame hw u).trans hu

/-- The eleven scalar post-blocks jointly implement `msPostR`.  Keeping this
as a separate lemma prevents reduction from walking the 107-instruction list
when the array store is compared below. -/
private theorem msPost_obs (c : Cfg) (hok : msOK c = true) (k : Nat)
    (u : RegState) (a : Nat → Nat) (hu : ∀ j, u j < M)
    (hN0 : u rN ≠ 0) (hN2 : 2 ≤ u rN) (hN32 : u rN ≤ 2 ^ 32)
    (hSq : u rSq ≠ 0) (hP : u rP ≠ 0) :
    obsR ⟨srun k u (msPost c),
      fun j => if j = srun k u (msPost c) rN
        then srun k u (msPost c) rCell else a j⟩ = msPostR c u a := by
  obtain ⟨u1, hu1⟩ : ∃ v, srun k u unpackBlock = v := ⟨_, rfl⟩
  obtain ⟨v1Mu, v1Abs⟩ := unpackBlock_vals k u (hu rV)
  rw [hu1] at v1Mu v1Abs
  have v1Acc : u1 rAcc = u rAcc := carry hu1 rfl
  have v1Qq : u1 rQq = u rQq := carry hu1 rfl
  have v1Sq : u1 rSq = u rSq := carry hu1 rfl
  have v1W : u1 rW = u rW := carry hu1 rfl
  have v1Qg : u1 rQg = u rQg := carry hu1 rfl
  have v1MuQ : u1 rMuQ = u rMuQ := carry hu1 rfl
  have v1Q : u1 rQ = u rQ := carry hu1 rfl
  have v1P : u1 rP = u rP := carry hu1 rfl
  have v1N : u1 rN = u rN := carry hu1 rfl
  have v1Lb : u1 rLb = u rLb := carry hu1 rfl
  have v1C : u1 rC = u rC := carry hu1 rfl
  have v1Bad : u1 rBad = u rBad := carry hu1 rfl
  have v1Max : u1 rMax = u rMax := carry hu1 rfl
  have v1Bs : u1 rBs = u rBs := carry hu1 rfl
  have v1Lam : u1 rLam = u rLam := carry hu1 rfl
  have v1V : u1 rV = u rV := carry hu1 rfl
  have v1Cell : u1 rCell = u rCell := carry hu1 rfl
  have v1S : u1 rS = u rS := carry hu1 rfl
  have v1Idx : u1 rIdx = u rIdx := carry hu1 rfl
  have hm1 : ∀ j, u1 j < M := by
    rw [← hu1]
    exact srun_regs_lt k unpackBlock u hu

  obtain ⟨u2, hu2⟩ : ∃ v, srun k u1 termBlock = v := ⟨_, rfl⟩
  have v2Acc := termBlock_vals k u1 (by rw [v1Sq]; exact hSq)
  rw [hu2, v1Acc, v1Abs, v1Qq, v1Sq, v1W] at v2Acc
  have v2Mu1 : u2 rMu1 = semMu1 (u rV) := carry hu2 v1Mu
  have v2Qg : u2 rQg = u rQg := carry hu2 v1Qg
  have v2MuQ : u2 rMuQ = u rMuQ := carry hu2 v1MuQ
  have v2Q : u2 rQ = u rQ := carry hu2 v1Q
  have v2P : u2 rP = u rP := carry hu2 v1P
  have v2N : u2 rN = u rN := carry hu2 v1N
  have v2Lb : u2 rLb = u rLb := carry hu2 v1Lb
  have v2C : u2 rC = u rC := carry hu2 v1C
  have v2Abs : u2 rAbs = semAbs (u rV) := carry hu2 v1Abs
  have v2Bad : u2 rBad = u rBad := carry hu2 v1Bad
  have v2Max : u2 rMax = u rMax := carry hu2 v1Max
  have v2Bs : u2 rBs = u rBs := carry hu2 v1Bs
  have v2Lam : u2 rLam = u rLam := carry hu2 v1Lam
  have v2V : u2 rV = u rV := carry hu2 v1V
  have v2Cell : u2 rCell = u rCell := carry hu2 v1Cell
  have v2S : u2 rS = u rS := carry hu2 v1S
  have v2Idx : u2 rIdx = u rIdx := carry hu2 v1Idx
  have v2W : u2 rW = u rW := carry hu2 v1W
  have hm2 : ∀ j, u2 j < M := by
    rw [← hu2]
    exact srun_regs_lt k termBlock u1 hm1

  obtain ⟨u3, hu3⟩ : ∃ v, srun k u2 latchBlock = v := ⟨_, rfl⟩
  have v3MuQ := latchBlock_vals k u2
  rw [hu3, v2Qg, v2MuQ, v2Mu1] at v3MuQ
  have v3Q : u3 rQ = u rQ := carry hu3 v2Q
  have v3P : u3 rP = u rP := carry hu3 v2P
  have v3N : u3 rN = u rN := carry hu3 v2N
  have v3Lb : u3 rLb = u rLb := carry hu3 v2Lb
  have v3C : u3 rC = u rC := carry hu3 v2C
  have v3Acc := carry hu3 v2Acc
  have v3Abs := carry hu3 v2Abs
  have v3Bad : u3 rBad = u rBad := carry hu3 v2Bad
  have v3Max : u3 rMax = u rMax := carry hu3 v2Max
  have v3Bs : u3 rBs = u rBs := carry hu3 v2Bs
  have v3Lam : u3 rLam = u rLam := carry hu3 v2Lam
  have v3V : u3 rV = u rV := carry hu3 v2V
  have v3Cell : u3 rCell = u rCell := carry hu3 v2Cell
  have v3S : u3 rS = u rS := carry hu3 v2S
  have v3Idx : u3 rIdx = u rIdx := carry hu3 v2Idx
  have v3W : u3 rW = u rW := carry hu3 v2W
  have hm3 : ∀ j, u3 j < M := by
    rw [← hu3]
    exact srun_regs_lt k latchBlock u2 hm2

  obtain ⟨u4, hu4⟩ : ∃ v, srun k u3 muBlock = v := ⟨_, rfl⟩
  have v4Mun := muBlock_vals k u3 (by rw [v3P]; exact hP) (hm3 rQ)
  rw [hu4, v3Q, v3P, v3MuQ] at v4Mun
  have v4N : u4 rN = u rN := carry hu4 v3N
  have v4Lb : u4 rLb = u rLb := carry hu4 v3Lb
  have v4C : u4 rC = u rC := carry hu4 v3C
  have v4Acc := carry hu4 v3Acc
  have v4Abs := carry hu4 v3Abs
  have v4Bad : u4 rBad = u rBad := carry hu4 v3Bad
  have v4Max : u4 rMax = u rMax := carry hu4 v3Max
  have v4Bs : u4 rBs = u rBs := carry hu4 v3Bs
  have v4Lam : u4 rLam = u rLam := carry hu4 v3Lam
  have v4V : u4 rV = u rV := carry hu4 v3V
  have v4Cell : u4 rCell = u rCell := carry hu4 v3Cell
  have v4S : u4 rS = u rS := carry hu4 v3S
  have v4Idx : u4 rIdx = u rIdx := carry hu4 v3Idx
  have v4W : u4 rW = u rW := carry hu4 v3W
  have hm4 : ∀ j, u4 j < M := by
    rw [← hu4]
    exact srun_regs_lt k muBlock u3 hm3

  obtain ⟨u5, hu5⟩ : ∃ v, srun k u4 lbBlock = v := ⟨_, rfl⟩
  obtain ⟨v5Lb, v5AbsN⟩ := lbBlock_vals k u4 (by rw [v4N]; exact hN0)
  rw [hu5, v4Lb, v4Mun, v4C, v4N] at v5Lb v5AbsN
  have v5Acc := carry hu5 v4Acc
  have v5Abs := carry hu5 v4Abs
  have v5N : u5 rN = u rN := carry hu5 v4N
  have v5Bad : u5 rBad = u rBad := carry hu5 v4Bad
  have v5Max : u5 rMax = u rMax := carry hu5 v4Max
  have v5Bs : u5 rBs = u rBs := carry hu5 v4Bs
  have v5C : u5 rC = u rC := carry hu5 v4C
  have v5Lam : u5 rLam = u rLam := carry hu5 v4Lam
  have v5V : u5 rV = u rV := carry hu5 v4V
  have v5Cell : u5 rCell = u rCell := carry hu5 v4Cell
  have v5S : u5 rS = u rS := carry hu5 v4S
  have v5Idx : u5 rIdx = u rIdx := carry hu5 v4Idx
  have v5W : u5 rW = u rW := carry hu5 v4W
  have hm5 : ∀ j, u5 j < M := by
    rw [← hu5]
    exact srun_regs_lt k lbBlock u4 hm4

  obtain ⟨u6, hu6⟩ : ∃ v, srun k u5 starBlock = v := ⟨_, rfl⟩
  have v6St := starBlock_vals k u5
  rw [hu6, v5Acc, v5AbsN, v5N] at v6St
  have v6Bad : u6 rBad = u rBad := carry hu6 v5Bad
  have v6Max : u6 rMax = u rMax := carry hu6 v5Max
  have v6Bs : u6 rBs = u rBs := carry hu6 v5Bs
  have v6N : u6 rN = u rN := carry hu6 v5N
  have v6C : u6 rC = u rC := carry hu6 v5C
  have v6Lam : u6 rLam = u rLam := carry hu6 v5Lam
  have v6V : u6 rV = u rV := carry hu6 v5V
  have v6Cell : u6 rCell = u rCell := carry hu6 v5Cell
  have v6Acc := carry hu6 v5Acc
  have v6Abs := carry hu6 v5Abs
  have v6Lb := carry hu6 v5Lb
  have v6AbsN := carry hu6 v5AbsN
  have v6S : u6 rS = u rS := carry hu6 v5S
  have v6Idx : u6 rIdx = u rIdx := carry hu6 v5Idx
  have v6W : u6 rW = u rW := carry hu6 v5W
  have hm6 : ∀ j, u6 j < M := by
    rw [← hu6]
    exact srun_regs_lt k starBlock u5 hm5

  obtain ⟨u7, hu7⟩ : ∃ v, srun k u6 (gateBlock c) = v := ⟨_, rfl⟩
  obtain ⟨v7Mx, v7Cv, v7Fire⟩ := gateBlock_vals (c := c) k u6 (ok_limM hok)
  rw [hu7] at v7Mx v7Cv v7Fire
  rw [v6Max, v6St] at v7Mx
  rw [v6N, v6St, v6Max] at v7Cv
  rw [v6N, v6Bs] at v7Fire
  have v7Bad : u7 rBad = u rBad := carry hu7 v6Bad
  have v7N : u7 rN = u rN := carry hu7 v6N
  have v7C : u7 rC = u rC := carry hu7 v6C
  have v7Lam : u7 rLam = u rLam := carry hu7 v6Lam
  have v7V : u7 rV = u rV := carry hu7 v6V
  have v7Cell : u7 rCell = u rCell := carry hu7 v6Cell
  have v7Acc := carry hu7 v6Acc
  have v7Abs := carry hu7 v6Abs
  have v7Lb := carry hu7 v6Lb
  have v7AbsN := carry hu7 v6AbsN
  have v7S : u7 rS = u rS := carry hu7 v6S
  have v7Idx : u7 rIdx = u rIdx := carry hu7 v6Idx
  have v7Max : u7 rMax = u rMax := carry hu7 v6Max
  have v7Bs : u7 rBs = u rBs := carry hu7 v6Bs
  have v7St := carry hu7 v6St
  have v7W : u7 rW = u rW := carry hu7 v6W
  have hm7 : ∀ j, u7 j < M := by
    rw [← hu7]
    exact srun_regs_lt k (gateBlock c) u6 hm6

  obtain ⟨u8, hu8⟩ : ∃ v, srun k u7 (ladderBlock c) = v := ⟨_, rfl⟩
  obtain ⟨v8Lam, v8LU⟩ := ladderBlock_vals (c := c) k u7
    (by rw [v7N]; exact hN2) (by rw [v7N]; exact hN32) (ok_handoffM hok)
  rw [hu8] at v8Lam v8LU
  rw [v7Lam, v7N, v7C] at v8Lam
  rw [v7N, v7V, v7Lam, v7C] at v8LU
  have v8Bad : u8 rBad = u rBad := carry hu8 v7Bad
  have v8C : u8 rC = u rC := carry hu8 v7C
  have v8Cell : u8 rCell = u rCell := carry hu8 v7Cell
  have v8Acc := carry hu8 v7Acc
  have v8Abs := carry hu8 v7Abs
  have v8Lb := carry hu8 v7Lb
  have v8AbsN := carry hu8 v7AbsN
  have v8S : u8 rS = u rS := carry hu8 v7S
  have v8Idx : u8 rIdx = u rIdx := carry hu8 v7Idx
  have v8Max : u8 rMax = u rMax := carry hu8 v7Max
  have v8Bs : u8 rBs = u rBs := carry hu8 v7Bs
  have v8N : u8 rN = u rN := carry hu8 v7N
  have v8St := carry hu8 v7St
  have v8Mx := carry hu8 v7Mx
  have v8Cv := carry hu8 v7Cv
  have v8Fire := carry hu8 v7Fire
  have v8Mun := carry hu8 (carry hu7 (carry hu6 (carry hu5 v4Mun)))
  have v8W : u8 rW = u rW := carry hu8 v7W
  have hm8 : ∀ j, u8 j < M := by
    rw [← hu8]
    exact srun_regs_lt k (ladderBlock c) u7 hm7

  obtain ⟨u9, hu9⟩ : ∃ v, srun k u8 productBlock = v := ⟨_, rfl⟩
  obtain ⟨_, _, v9Ok⟩ := productBlock_vals k u8 (hm8 rLU)
  rw [hu9, v8Cv, v8LU] at v9Ok
  have v9Bad : u9 rBad = u rBad := carry hu9 v8Bad
  have v9C : u9 rC = u rC := carry hu9 v8C
  have v9Cell : u9 rCell = u rCell := carry hu9 v8Cell
  have v9Acc := carry hu9 v8Acc
  have v9Abs := carry hu9 v8Abs
  have v9Lb := carry hu9 v8Lb
  have v9AbsN := carry hu9 v8AbsN
  have v9Lam := carry hu9 v8Lam
  have v9S : u9 rS = u rS := carry hu9 v8S
  have v9Idx : u9 rIdx = u rIdx := carry hu9 v8Idx
  have v9Max : u9 rMax = u rMax := carry hu9 v8Max
  have v9Bs : u9 rBs = u rBs := carry hu9 v8Bs
  have v9N : u9 rN = u rN := carry hu9 v8N
  have v9St := carry hu9 v8St
  have v9Mx := carry hu9 v8Mx
  have v9Fire := carry hu9 v8Fire
  have v9Mun := carry hu9 v8Mun
  have v9W : u9 rW = u rW := carry hu9 v8W

  obtain ⟨u10, hu10⟩ : ∃ v, srun k u9 (badBlock c) = v := ⟨_, rfl⟩
  have hcapS : c.capS < M := Nat.lt_of_le_of_lt (ok_capS hok) (by decide)
  have hcapL : c.capL < M := Nat.lt_of_le_of_lt (ok_capL hok) (by decide)
  have hcapLog : c.capLog < M := Nat.lt_of_le_of_lt (ok_capLog hok) (by decide)
  have v10Bad := badBlock_vals (c := c) k u9 hcapS hcapL hcapLog
  rw [hu10, v9Bad, v9Ok, v9Fire, v9C, v9Acc, v9Abs, v9St, v9AbsN, v9Lam,
    v9W] at v10Bad
  have v10Cell : u10 rCell = u rCell := carry hu10 v9Cell
  have v10Lb := carry hu10 v9Lb
  have v10Lam := carry hu10 v9Lam
  have v10S : u10 rS = u rS := carry hu10 v9S
  have v10Idx : u10 rIdx = u rIdx := carry hu10 v9Idx
  have v10Max : u10 rMax = u rMax := carry hu10 v9Max
  have v10Bs : u10 rBs = u rBs := carry hu10 v9Bs
  have v10N : u10 rN = u rN := carry hu10 v9N
  have v10C : u10 rC = u rC := carry hu10 v9C
  have v10Mx := carry hu10 v9Mx
  have v10Fire := carry hu10 v9Fire
  have v10Mun := carry hu10 v9Mun
  have v10AbsN := carry hu10 v9AbsN
  have v10Acc := carry hu10 v9Acc
  have v10MuQ := carry hu10 (carry hu9 (carry hu8 (carry hu7 (carry hu6
    (carry hu5 (carry hu4 v3MuQ))))))

  obtain ⟨u11, hu11⟩ : ∃ v, srun k u10 (updateBlock c) = v := ⟨_, rfl⟩
  obtain ⟨v11Cell, v11Max, v11Bs, v11Idx⟩ :=
    updateBlock_vals (c := c) k u10 (by have := ok_tab0 hok; omega) (ok_tabM hok)
  rw [hu11] at v11Cell v11Max v11Bs v11Idx
  rw [v10Mun, v10AbsN, v10C, v10Cell] at v11Cell
  rw [v10Fire, v10Mx, v10C, v10Max] at v11Max
  rw [v10N, v10Fire, v10Bs, v10C] at v11Bs
  rw [v10Idx, v10C, v10Fire] at v11Idx
  have v11Bad := carry hu11 v10Bad
  have v11Lb := carry hu11 v10Lb
  have v11Lam := carry hu11 v10Lam
  have v11Acc := carry hu11 v10Acc
  have v11S : u11 rS = u rS := carry hu11 v10S
  have v11MuQ := carry hu11 v10MuQ
  have v11N : u11 rN = u rN := carry hu11 v10N
  have hrun : srun k u (msPost c) = u11 := by
    rw [show msPost c = unpackBlock ++ (termBlock ++ (latchBlock ++ (muBlock ++
      (lbBlock ++ (starBlock ++ (gateBlock c ++ (ladderBlock c ++
        (productBlock ++ (badBlock c ++ updateBlock c))))))))) from rfl,
      srun_append, srun_append, srun_append, srun_append, srun_append,
      srun_append, srun_append, srun_append, srun_append, srun_append,
      hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10, hu11]
  rw [hrun]
  ext j <;> simp only [obsR, msPostR]
  · exact v11Bad
  · exact v11Lb
  · exact v11Lam
  · exact v11Idx
  · exact v11Bs
  · exact v11Max
  · exact v11Cell
  · exact v11Acc
  · exact v11S
  · exact v11MuQ
  · rw [v11N, v11Cell]

/-- The scan accumulator is a word: it is an `MA`. -/
private theorem semScanS_lt (S sq n d w : Nat) : semScanS S sq n d w < M := MA_lt _ _

/-- **The pre-load stage, as values.** -/
theorem msPre_vals (c : Cfg) (hok : msOK c = true) (k : Nat) (hk : k < c.len * c.B)
    (s : RegState) (_hs : ∀ j, s j < M) :
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
  obtain ⟨hkM, hkdiv, hkmod, hnle⟩ := ok_idx hok hk
  have hB0 : 0 < c.B := ok_B_pos hok
  have hBM : c.B < M := ok_BM hok
  have hn0M : c.n0 < M := ok_n0M hok
  have hlimM : c.limit < M := ok_limM hok
  have hn0 : 2 ≤ c.n0 := ok_n0 hok
  have hBlt : c.B + 1 < 2 ^ 20 := ok_Blt hok
  have hlim32 : c.limit < 2 ^ 32 := ok_lim32 hok
  have h20 : (2:Nat) ^ 20 < M := two20_lt_M
  have h32 : (2:Nat) ^ 32 < M := two32_lt_M
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnle hlimM
  have hn2 : 2 ≤ c.n0 + k / c.B := Nat.le_trans hn0 (Nat.le_add_right c.n0 (k / c.B))
  have hdM : k % c.B + 2 < M := by omega
  have hB2M : c.B - 2 < M := by omega
  have hB1M : c.B - 1 < M := by omega
  have hlim1M : c.limit + 1 < M := by omega
  have hdle : k % c.B + 2 ≤ 2 ^ 20 := by omega
  have hddle : (k % c.B + 2) * (k % c.B + 2) ≤ 2 ^ 20 * 2 ^ 20 :=
    Nat.mul_le_mul hdle hdle
  have hM40 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
  have hdd : (k % c.B + 2) * (k % c.B + 2) < M := Nat.lt_of_le_of_lt hddle hM40
  have hsqval : MMul (k % c.B + 2) (k % c.B + 2) = (k % c.B + 2) * (k % c.B + 2) :=
    Nat.mod_eq_of_lt hdd
  have hsqpos : 0 < (k % c.B + 2) * (k % c.B + 2) := Nat.mul_pos (by omega) (by omega)
  have hsq0 : MMul (k % c.B + 2) (k % c.B + 2) ≠ 0 := by rw [hsqval]; omega
  -- stage 1: the decode
  obtain ⟨u1, hu1⟩ : ∃ u, srun k s (decodeBlock c) = u := ⟨_, rfl⟩
  obtain ⟨d_N, d_D, d_Sq, d_W, d_Qg, d_C, d_S, d_Acc⟩ :=
    decodeBlock_vals (c := c) k s (r := k % c.B) (n := c.n0 + k / c.B)
      (d := k % c.B + 2) rfl rfl rfl hkM hB0 hBM hn0M hnM hdM hB2M hB1M
  rw [hu1] at d_N d_D d_Sq d_W d_Qg d_C d_S d_Acc
  have d_Idx : u1 rIdx = s rIdx := carry hu1 rfl
  -- stage 2: the trial round
  obtain ⟨u2, hu2⟩ : ∃ u, srun k u1 scanBlock = u := ⟨_, rfl⟩
  have e2_S : u2 rS =
      semScanS (MMul (s rS) (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2)) := by
    rw [← hu2, scanBlock_vals k u1 (by rw [d_D]; omega) (by rw [d_N]; exact hnM),
      d_S, d_Sq, d_N, d_D, d_W]
  have e2_N : u2 rN = c.n0 + k / c.B := carry hu2 d_N
  have e2_Sq : u2 rSq = MMul (k % c.B + 2) (k % c.B + 2) := carry hu2 d_Sq
  have e2_W : u2 rW = bitOf (k % c.B < c.B - 2) := carry hu2 d_W
  have e2_Qg : u2 rQg = bitOf (k % c.B = c.B - 2) := carry hu2 d_Qg
  have e2_C : u2 rC = bitOf (k % c.B = c.B - 1) := carry hu2 d_C
  have e2_Acc : u2 rAcc = MMul (s rAcc) (bitOf (k % c.B ≠ 0)) := carry hu2 d_Acc
  have e2_Idx : u2 rIdx = s rIdx := carry hu2 d_Idx
  have e2_SM : u2 rS < M := by rw [e2_S]; exact semScanS_lt _ _ _ _ _
  have e2_NM : u2 rN < M := by rw [e2_N]; exact hnM
  have e2_N0 : u2 rN ≠ 0 := by rw [e2_N]; omega
  -- stage 3: the factor select
  obtain ⟨u3, hu3⟩ : ∃ u, srun k u2 selectBlock = u := ⟨_, rfl⟩
  obtain ⟨d_P, d_Q⟩ := selectBlock_vals k u2 e2_SM e2_NM e2_N0
  rw [hu3] at d_P d_Q
  have e3_N : u3 rN = c.n0 + k / c.B := carry hu3 e2_N
  have e3_Sq : u3 rSq = MMul (k % c.B + 2) (k % c.B + 2) := carry hu3 e2_Sq
  have e3_W : u3 rW = bitOf (k % c.B < c.B - 2) := carry hu3 e2_W
  have e3_Qg : u3 rQg = bitOf (k % c.B = c.B - 2) := carry hu3 e2_Qg
  have e3_C : u3 rC = bitOf (k % c.B = c.B - 1) := carry hu3 e2_C
  have e3_Acc : u3 rAcc = MMul (s rAcc) (bitOf (k % c.B ≠ 0)) := carry hu3 e2_Acc
  have e3_Idx : u3 rIdx = s rIdx := carry hu3 e2_Idx
  have e3_S : u3 rS =
      semScanS (MMul (s rS) (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2)) := carry hu3 e2_S
  have e3_Su2 : u3 rS = u2 rS := carry hu3 rfl
  have e3_Nu2 : u3 rN = u2 rN := carry hu3 rfl
  have e3_P : u3 rP = semP (u3 rS) (u3 rN) := by rw [e3_Su2, e3_Nu2]; exact d_P
  have e3_Q : u3 rQ = semQ (u3 rS) (u3 rN) := by rw [e3_Su2, e3_Nu2]; exact d_Q
  have e3_SqNe : u3 rSq ≠ 0 := by rw [e3_Sq]; exact hsq0
  have e3_NM : u3 rN < M := by rw [e3_N]; exact hnM
  -- stage 4: the load index
  obtain ⟨u4, hu4⟩ : ∃ u, srun k u3 (indexBlock c) = u := ⟨_, rfl⟩
  obtain ⟨d_Qq, d_I⟩ := indexBlock_vals (c := c) k u3 e3_SqNe e3_NM hlim1M
  rw [hu4] at d_Qq d_I
  have e4_N : u4 rN = c.n0 + k / c.B := carry hu4 e3_N
  have e4_Sq : u4 rSq = MMul (k % c.B + 2) (k % c.B + 2) := carry hu4 e3_Sq
  have e4_W : u4 rW = bitOf (k % c.B < c.B - 2) := carry hu4 e3_W
  have e4_Qg : u4 rQg = bitOf (k % c.B = c.B - 2) := carry hu4 e3_Qg
  have e4_C : u4 rC = bitOf (k % c.B = c.B - 1) := carry hu4 e3_C
  have e4_Acc : u4 rAcc = MMul (s rAcc) (bitOf (k % c.B ≠ 0)) := carry hu4 e3_Acc
  have e4_S : u4 rS =
      semScanS (MMul (s rS) (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2)) := carry hu4 e3_S
  have e4_Su3 : u4 rS = u3 rS := carry hu4 rfl
  have e4_Nu3 : u4 rN = u3 rN := carry hu4 rfl
  have e4_Qu3 : u4 rQ = u3 rQ := carry hu4 rfl
  have e4_P : u4 rP = semP (u4 rS) (u4 rN) := by
    rw [e4_Su3, e4_Nu3, ← e3_P]; exact carry hu4 rfl
  have e4_Q : u4 rQ = semQ (u4 rS) (u4 rN) := by
    rw [e4_Su3, e4_Nu3, ← e3_Q]; exact carry hu4 rfl
  -- the whole pre-stage
  have hsplit : msPre c =
      decodeBlock c ++ (scanBlock ++ (selectBlock ++ indexBlock c)) := rfl
  have hrun : srun k s (msPre c) = u4 := by
    rw [hsplit, srun_append, srun_append, srun_append, hu1, hu2, hu3, hu4]
  rw [hrun]
  refine ⟨e4_N, e4_Sq, e4_W, e4_Qg, e4_C, e4_S, e4_Acc, ?_, ?_, ?_, ?_⟩
  · rw [e4_P, e4_N]
  · rw [e4_Q, e4_N]
  · rw [d_Qq, e3_N, e3_Sq]
  · rw [d_I, e4_Qu3, e3_W, e3_N, e3_Sq, e3_Qg, e3_C, e3_Idx]

/-- The trial round leaves the scan register either empty or holding the
current trial divisor: it never invents a value of its own. -/
private theorem semScanS_cases (S0 sq n d : Nat) (q : Prop) [Decidable q]
    (hS0 : S0 < M) (hd : d < M) :
    semScanS S0 sq n d (bitOf q) = S0 ∨ semScanS S0 sq n d (bitOf q) = d := by
  have hg : semScanG S0 sq n d (bitOf q)
      = bitOf (((S0 = 0 ∧ sq ≤ n) ∧ n % d = 0) ∧ q) := MMul_bit _ _
  unfold semScanS
  rw [hg, MS_one_bit]
  by_cases hP : ((S0 = 0 ∧ sq ≤ n) ∧ n % d = 0) ∧ q
  · right
    rw [bitOf_pos hP, bitOf_neg (fun t => t hP), MMul_zero_left,
      MMul_one_left hd, MA_zero_left hd]
  · left
    rw [bitOf_neg hP, bitOf_pos hP, MMul_one_left hS0, MMul_zero_left,
      MA_zero_right hS0]

/-- **The scan register's dichotomy, preserved by the pre-load stage.** -/
private theorem pre_scan_dichotomy (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : RegState) (hs : ∀ j, s j < M)
    (hS : s rS = 0 ∨ 2 ≤ s rS) :
    srun k s (msPre c) rS = 0 ∨ 2 ≤ srun k s (msPre c) rS := by
  have v_S := (msPre_vals c hok k hk s hs).2.2.2.2.2.1
  have hkmod : k % c.B < c.B := (ok_idx hok hk).2.2.1
  have hBlt := ok_Blt hok
  have h20 := two20_lt_M
  have hdM : k % c.B + 2 < M := by omega
  have hS0M : MMul (s rS) (bitOf (k % c.B ≠ 0)) < M := MMul_lt _ _
  rw [v_S]
  rcases semScanS_cases (MMul (s rS) (bitOf (k % c.B ≠ 0)))
      (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
      (k % c.B < c.B - 2) hS0M hdM with h | h
  · rw [h, MMul_bit_right _ (hs rS)]
    split
    · exact hS
    · exact Or.inl rfl
  · rw [h]; exact Or.inr (by omega)

/-- **The load index is in range**, and it never points at the cell this
candidate is about to write. -/
theorem msPre_index (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    srun k s.regs (msPre c) rI < c.limit + 1 + c.tab ∧
      srun k s.regs (msPre c) rI ≠ c.n0 + k / c.B := by
  obtain ⟨hregs, _, hidxlt, hscan⟩ := hinv
  obtain ⟨hkM, hkdiv, hkmod, hnle⟩ := ok_idx hok hk
  have hB3 : 3 ≤ c.B := ok_B3 hok
  have hn0 : 2 ≤ c.n0 := ok_n0 hok
  have hlimM : c.limit < M := ok_limM hok
  have hlim32 : c.limit < 2 ^ 32 := ok_lim32 hok
  have htab : c.tab ≤ 2 ^ 10 := ok_tab hok
  have hn2 : 2 ≤ c.n0 + k / c.B := Nat.le_trans hn0 (Nat.le_add_right c.n0 (k / c.B))
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnle hlimM
  have hbig : (2:Nat) ^ 32 + 1 + 2 ^ 10 < M := by decide
  obtain ⟨S, hSv⟩ : ∃ x, srun k s.regs (msPre c) rS = x := ⟨_, rfl⟩
  obtain ⟨Q, hQv⟩ : ∃ x, srun k s.regs (msPre c) rQ = x := ⟨_, rfl⟩
  have vals := msPre_vals c hok k hk s.regs hregs
  have v_Q : Q = semQ S (c.n0 + k / c.B) := by rw [← hQv, ← hSv]; exact vals.2.2.2.2.2.2.2.2.1
  have v_I : srun k s.regs (msPre c) rI =
      semI (bitOf (k % c.B < c.B - 2))
        ((c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2))
        (bitOf (k % c.B = c.B - 2)) Q
        (bitOf (k % c.B = c.B - 1)) (c.limit + 1) (s.regs rIdx) := by
    rw [← hQv]; exact vals.2.2.2.2.2.2.2.2.2.2
  by_cases ha : k % c.B < c.B - 2
  · -- work round: the index is ⌊n/d²⌋
    have hqqM : (c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2) < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
    have hI : srun k s.regs (msPre c) rI
        = (c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2) := by
      rw [v_I, bitOf_pos ha, bitOf_neg (show ¬ (k % c.B = c.B - 2) by omega),
        bitOf_neg (show ¬ (k % c.B = c.B - 1) by omega)]
      unfold semI
      rw [MMul_zero_left, MMul_zero_left, MMul_one_left hqqM, MA_MA_zero,
        MA_zero_right hqqM]
    have h4 : 4 ≤ (k % c.B + 2) * (k % c.B + 2) :=
      Nat.mul_le_mul (show 2 ≤ k % c.B + 2 by omega) (show 2 ≤ k % c.B + 2 by omega)
    have hsq1 : 1 < MMul (k % c.B + 2) (k % c.B + 2) := by
      have hBlt := ok_Blt hok
      have h20 := two20_lt_M
      have hdle : k % c.B + 2 ≤ 2 ^ 20 := by omega
      have hM40 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
      have hdd : (k % c.B + 2) * (k % c.B + 2) < M :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul hdle hdle) hM40
      have : MMul (k % c.B + 2) (k % c.B + 2) = (k % c.B + 2) * (k % c.B + 2) :=
        Nat.mod_eq_of_lt hdd
      rw [this]; omega
    have hlt : (c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2) < c.n0 + k / c.B :=
      Nat.div_lt_self (by omega) hsq1
    exact ⟨by rw [hI]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt hnle) (by omega),
      by rw [hI]; exact Nat.ne_of_lt hlt⟩
  · by_cases hb : k % c.B = c.B - 2
    · -- Möbius round: the index is q = n / p, and p ≥ 2
      have hQM : Q < M := by
        rw [v_Q]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
      have hI : srun k s.regs (msPre c) rI = Q := by
        rw [v_I, bitOf_neg ha, bitOf_pos hb,
          bitOf_neg (show ¬ (k % c.B = c.B - 1) by omega)]
        unfold semI
        rw [MMul_zero_left, MMul_one_left hQM, MMul_zero_left, MA_zero_left hQM,
          MA_zero_right hQM]
      have hSM : S < M := by rw [← hSv]; exact srun_regs_lt k (msPre c) s.regs hregs rS
      have hSdich : S = 0 ∨ 2 ≤ S := by
        rw [← hSv]; exact pre_scan_dichotomy c hok k hk s.regs hregs hscan
      have hp2 : 1 < semP S (c.n0 + k / c.B) := by
        rw [semP_eq hSM hnM]
        split
        · omega
        · rename_i hne
          rcases hSdich with h | h
          · exact absurd h hne
          · omega
      have hQlt : Q < c.n0 + k / c.B := by
        rw [v_Q]
        show (c.n0 + k / c.B) / semP S (c.n0 + k / c.B) < c.n0 + k / c.B
        exact Nat.div_lt_self (by omega) hp2
      exact ⟨by rw [hI]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hQlt hnle) (by omega),
        by rw [hI]; exact Nat.ne_of_lt hQlt⟩
    · -- commit round: the index is a log-constant cell, above the table
      have hcc : k % c.B = c.B - 1 := by omega
      have hmaM : c.limit + 1 + s.regs rIdx < M := by omega
      have hma : MA (c.limit + 1) (s.regs rIdx) = c.limit + 1 + s.regs rIdx :=
        Nat.mod_eq_of_lt hmaM
      have hI : srun k s.regs (msPre c) rI = c.limit + 1 + s.regs rIdx := by
        rw [v_I, bitOf_neg ha, bitOf_neg hb, bitOf_pos hcc]
        unfold semI
        rw [MMul_zero_left, MMul_zero_left, MMul_one_left (MA_lt _ _),
          MA_zero_right (show (0:Nat) < M by decide),
          MA_zero_left (MA_lt (c.limit + 1) (s.regs rIdx))]
        exact hma
      exact ⟨by rw [hI]; omega,
        by rw [hI]
           exact (Nat.ne_of_lt (Nat.lt_of_le_of_lt hnle (by omega))).symm⟩

/-- **The body is defined** at every index the loop visits. -/
private theorem msPre_sdefined (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : RegState) (hs : ∀ j, s j < M) :
    SAllDefined k s (msPre c) := by
  obtain ⟨hkM, _, hrB, hnle⟩ := ok_idx hok hk
  have hB0 := ok_B_pos hok
  have hBM := ok_BM hok
  have hn0M := ok_n0M hok
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnle (ok_limM hok)
  have hdM : k % c.B + 2 < M := by
    have h1 := ok_Blt hok
    have h2 := two20_lt_M
    omega
  have hB2M : c.B - 2 < M := by omega
  have hB1M : c.B - 1 < M := by omega
  have hlim1M : c.limit + 1 < M := by
    have h1 := ok_lim32 hok
    have h2 := two32_lt_M
    omega
  let u1 := srun k s (decodeBlock c)
  obtain ⟨hN1, hD1, hSq1, -, -, -, -, -⟩ :=
    decodeBlock_vals (c := c) k s (r := k % c.B) (n := c.n0 + k / c.B)
      (d := k % c.B + 2) rfl rfl rfl hkM hB0 hBM hn0M hnM hdM hB2M hB1M
  have hd0 : u1 rD ≠ 0 := by
    change srun k s (decodeBlock c) rD ≠ 0
    rw [hD1]
    omega
  have hsq0 : u1 rSq ≠ 0 := by
    change srun k s (decodeBlock c) rSq ≠ 0
    rw [hSq1]
    have hsq : (k % c.B + 2) * (k % c.B + 2) < M := by
      have h1 := ok_Blt hok
      have h2 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) h2
    unfold MMul
    rw [Nat.mod_eq_of_lt hsq]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have hdec : SAllDefined k s (decodeBlock c) := decodeBlock_defined k s hB0 hBM
  let u2 := srun k u1 scanBlock
  have hN2 : u2 rN = c.n0 + k / c.B :=
    (read_frame (k := k) (d := rN) (l := scanBlock) (by rfl) u1).trans hN1
  have hSq2 : u2 rSq = u1 rSq := read_frame (by rfl) u1
  have hscan : SAllDefined k u1 scanBlock := scanBlock_defined k u1 hd0
  let u3 := srun k u2 selectBlock
  have hN2M : u2 rN < M := by rw [hN2]; exact hnM
  have hN20 : u2 rN ≠ 0 := by
    rw [hN2]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by have := ok_n0 hok; omega)
      (Nat.le_add_right _ _))
  have hsel : SAllDefined k u2 selectBlock :=
    selectBlock_defined k u2 (srun_regs_lt k scanBlock u1
      (srun_regs_lt k (decodeBlock c) s hs) rS) hN2M hN20
  have hN3 : u3 rN = u2 rN := read_frame (by rfl) u2
  have hSq3 : u3 rSq = u2 rSq := read_frame (by rfl) u2
  have hidx : SAllDefined k u3 (indexBlock c) :=
    indexBlock_defined k u3 (by rw [hSq3, hSq2]; exact hsq0)
      (by rw [hN3]; exact hN2M)
  rw [show msPre c = decodeBlock c ++ (scanBlock ++ (selectBlock ++ indexBlock c))
    from by simp [msPre, List.append_assoc]]
  exact sAllDefined_append hdec (sAllDefined_append hscan (sAllDefined_append hsel hidx))

private theorem msPost_sdefined (c : Cfg) (hok : msOK c = true) (k : Nat)
    (u : RegState) (_hu : ∀ j, u j < M) (hN0 : u rN ≠ 0)
    (hN2 : 2 ≤ u rN) (hN32 : u rN ≤ 2 ^ 32)
    (hSq : u rSq ≠ 0) (hP : u rP ≠ 0) :
    SAllDefined k u (msPost c) := by
  have htab : c.tab ≠ 0 := by have := ok_tab0 hok; omega
  have htabM := ok_tabM hok
  let u1 := srun k u unpackBlock
  have d1 := unpackBlock_defined k u
  have hSq1 : u1 rSq = u rSq := by
    simpa [u1] using (read_frame (k := k) (d := rSq) (l := unpackBlock) (by rfl) u)
  have hP1 : u1 rP = u rP := by
    simpa [u1] using (read_frame (k := k) (d := rP) (l := unpackBlock) (by rfl) u)
  have hN1 : u1 rN = u rN := by
    simpa [u1] using (read_frame (k := k) (d := rN) (l := unpackBlock) (by rfl) u)
  let u2 := srun k u1 termBlock
  have d2 := termBlock_defined k u1 (by rw [hSq1]; exact hSq)
  have hP2 : u2 rP = u1 rP := by
    simpa [u2] using (read_frame (k := k) (d := rP) (l := termBlock) (by rfl) u1)
  have hN2' : u2 rN = u1 rN := by
    simpa [u2] using (read_frame (k := k) (d := rN) (l := termBlock) (by rfl) u1)
  let u3 := srun k u2 latchBlock
  have d3 := latchBlock_defined k u2
  have hP3 : u3 rP = u2 rP := by
    simpa [u3] using (read_frame (k := k) (d := rP) (l := latchBlock) (by rfl) u2)
  have hN3 : u3 rN = u2 rN := by
    simpa [u3] using (read_frame (k := k) (d := rN) (l := latchBlock) (by rfl) u2)
  let u4 := srun k u3 muBlock
  have d4 := muBlock_defined k u3 (by rw [hP3, hP2, hP1]; exact hP)
  have hN4 : u4 rN = u3 rN := by
    simpa [u4] using (read_frame (k := k) (d := rN) (l := muBlock) (by rfl) u3)
  let u5 := srun k u4 lbBlock
  have d5 := lbBlock_defined k u4 (by rw [hN4, hN3, hN2', hN1]; exact hN0)
  have hN5 : u5 rN = u4 rN := by
    simpa [u5] using (read_frame (k := k) (d := rN) (l := lbBlock) (by rfl) u4)
  let u6 := srun k u5 starBlock
  have d6 := starBlock_defined k u5
  have hN6 : u6 rN = u5 rN := by
    simpa [u6] using (read_frame (k := k) (d := rN) (l := starBlock) (by rfl) u5)
  let u7 := srun k u6 (gateBlock c)
  have d7 := gateBlock_defined (c := c) k u6
  have hN7 : u7 rN = u6 rN := by
    simpa [u7] using (read_frame (k := k) (d := rN) (l := gateBlock c) (by rfl) u6)
  let u8 := srun k u7 (ladderBlock c)
  have hN7eq : u7 rN = u rN := by rw [hN7, hN6, hN5, hN4, hN3, hN2', hN1]
  have d8 := ladderBlock_defined (c := c) k u7 (by rw [hN7eq]; exact hN2)
    (by rw [hN7eq]; exact hN32)
  let u9 := srun k u8 productBlock
  have d9 := productBlock_defined k u8
  let u10 := srun k u9 (badBlock c)
  have d10 := badBlock_defined (c := c) k u9
  have d11 := updateBlock_defined (c := c) k u10 htab htabM
  rw [show msPost c = unpackBlock ++ (termBlock ++ (latchBlock ++ (muBlock ++
      (lbBlock ++ (starBlock ++ (gateBlock c ++ (ladderBlock c ++
        (productBlock ++ (badBlock c ++ updateBlock c)))))))))
    from by simp [msPost, List.append_assoc]]
  exact sAllDefined_append d1 (sAllDefined_append d2 (sAllDefined_append d3
    (sAllDefined_append d4 (sAllDefined_append d5 (sAllDefined_append d6
      (sAllDefined_append d7 (sAllDefined_append d8 (sAllDefined_append d9
        (sAllDefined_append d10 d11)))))))))

theorem msBody_defined (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    AllDefined (c.limit + 1 + c.tab) k s (msBody c) := by
  obtain ⟨hregs, harr, hidx, hscan⟩ := hinv
  obtain ⟨_, _, _, hnle⟩ := ok_idx hok hk
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnle (ok_limM hok)
  have hn2 : 2 ≤ c.n0 + k / c.B :=
    Nat.le_trans (ok_n0 hok) (Nat.le_add_right _ _)
  have hn0 : c.n0 + k / c.B ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn2)
  have hn32 : c.n0 + k / c.B ≤ 2 ^ 32 :=
    Nat.le_trans hnle (Nat.le_of_lt (ok_lim32 hok))
  have hpidx := msPre_index c hok k hk s ⟨hregs, harr, hidx, hscan⟩
  let pre := srun k s.regs (msPre c)
  let u := RegState.set pre rV (s.arr (pre rI))
  have hpre := msPre_vals c hok k hk s.regs hregs
  have hu_keep (j : Nat) (hj : j ≠ rV) : u j = pre j := by
    simp [u, RegState.set, hj]
  have hu : ∀ j, u j < M := by
    intro j
    simp only [u, RegState.set]
    split
    · exact harr _
    · exact srun_regs_lt k (msPre c) s.regs hregs j
  have huN : u rN = c.n0 + k / c.B :=
    (hu_keep rN (by decide)).trans hpre.1
  have huSq : u rSq = MMul (k % c.B + 2) (k % c.B + 2) := by
    exact (hu_keep rSq (by decide)).trans hpre.2.1
  have huP : u rP = semP (u rS) (u rN) := by
    calc
      u rP = pre rP := hu_keep rP (by decide)
      _ = semP (pre rS) (c.n0 + k / c.B) := hpre.2.2.2.2.2.2.2.1
      _ = semP (u rS) (u rN) := by rw [hu_keep rS (by decide), huN]
  have huSq0 : u rSq ≠ 0 := by
    rw [huSq]
    have hr := (ok_idx hok hk).2.2.1
    have hs : (k % c.B + 2) * (k % c.B + 2) < M := by
      have h2 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (by have := ok_Blt hok; omega)
        (by have := ok_Blt hok; omega)) h2
    unfold MMul
    rw [Nat.mod_eq_of_lt hs]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have huP0 : u rP ≠ 0 := by
    rw [huP]
    exact semP_ne_zero (hu rS) (by rw [huN]; exact hnM) (by rw [huN]; exact hn0)
  have hpost := msPost_sdefined c hok k u hu (by rw [huN]; exact hn0)
    (by rw [huN]; exact hn2) (by rw [huN]; exact hn32) huSq0 huP0
  have hstoreN : srun k u (msPost c) rN < c.limit + 1 + c.tab := by
    rw [read_frame (k := k) (d := rN) (l := msPost c) (by rfl) u, huN]
    exact Nat.lt_of_le_of_lt hnle (by have := ok_tab0 hok; omega)
  have hloadState :
      arun k (arun k s (lift (msPre c))) [.load rV rI] = ⟨u, s.arr⟩ := by
    rw [arun_lift]
    rfl
  rw [show msBody c = lift (msPre c) ++
      ([.load rV rI] ++ (lift (msPost c) ++ [.store rN rCell]))
    from by simp [msBody, List.append_assoc],
    AllDefined_append]
  refine ⟨(allDefined_lift _ _ _ _).mpr (msPre_sdefined c hok k hk s.regs hregs), ?_⟩
  rw [AllDefined_append]
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · change (arun k s (lift (msPre c))).regs rI < c.limit + 1 + c.tab
    rw [arun_lift_regs]
    exact hpidx.1
  rw [hloadState]
  rw [AllDefined_append]
  refine ⟨?_, ⟨?_, trivial⟩⟩
  · exact (allDefined_lift _ _ _ _).mpr hpost
  · change (arun k ⟨u, s.arr⟩ (lift (msPost c))).regs rN < c.limit + 1 + c.tab
    rw [arun_lift_regs]
    exact hstoreN

/-- **The body computes `msRound`.** -/
theorem msBody_obs (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    obsR (arun k s (msBody c)) = msRound c k (obsR s) := by
  obtain ⟨hregs, harr, -, -⟩ := hinv
  obtain ⟨_, _, _, hnle⟩ := ok_idx hok hk
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnle (ok_limM hok)
  have hn2 : 2 ≤ c.n0 + k / c.B :=
    Nat.le_trans (ok_n0 hok) (Nat.le_add_right _ _)
  have hn0 : c.n0 + k / c.B ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn2)
  have hn32 : c.n0 + k / c.B ≤ 2 ^ 32 :=
    Nat.le_trans hnle (Nat.le_of_lt (ok_lim32 hok))
  let pre := srun k s.regs (msPre c)
  let u := RegState.set pre rV (s.arr (pre rI))
  have hp := msPre_vals c hok k hk s.regs hregs
  have keep (j : Nat) (hj : j ≠ rV) : u j = pre j := by
    simp [u, RegState.set, hj]
  have old (j : Nat) (hj : j ≠ rV)
      (hw : writes j (msPre c) = false := by rfl) : u j = s.regs j := by
    exact (keep j hj).trans (read_frame hw s.regs)
  have uN : u rN = c.n0 + k / c.B := (keep rN (by decide)).trans hp.1
  have uSq : u rSq = MMul (k % c.B + 2) (k % c.B + 2) :=
    (keep rSq (by decide)).trans hp.2.1
  have uW : u rW = bitOf (k % c.B < c.B - 2) :=
    (keep rW (by decide)).trans hp.2.2.1
  have uQg : u rQg = bitOf (k % c.B = c.B - 2) :=
    (keep rQg (by decide)).trans hp.2.2.2.1
  have uC : u rC = bitOf (k % c.B = c.B - 1) :=
    (keep rC (by decide)).trans hp.2.2.2.2.1
  have uS := (keep rS (by decide)).trans hp.2.2.2.2.2.1
  have uAcc := (keep rAcc (by decide)).trans hp.2.2.2.2.2.2.1
  have uP := (keep rP (by decide)).trans hp.2.2.2.2.2.2.2.1
  have uQ := (keep rQ (by decide)).trans hp.2.2.2.2.2.2.2.2.1
  have uQq := (keep rQq (by decide)).trans hp.2.2.2.2.2.2.2.2.2.1
  have uV : u rV = s.arr (pre rI) := by simp [u, RegState.set]
  have hu : ∀ j, u j < M := by
    intro j
    simp only [u, RegState.set]
    split
    · exact harr _
    · exact srun_regs_lt k (msPre c) s.regs hregs j
  have uSq0 : u rSq ≠ 0 := by
    rw [uSq]
    have hs : (k % c.B + 2) * (k % c.B + 2) < M := by
      have h2 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (by have := ok_Blt hok; omega)
        (by have := ok_Blt hok; omega)) h2
    unfold MMul
    rw [Nat.mod_eq_of_lt hs]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have uP0 : u rP ≠ 0 := by
    rw [uP]
    exact semP_ne_zero (srun_regs_lt k (msPre c) s.regs hregs rS) hnM hn0
  rw [msBody_arun]
  calc
    obsR ⟨srun k u (msPost c),
        fun j => if j = srun k u (msPost c) rN
          then srun k u (msPost c) rCell else s.arr j⟩ = msPostR c u s.arr :=
      msPost_obs c hok k u s.arr hu (by rw [uN]; exact hn0)
        (by rw [uN]; exact hn2) (by rw [uN]; exact hn32) uSq0 uP0
    _ = msRound c k (obsR s) := by
      have uBad : u rBad = s.regs rBad := old rBad (by decide)
      have uLb : u rLb = s.regs rLb := old rLb (by decide)
      have uLam : u rLam = s.regs rLam := old rLam (by decide)
      have uIdx : u rIdx = s.regs rIdx := old rIdx (by decide)
      have uBs : u rBs = s.regs rBs := old rBs (by decide)
      have uMax : u rMax = s.regs rMax := old rMax (by decide)
      have uCell : u rCell = s.regs rCell := old rCell (by decide)
      have uMuQ : u rMuQ = s.regs rMuQ := old rMuQ (by decide)
      have pS := hp.2.2.2.2.2.1
      have pQ := hp.2.2.2.2.2.2.2.2.1
      have pI := hp.2.2.2.2.2.2.2.2.2.2
      ext j <;> simp only [msPostR, msRound, obsR] <;>
        simp only [uN, uSq, uW, uQg, uC, uS, uAcc, uP, uQ, uQq,
          uV, uBad, uLb, uLam, uIdx, uBs, uMax, uCell, uMuQ, pre, pS, pQ, pI]

/-- **The invariant is preserved.** -/
theorem msBody_inv (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (s : AState) (hinv : MSInv c s) :
    MSInv c (arun k s (msBody c)) := by
  have hinv0 := hinv
  obtain ⟨hregs, harr, -, hscan⟩ := hinv
  let pre := srun k s.regs (msPre c)
  let u := RegState.set pre rV (s.arr (pre rI))
  have keepS : u rS = pre rS := by
    simp [u, RegState.set, show rS ≠ rV by decide]
  have hu : ∀ j, u j < M := by
    intro j
    simp only [u, RegState.set]
    split
    · exact harr _
    · exact srun_regs_lt k (msPre c) s.regs hregs j
  have hfin : ∀ j, srun k u (msPost c) j < M :=
    srun_regs_lt k (msPost c) u hu
  have hfinS : srun k u (msPost c) rS = pre rS :=
    (read_frame (k := k) (d := rS) (l := msPost c) (by rfl) u).trans keepS
  have hpreScan : pre rS = 0 ∨ 2 ≤ pre rS := by
    exact pre_scan_dichotomy c hok k hk s.regs hregs hscan
  have hfinalScan : srun k u (msPost c) rS = 0 ∨
      2 ≤ srun k u (msPost c) rS := by
    rw [hfinS]
    exact hpreScan
  have hidxEq := congrArg RSt.idx (msBody_obs c hok k hk s hinv0)
  rw [msBody_arun] at hidxEq
  change srun k u (msPost c) rIdx = (msRound c k (obsR s)).idx at hidxEq
  rw [msBody_arun]
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro i
    change (if i = srun k u (msPost c) rN
      then srun k u (msPost c) rCell else s.arr i) < M
    split
    · exact hfin rCell
    · exact harr i
  · change srun k u (msPost c) rIdx < c.tab
    rw [hidxEq]
    simp only [msRound, semIdx]
    exact Nat.mod_lt _ (by have := ok_tab0 hok; omega)
  · simpa only [pre, u] using hfinalScan

end LeanCompCert.Ports.RamareMStar140M
