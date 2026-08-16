/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.FixedMulBlock
import LeanCompCert.Ports.TwosComplementBlock

/-!
# The complex product, assembled

Every leaf is proved: `sfpMulG` for a signed product, `tcOfSignG` for the
representation change, `tcSubG`/`tcAddG` for the accumulator arithmetic.  This
wires them together.

## Concrete registers, on purpose

★ Every other block in this development is parameterised by register numbers,
which is right for a primitive and wrong here.  Assembling four multiplies
needs each one's scratch to be disjoint from every earlier one's *outputs*, and
carried as hypotheses that is roughly sixty `≠`s at the call site.  Fixed
numbers turn all of them into `decide`, which is the same trade `divP18S`
makes upstream.

⚠ The cost is that the allocation is now part of the interface: a caller must
place its inputs at these registers.  That is a real constraint and it is
stated in `reBlock`'s docstring rather than left implicit.

## Scope

This module does the **real part**, `x.re·y.re − x.im·y.im`.  The imaginary
part is the same shape with `tcAddG` and the operands crossed; it is not done
here, and saying so is better than implying the complex product is finished.
-/

namespace LeanCompCert.Ports.ComplexMulBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.FixedMul
open LeanCompCert.Verified.TwosComplement
open LeanCompCert.Verified.BlockCompose
open LeanCompCert.Ports.FixedMulBlock
open LeanCompCert.Ports.TwosComplementBlock
open LeanCompCert.Ports.Section413G1Denote

/-- Discharges the register side-conditions.  `Distinct8`/`NotIn8` are plain
`def`s, so `decide` cannot see through them without unfolding first. -/
local macro "regdec" : tactic => `(tactic|
  first
    | decide
    | (simp only [LeanCompCert.Ports.Section413G1Denote.Distinct8,
        LeanCompCert.Ports.Section413G1Denote.NotIn8]; decide))

/-! ### The allocation -/

abbrev xrn : Nat := 300  -- `x.re` sign
abbrev xrm : Nat := 301  -- `x.re` magnitude
abbrev xin : Nat := 302
abbrev xim : Nat := 303
abbrev yrn : Nat := 304
abbrev yrm : Nat := 305
abbrev yin : Nat := 306
abbrev yim : Nat := 307

abbrev prrn : Nat := 310  -- `x.re·y.re`, sign-magnitude
abbrev prrm : Nat := 311
abbrev piin : Nat := 312  -- `x.im·y.im`
abbrev piim : Nat := 313

abbrev arr : Nat := 320   -- the two products, two's complement
abbrev aii : Nat := 321
abbrev outRe : Nat := 330

abbrev rlo : Nat := 340
abbrev rhi : Nat := 341
abbrev tt0 : Nat := 342
abbrev tt1 : Nat := 343
abbrev u0 : Nat := 344
abbrev u1 : Nat := 345
abbrev c0 : Nat := 350
abbrev c1 : Nat := 351
abbrev c2 : Nat := 352
abbrev c3 : Nat := 353
abbrev c4 : Nat := 354
abbrev c5 : Nat := 355
abbrev c6 : Nat := 356
abbrev c7 : Nat := 357

/-! ### The register side-conditions, once

⚠ Proved as named lemmas rather than inline.  Deciding `Distinct8` at each of
the forty-odd call sites below made the kernel time out; deciding it once does
not. -/

theorem hD8 : Distinct8 c0 c1 c2 c3 c4 c5 c6 c7 := by
  simp only [LeanCompCert.Ports.Section413G1Denote.Distinct8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [c0, c1, c2, c3, c4, c5, c6, c7] <;> omega

theorem hNI {r : Nat} (h : r < 350) : NotIn8 r c0 c1 c2 c3 c4 c5 c6 c7 := by
  simp only [LeanCompCert.Ports.Section413G1Denote.NotIn8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [c0, c1, c2, c3, c4, c5, c6, c7] <;> omega

/-! ### The block -/

/-- `x.re · y.re`, into `prrn`/`prrm`. -/
def mulRR (S : Nat) : List Instr :=
  sfpMulG S xrn xrm yrn yrm prrn prrm rlo rhi tt0 tt1 c0 c1 c2 c3 c4 c5 c6 c7

/-- `x.im · y.im`, into `piin`/`piim`.  Reuses all the scratch. -/
def mulII (S : Nat) : List Instr :=
  sfpMulG S xin xim yin yim piin piim rlo rhi tt0 tt1 c0 c1 c2 c3 c4 c5 c6 c7

/-- **The real part of the complex product.**

Inputs must be at `xrn`/`xrm`/`xin`/`xim` and `yrn`/`yrm`/`yin`/`yim`, sign
bits in `{0,1}`; the result lands in `outRe` in two's complement. -/
def reBlock (S : Nat) : List Instr :=
  mulRR S ++ mulII S
    ++ tcOfSignG prrn prrm arr u0 u1
    ++ tcOfSignG piin piim aii u0 u1
    ++ tcSubG arr aii outRe

/-! ### Frames

With concrete registers each of these is a decision procedure. -/

/-- ★ Every destination of `mulRR` is `≥ 310`, so one bound covers every
frame obligation against it. -/
theorem mulRR_preserves (S : Nat) {r : Nat} (h : r < 310) :
    Preserves (mulRR S) r := by
  refine sfpMulG_preserves ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [prrn, prrm, rlo, rhi, tt0, tt1, c0, c1, c2, c3, c4, c5, c6,
      c7] <;> omega

/-- Every destination of `mulII` is `≥ 312`. -/
theorem mulII_preserves (S : Nat) {r : Nat} (h : r < 312) :
    Preserves (mulII S) r := by
  refine sfpMulG_preserves ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [piin, piim, rlo, rhi, tt0, tt1, c0, c1, c2, c3, c4, c5, c6,
      c7] <;> omega

theorem convRR_preserves {r : Nat} (h0 : r ≠ arr) (h1 : r ≠ u0)
    (h2 : r ≠ u1) : Preserves (tcOfSignG prrn prrm arr u0 u1) r :=
  tcOfSignG_preserves (Ne.symm h0) (Ne.symm h1) (Ne.symm h2)

theorem convII_preserves {r : Nat} (h0 : r ≠ aii) (h1 : r ≠ u0)
    (h2 : r ≠ u1) : Preserves (tcOfSignG piin piim aii u0 u1) r :=
  tcOfSignG_preserves (Ne.symm h0) (Ne.symm h1) (Ne.symm h2)

/-! ### The intermediate states

⚠ Named as definitions rather than with `set`, which is a Mathlib tactic and
does not exist here. -/

private def st1 (k : Nat) (s : RegState) (S : Nat) : RegState :=
  srun k s (mulRR S)

private def st2 (k : Nat) (s : RegState) (S : Nat) : RegState :=
  srun k (st1 k s S) (mulII S)

private def st3 (k : Nat) (s : RegState) (S : Nat) : RegState :=
  srun k (st2 k s S) (tcOfSignG prrn prrm arr u0 u1)

private def st4 (k : Nat) (s : RegState) (S : Nat) : RegState :=
  srun k (st3 k s S) (tcOfSignG piin piim aii u0 u1)

/-! ### The specification -/

set_option maxHeartbeats 2000000 in
/-- **The real part of the complex product, emitted and proved.**

The right-hand side is exactly what `SignedFixedMul.sfpMul` and
`TwosComplement.tcOfSign` compute, so this joins the emitted code to the
proved arithmetic. -/
theorem reBlock_spec (k : Nat) (s : RegState) (S : Nat) (hS : S ≤ 64)
    (hs : ∀ j, s j < M)
    (hxr : s xrn ≤ 1) (hyr : s yrn ≤ 1)
    (hxi : s xin ≤ 1) (hyi : s yin ≤ 1)
    (hfit1 : (hl (s xrm) (s yrm)).2 < 2 ^ S)
    (hfit2 : (hl (s xim) (s yim)).2 < 2 ^ S) :
    srun k s (reBlock S) outRe
      = (tcOfSign (if s xrn = s yrn then 0 else 1) (fpMul S (s xrm) (s yrm))
          + (M - tcOfSign (if s xin = s yin then 0 else 1)
                  (fpMul S (s xim) (s yim)))) % M := by
  have hs1M : ∀ j, st1 k s S j < M := srun_lt_of_lt k _ s hs
  have hs1pre : ∀ j, j < 310 → st1 k s S j = s j := fun j hj =>
    srun_preserves k s (mulRR_preserves S hj)
  have h1m : st1 k s S prrm = fpMul S (s xrm) (s yrm) :=
    sfpMulG_mag k s S xrn xrm yrn yrm prrn prrm rlo rhi tt0 tt1
      c0 c1 c2 c3 c4 c5 c6 c7 hS hD8 (hNI (by decide)) (hNI (by decide))
      (hNI (by decide)) (hNI (by decide)) (by regdec) hs (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) hfit1
  have h1n : st1 k s S prrn = if s xrn = s yrn then 0 else 1 :=
    sfpMulG_sign k s S xrn xrm yrn yrm prrn prrm rlo rhi tt0 tt1
      c0 c1 c2 c3 c4 c5 c6 c7 hxr hyr (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
  have hs2M : ∀ j, st2 k s S j < M := srun_lt_of_lt k _ _ hs1M
  have hs2pre : ∀ j, j < 312 → st2 k s S j = st1 k s S j := fun j hj =>
    srun_preserves k _ (mulII_preserves S hj)
  have h2m : st2 k s S piim = fpMul S (s xim) (s yim) := by
    have hh := sfpMulG_mag k (st1 k s S) S xin xim yin yim piin piim
      rlo rhi tt0 tt1 c0 c1 c2 c3 c4 c5 c6 c7 hS hD8 (hNI (by decide))
      (hNI (by decide)) (hNI (by decide)) (hNI (by decide)) (by regdec)
      hs1M (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec)
      (by rw [hs1pre xim (by regdec), hs1pre yim (by regdec)]; exact hfit2)
    rw [st2, mulII, hh, hs1pre xim (by regdec), hs1pre yim (by regdec)]
  have h2n : st2 k s S piin = if s xin = s yin then 0 else 1 := by
    have hh := sfpMulG_sign k (st1 k s S) S xin xim yin yim piin piim
      rlo rhi tt0 tt1 c0 c1 c2 c3 c4 c5 c6 c7
      (by rw [hs1pre xin (by regdec)]; exact hxi)
      (by rw [hs1pre yin (by regdec)]; exact hyi)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by regdec) (by regdec)
    rw [st2, mulII, hh, hs1pre xin (by regdec), hs1pre yin (by regdec)]
  have hs3M : ∀ j, st3 k s S j < M := srun_lt_of_lt k _ _ hs2M
  have h3arr : st3 k s S arr = tcOfSign (st2 k s S prrn) (st2 k s S prrm) :=
    tcOfSignG_spec k (st2 k s S) prrn prrm arr u0 u1 (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by rw [hs2pre prrn (by regdec), h1n]; split <;> omega)
      (hs2M prrm)
  have h3piin : st3 k s S piin = st2 k s S piin :=
    srun_preserves k _ (convRR_preserves (by regdec) (by regdec) (by regdec))
  have h3piim : st3 k s S piim = st2 k s S piim :=
    srun_preserves k _ (convRR_preserves (by regdec) (by regdec) (by regdec))
  have h4aii : st4 k s S aii = tcOfSign (st3 k s S piin) (st3 k s S piim) :=
    tcOfSignG_spec k (st3 k s S) piin piim aii u0 u1 (by regdec) (by regdec)
      (by regdec) (by regdec) (by regdec) (by regdec) (by regdec)
      (by rw [h3piin, h2n]; split <;> omega) (hs3M piim)
  have h4arr : st4 k s S arr = st3 k s S arr :=
    srun_preserves k _ (convII_preserves (by regdec) (by regdec) (by regdec))
  have hdecomp : srun k s (reBlock S) outRe
      = srun k (st4 k s S) (tcSubG arr aii outRe) outRe := by
    rw [reBlock, srun_append, srun_append, srun_append, srun_append,
      st4, st3, st2, st1]
  rw [hdecomp, tcSubG_spec, h4arr, h4aii, h3arr, h3piin, h3piim,
    hs2pre prrn (by regdec), hs2pre prrm (by regdec), h1n, h1m, h2n, h2m]

#print axioms mulRR_preserves
#print axioms reBlock_spec

end LeanCompCert.Ports.ComplexMulBlock
