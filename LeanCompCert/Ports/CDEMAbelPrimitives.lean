import LeanCompCert.Ports.AddWidePort
import LeanCompCert.Ports.Section413G1Denote

/-!
# Scalar arithmetic used by the CDEM Abel scan

`CDEMAbelScan` emits three branchless scalar combinators inside its array
program: a conditional select, a 64-by-64 to 128-bit product, and a two-limb
addition.  The arithmetic proofs already existed in the generic wide-word
library and in the Section 4.13 denotation development, but the CDEM scan had
no theorem stated against its own instruction lists.

This file supplies that missing machine-to-model layer.  Each theorem below
is about `arun` of the literal block used by `CDEMAbelScan`; in particular the
array-frame conjunct records that these arithmetic stages cannot silently
change the sieve plane.  The product theorem is exact over `Nat`, and the
addition theorem is exact modulo `2^128`, with a no-wrap corollary for the
accumulator invariant.
-/

namespace LeanCompCert.Ports.CDEMAbelPrimitives

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports

/-! ## Branchless selection -/

/-- The actual CDEM selector returns `x` at gate one and `y` at gate zero,
and cannot modify the array. -/
theorem muxBody_arun (k : Nat) (st : AState) (dst gate x y sc : Nat)
    (hd : sc ≠ dst) (hgt : sc ≠ gate) (hx : sc ≠ x) (hy : sc ≠ y)
    (hg : st.regs gate ≤ 1) (hword : ∀ j, st.regs j < M) :
    let out := arun k st (CDEMAbelScan.muxBody dst gate x y sc)
    out.regs dst = (if st.regs gate = 1 then st.regs x else st.regs y) ∧
      out.arr = st.arr := by
  rw [Section413G1Denote.muxBody_lift, arun_lift]
  exact ⟨Section413G1Denote.muxS_spec k st.regs dst gate x y sc
    hd hgt hx hy hg hword, rfl⟩

/-! ## Wide multiplication -/

/-- The CDEM half-limb multiplier returns the library's proved limb pair and
does not modify the array. -/
theorem mulWideBody_arun_limbs (k : Nat) (st : AState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : Section413G1Denote.NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : Section413G1Denote.NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, st.regs j < M) :
    let out := arun k st
      (CDEMAbelScan.mulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (out.regs rlo, out.regs rhi) = MulWide.hl (st.regs ra) (st.regs rb) ∧
      out.arr = st.arr := by
  rw [Section413G1Denote.mulWideBody_lift, arun_lift]
  have h := Section413G1Denote.mulWideG_hl k st.regs ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hrlo hrhi hlohi hword
  exact ⟨Prod.ext h.1 h.2, rfl⟩

/-- Consequently, the two output registers of the literal CDEM block
recombine to the exact 128-bit product of its input registers. -/
theorem mulWideBody_arun_exact (k : Nat) (st : AState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : Section413G1Denote.NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : Section413G1Denote.NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, st.regs j < M) :
    let out := arun k st
      (CDEMAbelScan.mulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)
    out.regs rlo + MulWide.B64 * out.regs rhi = st.regs ra * st.regs rb ∧
      out.arr = st.arr := by
  have hrun := mulWideBody_arun_limbs k st ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hrlo hrhi hlohi hword
  have hMB : M = MulWide.B64 := by decide
  have hspec := MulWide.hl_spec (st.regs ra) (st.regs rb)
    (by rw [← hMB]; exact hword ra)
    (by rw [← hMB]; exact hword rb)
  dsimp only at hrun ⊢
  have hlo := congrArg Prod.fst hrun.1
  have hhi := congrArg Prod.snd hrun.1
  constructor
  · simp only at hlo hhi
    rw [hlo, hhi]
    exact hspec.1
  · exact hrun.2

/-! ## Wide accumulation -/

/-- Scalar view of the literal CDEM accumulator.  Its argument order differs
from `AddWidePort.addWideBody`, so keeping this bridge explicit prevents a
carry/addend permutation from being hidden by elaboration. -/
def addWideS (accLo accHi alo ahi carry : Nat) : List Instr :=
  AddWidePort.addWideBody accLo accHi carry alo ahi

theorem addWideBody_lift (accLo accHi alo ahi carry : Nat) :
    CDEMAbelScan.addWideBody accLo accHi alo ahi carry =
      lift (addWideS accLo accHi alo ahi carry) := rfl

/-- The scalar view of CDEM's four accumulator instructions computes
`Verified.AddWide.addWide`, including the frame for every non-output register. -/
theorem addWideS_run (k : Nat) (s : RegState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi) :
    let out := srun k s (addWideS accLo accHi alo ahi carry)
    (out accLo, out accHi) = AddWide.addWide (s accLo, s accHi) (s alo, s ahi) ∧
      ∀ j, j ≠ accLo → j ≠ accHi → j ≠ carry → out j = s j := by
  have hnodiv : ∀ i ∈ addWideS accLo accHi alo ahi carry, NoDivI i = true := by
    intro i hi
    simp only [addWideS, AddWidePort.addWideBody, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  have hmachine := srun_correct k _ hnodiv s
  obtain ⟨s', hdenote, hlo, hhi, hframe⟩ :=
    AddWidePort.addWideBody_denote accLo accHi carry alo ahi hr k s
  have heq : s' = srun k s (addWideS accLo accHi alo ahi carry) := by
    apply Option.some.inj
    exact hdenote.symm.trans hmachine
  subst s'
  exact ⟨Prod.ext hlo hhi, hframe⟩

/-- The literal CDEM accumulator computes wide addition and cannot modify the
array. -/
theorem addWideBody_arun (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    (out.regs accLo, out.regs accHi) =
        AddWide.addWide (st.regs accLo, st.regs accHi) (st.regs alo, st.regs ahi) ∧
      out.arr = st.arr ∧
      ∀ j, j ≠ accLo → j ≠ accHi → j ≠ carry → out.regs j = st.regs j := by
  rw [addWideBody_lift, arun_lift]
  have h := addWideS_run k st.regs accLo accHi alo ahi carry hr
  exact ⟨h.1, rfl, h.2⟩

/-- Recombining the CDEM accumulator's output limbs gives addition modulo
`2^128`. -/
theorem addWideBody_arun_mod (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi)
    (hacc : AddWide.Ok (st.regs accLo, st.regs accHi))
    (hadd : AddWide.Ok (st.regs alo, st.regs ahi)) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    AddWide.wval (out.regs accLo, out.regs accHi) =
      (AddWide.wval (st.regs accLo, st.regs accHi) +
        AddWide.wval (st.regs alo, st.regs ahi)) % AddWide.B128 := by
  have hrun := addWideBody_arun k st accLo accHi alo ahi carry hr
  dsimp only at hrun ⊢
  rw [hrun.1]
  exact AddWide.addWide_spec _ _ hacc hadd

/-- Under the scan's no-overflow invariant, CDEM's accumulator is ordinary
exact natural-number addition. -/
theorem addWideBody_arun_exact (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi)
    (hacc : AddWide.Ok (st.regs accLo, st.regs accHi))
    (hadd : AddWide.Ok (st.regs alo, st.regs ahi))
    (hfit : AddWide.wval (st.regs accLo, st.regs accHi) +
      AddWide.wval (st.regs alo, st.regs ahi) < AddWide.B128) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    AddWide.wval (out.regs accLo, out.regs accHi) =
      AddWide.wval (st.regs accLo, st.regs accHi) +
        AddWide.wval (st.regs alo, st.regs ahi) := by
  dsimp only
  rw [addWideBody_arun_mod k st accLo accHi alo ahi carry hr hacc hadd,
    Nat.mod_eq_of_lt hfit]

end LeanCompCert.Ports.CDEMAbelPrimitives
