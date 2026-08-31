/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.FixedMulBlock
import LeanCompCert.Ports.RamareCombined100MQuotient
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Exact fixed-point products for the Ramaré 100M sweep

The production log words are approximately 36 bits at scale `2^32`, so their
product needs approximately 73 bits.  This module denotes the emitted
64x64-to-128 multiply and its exact floor/ceiling projection at scale `2^32`.

It is intentionally separate from the large sweep module.  The expensive
instruction proof is compiled once here; consumers compose its theorem instead
of normalizing the widening circuit inside a whole-window invariant.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ExactProduct

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift_regs)

/-! The register allocation is the production allocation from
`RamareCombined100MSeamBlock`.  Keeping it here makes all aliasing obligations
closed propositions, checked once. -/

def rA : Nat := 263
def rB : Nat := 264
def rT0 : Nat := 265
def rT1 : Nat := 266
def rLo : Nat := 287
def rHi : Nat := 288
def rProd : Nat := 289
def s0 : Nat := 267
def s1 : Nat := 268
def s2 : Nat := 269
def s3 : Nat := 270
def s4 : Nat := 271
def s5 : Nat := 276
def s6 : Nat := 277
def s7 : Nat := 278

def floorBlock : List AInstr :=
  lift (LeanCompCert.Ports.FixedMulBlock.fpMulG 32 rA rB rProd rLo rHi rT0 rT1
    s0 s1 s2 s3 s4 s5 s6 s7)

private theorem mulWide_hl (k : Nat) (st : AState)
    (hw : ∀ j, st.regs j < M) :
    let block := LeanCompCert.Ports.Section413G1Denote.mulWideG
      4294967295 4294967296 rA rB rLo rHi s0 s1 s2 s3 s4 s5 s6 s7
    LeanCompCert.Verified.InstrBlock.srun k st.regs block rLo =
        (LeanCompCert.Verified.MulWide.hl (st.regs rA) (st.regs rB)).1 ∧
      LeanCompCert.Verified.InstrBlock.srun k st.regs block rHi =
        (LeanCompCert.Verified.MulWide.hl (st.regs rA) (st.regs rB)).2 := by
  apply LeanCompCert.Ports.Section413G1Denote.mulWideG_hl
  · simp [LeanCompCert.Ports.Section413G1Denote.Distinct8,
      s0, s1, s2, s3, s4, s5, s6, s7]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rA, s0, s1, s2, s3, s4, s5, s6, s7]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rB, s0, s1, s2, s3, s4, s5, s6, s7]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rLo, s0, s1, s2, s3, s4, s5, s6, s7]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rHi, s0, s1, s2, s3, s4, s5, s6, s7]
  · decide
  · exact hw

theorem floorBlock_run (k : Nat) (st : AState)
    (hw : ∀ j, st.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (st.regs rA) (st.regs rB)).2 < 2 ^ 32) :
    (arun k st floorBlock).regs rProd = mulLower (st.regs rA) (st.regs rB) := by
  have hMB : M = LeanCompCert.Verified.MulWide.B64 := rfl
  rw [floorBlock, arun_lift_regs]
  rw [LeanCompCert.Ports.FixedMulBlock.fpMulG_spec k st.regs 32 rA rB rProd
    rLo rHi rT0 rT1 s0 s1 s2 s3 s4 s5 s6 s7 (by decide)
    (by simp [LeanCompCert.Ports.Section413G1Denote.Distinct8,
      s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rA, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rB, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rLo, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [LeanCompCert.Ports.Section413G1Denote.NotIn8,
      rHi, s0, s1, s2, s3, s4, s5, s6, s7])
    (by decide) hw (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hfit]
  rw [LeanCompCert.Verified.FixedMul.fpMul_eq 32 _ _ (by decide)
    (hMB ▸ hw rA) (hMB ▸ hw rB)]
  simp [mulLower, coeffScale]

theorem floorBlock_low (k : Nat) (st : AState) (hw : ∀ j, st.regs j < M) :
    (arun k st floorBlock).regs rLo =
      (LeanCompCert.Verified.MulWide.hl (st.regs rA) (st.regs rB)).1 := by
  rw [floorBlock, arun_lift_regs,
    LeanCompCert.Ports.FixedMulBlock.fpMulG,
    LeanCompCert.Verified.InstrBlock.srun_append,
    LeanCompCert.Ports.FixedMulBlock.fpMulTail_frame k _ 32 rProd rLo rHi
      rT0 rT1 rLo (by decide) (by decide) (by decide)]
  exact (mulWide_hl k st hw).1

theorem floorBlock_high (k : Nat) (st : AState) (hw : ∀ j, st.regs j < M) :
    (arun k st floorBlock).regs rHi =
      (LeanCompCert.Verified.MulWide.hl (st.regs rA) (st.regs rB)).2 := by
  rw [floorBlock, arun_lift_regs,
    LeanCompCert.Ports.FixedMulBlock.fpMulG,
    LeanCompCert.Verified.InstrBlock.srun_append,
    LeanCompCert.Ports.FixedMulBlock.fpMulTail_frame k _ 32 rProd rLo rHi
      rT0 rT1 rHi (by decide) (by decide) (by decide)]
  exact (mulWide_hl k st hw).2

def ceilTail : List AInstr :=
  [ .scalar (.binop rT0 .band (.reg rLo) (.lit 4294967295))
  , .scalar (.binop rT0 .ne (.reg rT0) (.lit 0))
  , .scalar (.binop rProd .add (.reg rProd) (.reg rT0)) ]

def ceilBlock : List AInstr := floorBlock ++ ceilTail

private theorem ceilTail_run (k : Nat) (st : AState) (q lo : Nat)
    (hq : st.regs rProd = q) (hlo : st.regs rLo = lo)
    (hfit : q + (if lo % 4294967296 = 0 then 0 else 1) < M) :
    (arun k st ceilTail).regs rProd =
      q + if lo % 4294967296 = 0 then 0 else 1 := by
  have hlo' : st.regs 287 = lo := hlo
  have hq' : st.regs 289 = q := hq
  have hand := Nat.and_two_pow_sub_one_eq_mod lo 32
  have hremM : lo % 4294967296 < M :=
    Nat.lt_trans (Nat.mod_lt lo (show 0 < 4294967296 by decide)) (by decide)
  simp only [ceilTail, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, RegState.set, List.foldl_cons, List.foldl_nil,
    if_pos rfl, if_true, Option.getD_some, rT0, rLo, rProd]
  rw [hlo', hq', show (4294967295 : Nat) % M = 4294967295 by decide,
    Nat.zero_mod M, hand, Nat.mod_eq_of_lt hremM]
  split <;> simp_all [Nat.mod_eq_of_lt hfit]

theorem ceilBlock_run (k : Nat) (st : AState)
    (hw : ∀ j, st.regs j < M)
    (hfit : (LeanCompCert.Verified.MulWide.hl
      (st.regs rA) (st.regs rB)).2 < 2 ^ 32)
    (hceil : mulUpper (st.regs rA) (st.regs rB) < M) :
    (arun k st ceilBlock).regs rProd = mulUpper (st.regs rA) (st.regs rB) := by
  let a := st.regs rA
  let b := st.regs rB
  let lo := (LeanCompCert.Verified.MulWide.hl a b).1
  let q := mulLower a b
  have hMB : M = LeanCompCert.Verified.MulWide.B64 := rfl
  have ha : a < LeanCompCert.Verified.MulWide.B64 := hMB ▸ hw rA
  have hb : b < LeanCompCert.Verified.MulWide.B64 := hMB ▸ hw rB
  have hspec := LeanCompCert.Verified.MulWide.hl_spec a b ha hb
  have hrem : a * b % 4294967296 = lo % 4294967296 := by
    have hdB : 4294967296 ∣ LeanCompCert.Verified.MulWide.B64 :=
      ⟨4294967296, rfl⟩
    have hd : 4294967296 ∣
        LeanCompCert.Verified.MulWide.B64 *
          (LeanCompCert.Verified.MulWide.hl a b).2 :=
      Nat.dvd_mul_right_of_dvd hdB _
    calc
      a * b % 4294967296 =
          (lo + LeanCompCert.Verified.MulWide.B64 *
            (LeanCompCert.Verified.MulWide.hl a b).2) % 4294967296 := by
              simpa only [lo] using
                congrArg (fun n : Nat => n % 4294967296) hspec.1.symm
      _ = (lo % 4294967296 +
          (LeanCompCert.Verified.MulWide.B64 *
            (LeanCompCert.Verified.MulWide.hl a b).2) % 4294967296) %
            4294967296 := Nat.add_mod _ _ _
      _ = lo % 4294967296 := by rw [Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
        Nat.mod_mod]
  have hupper : mulUpper a b = q + if lo % 4294967296 = 0 then 0 else 1 := by
    change ceilDiv (a * b) 4294967296 =
      a * b / 4294967296 + if lo % 4294967296 = 0 then 0 else 1
    rw [ceilDiv_eq_div_add_modBit (a * b) 4294967296 (by decide)]
    by_cases hr : a * b % 4294967296 = 0
    · have hrlo : lo % 4294967296 = 0 := by rwa [← hrem]
      simp [hr, hrlo]
    · have hrlo : lo % 4294967296 ≠ 0 := by rwa [← hrem]
      simp [hr, hrlo]
  rw [ceilBlock, arun_append]
  apply Eq.trans (ceilTail_run k (arun k st floorBlock) q lo ?_ ?_ ?_) hupper.symm
  · exact floorBlock_run k st hw hfit
  · exact floorBlock_low k st hw
  · rw [← hupper]
    exact hceil

theorem blocks_wf :
    floorBlock.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true ∧
    ceilBlock.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB 327) = true := by
  constructor <;> rfl

end LeanCompCert.Ports.RamareCombined100M.ExactProduct
