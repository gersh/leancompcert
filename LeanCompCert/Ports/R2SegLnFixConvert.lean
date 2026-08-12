import LeanCompCert.Ports.R2SegLogFactors

/-!
# Exact natural-log conversion in the `R₂*` log phase

At production scale `logFix 24 n < 63 * 2^24 < 2^30`.  Consequently its
upper 32-bit half is zero, and the emitted half-limb multiplication by the
64-bit `L2` literal has a particularly small exact proof.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.PsiSegSieve (L2hi L2lo)

def lnFixExtractInstrs : List Instr :=
  [ .binop 252 .band (.reg 251) (.lit 4294967295)
  , .binop 253 .lshr (.reg 251) (.lit 32) ]

def lnFixMultiplyInstrs : List Instr :=
  [ .binop 254 .mul (.reg 252) (.lit L2lo)
  , .binop 255 .mul (.reg 252) (.lit L2hi)
  , .binop 256 .mul (.reg 253) (.lit L2lo)
  , .binop 257 .mul (.reg 253) (.lit L2hi) ]

def lnFixCarryInstrs : List Instr :=
  [ .binop 258 .lshr (.reg 254) (.lit 32)
  , .binop 259 .add (.reg 255) (.reg 256)
  , .binop 260 .add (.reg 259) (.reg 258)
  , .binop 261 .lshr (.reg 260) (.lit 32)
  , .binop 262 .add (.reg 257) (.reg 261) ]

def lnFixConvertInstrs : List Instr :=
  lnFixExtractInstrs ++ lnFixMultiplyInstrs ++ lnFixCarryInstrs

def lnFixConvertBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift lnFixConvertInstrs

theorem lnFixConvertBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 63).take 11 = lnFixConvertBody := by
  rfl

private theorem high_word_decomposition (a b B : Nat) (hB : 0 < B) :
    (a * (b / B) + a * (b % B) / B) / B = a * b / (B * B) := by
  have hb := Nat.div_add_mod b B
  have hab : a * b = B * (a * (b / B)) + a * (b % B) := by
    calc
      a * b = a * (B * (b / B) + b % B) := congrArg (fun x => a * x) hb.symm
      _ = B * (a * (b / B)) + a * (b % B) := by
        simp only [Nat.mul_add]
        rw [Nat.mul_left_comm a B]
  rw [← Nat.div_div_eq_div_mul]
  rw [hab, Nat.mul_add_div hB]

private theorem lnFixExtractInstrs_run (k : Nat) (s : RegState) (a : Nat)
    (ha32 : a < 4294967296) (h251 : s 251 = a) :
    let out := srun k s lnFixExtractInstrs
    out 252 = a ∧ out 253 = 0 := by
  have haM : a < M := Nat.lt_trans ha32 (by decide)
  have hand : a &&& 4294967295 = a := by
    have h := Nat.and_two_pow_sub_one_eq_mod a 32
    change a &&& (2 ^ 32 - 1) = a
    rw [h, Nat.mod_eq_of_lt ha32]
  have hshr : a >>> 32 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt ha32
  have hmask : (4294967295 : Nat) % M = 4294967295 := by decide
  have h32 : (32 : Nat) % M = 32 := by decide
  simp [lnFixExtractInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h251, hmask, h32, hand, hshr,
    Nat.mod_eq_of_lt haM]

private theorem lnFixMultiplyInstrs_run (k : Nat) (s : RegState) (a : Nat)
    (h252 : s 252 = a) (h253 : s 253 = 0)
    (hp0 : a * L2lo < M) (hp1 : a * L2hi < M) :
    let out := srun k s lnFixMultiplyInstrs
    out 254 = a * L2lo ∧ out 255 = a * L2hi ∧
      out 256 = 0 ∧ out 257 = 0 := by
  have hloM : L2lo % M = L2lo :=
    Nat.mod_eq_of_lt (Nat.lt_trans (show L2lo < 4294967296 by decide) (by decide))
  have hhiM : L2hi % M = L2hi :=
    Nat.mod_eq_of_lt (Nat.lt_trans (show L2hi < 4294967296 by decide) (by decide))
  simp [lnFixMultiplyInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h252, h253, hloM, hhiM,
    Nat.mod_eq_of_lt hp0, Nat.mod_eq_of_lt hp1]

private theorem lnFixCarryInstrs_run (k : Nat) (s : RegState) (p0 p1 : Nat)
    (h254 : s 254 = p0) (h255 : s 255 = p1)
    (h256 : s 256 = 0) (h257 : s 257 = 0)
    (hp1 : p1 < M)
    (hsum : p1 + p0 / 4294967296 < M) :
    (srun k s lnFixCarryInstrs) 262 =
      (p1 + p0 / 4294967296) / 4294967296 := by
  have hsumDiv : (p1 + p0 / 4294967296) / 4294967296 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsum
  have h32 : (32 : Nat) % M = 32 := by decide
  simp [lnFixCarryInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h254, h255, h256, h257,
    h32, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hp1,
    Nat.mod_eq_of_lt hsum,
    Nat.mod_eq_of_lt hsumDiv]

theorem lnFixConvertInstrs_run (k : Nat) (s : RegState) (a : Nat)
    (ha : a < 2 ^ 30) (h251 : s 251 = a) :
    (srun k s lnFixConvertInstrs) 262 =
      a * LeanCompCert.Ports.PsiSegSieve.L2 / 2 ^ 64 := by
  have ha32 : a < 4294967296 := by omega
  have hlo : L2lo < 4294967296 := by decide
  have hhi : L2hi < 4294967296 := by decide
  have hp0 : a * L2lo < M := by
    simpa [M] using
      LeanCompCert.Verified.MulWide.mul_lt_mul_of_lt_of_lt ha32 hlo
  have hp1 : a * L2hi < M := by
    simpa [M] using
      LeanCompCert.Verified.MulWide.mul_lt_mul_of_lt_of_lt ha32 hhi
  have hp1small : a * L2hi < 2 ^ 62 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt ha (show L2hi < 2 ^ 32 by decide)
    rw [show (2 : Nat) ^ 30 * 2 ^ 32 = 2 ^ 62 by decide] at h
    exact h
  have hp0div : a * L2lo / 4294967296 < 4294967296 :=
    (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [M] using hp0)
  have hsum : a * L2hi + a * L2lo / 4294967296 < M := by
    simp only [M] at hp1small hp0div ⊢
    omega
  have hhiword :
      (a * L2hi + a * L2lo / 4294967296) / 4294967296 =
        a * LeanCompCert.Ports.PsiSegSieve.L2 / 2 ^ 64 := by
    have h := high_word_decomposition a
      LeanCompCert.Ports.PsiSegSieve.L2 4294967296 (by decide)
    simpa [L2hi, L2lo] using h
  let extracted := srun k s lnFixExtractInstrs
  let multiplied := srun k extracted lnFixMultiplyInstrs
  have hextract := lnFixExtractInstrs_run k s a ha32 h251
  have hmultiply := lnFixMultiplyInstrs_run k extracted a
    hextract.1 hextract.2 hp0 hp1
  have hcarry := lnFixCarryInstrs_run k multiplied (a * L2lo) (a * L2hi)
    hmultiply.1 hmultiply.2.1 hmultiply.2.2.1 hmultiply.2.2.2 hp1 hsum
  rw [lnFixConvertInstrs, srun_append, srun_append]
  exact hcarry.trans hhiword

/-- Production specialization: the output is definitionally `lnFix S n`. -/
theorem lnFixConvertInstrs_logFix_run (k : Nat) (s : RegState) (S n : Nat)
    (ha : LeanCompCert.Verified.LogFixed.logFix S n < 2 ^ 30)
    (h251 : s 251 = LeanCompCert.Verified.LogFixed.logFix S n) :
    (srun k s lnFixConvertInstrs) 262 =
      LeanCompCert.Ports.PsiSegSieve.lnFix S n := by
  simpa [LeanCompCert.Ports.PsiSegSieve.lnFix] using
    lnFixConvertInstrs_run k s
      (LeanCompCert.Verified.LogFixed.logFix S n) ha h251

/-- The same conversion theorem at the array-machine boundary used by the
production `R₂*` loop; the scalar slice leaves the sieve array unchanged. -/
theorem lnFixConvertBody_logFix_run (k : Nat) (s : AState) (S n : Nat)
    (ha : LeanCompCert.Verified.LogFixed.logFix S n < 2 ^ 30)
    (h251 : s.regs 251 = LeanCompCert.Verified.LogFixed.logFix S n) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s lnFixConvertBody
    out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix S n ∧
      out.arr = s.arr := by
  rw [lnFixConvertBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨lnFixConvertInstrs_logFix_run k s.regs S n ha h251, rfl⟩

#print axioms lnFixConvertBody_eq_slice
#print axioms lnFixConvertInstrs_run
#print axioms lnFixConvertInstrs_logFix_run
#print axioms lnFixConvertBody_logFix_run

end LeanCompCert.Ports.R2SegSieve
