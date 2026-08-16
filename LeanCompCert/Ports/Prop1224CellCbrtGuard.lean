import LeanCompCert.Ports.Prop1224Cell
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Two-sided cube-root guard for Proposition 12.2.4 cells

The reciprocal envelope is sound only when the carried `t` is a lower bound
for the true scaled cube root.  This module pins and proves the new emitted
guard which rejects both an overflowing `t` and `t³ > 2^15·20000k` on every
tested cell.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def cbrtLowerGuardBody (c : CellCfg) : List AInstr :=
  [ .scalar (.binop 260 .lt (.reg rT) (.lit 2097152))
  , .scalar (.binop 261 .sub (.lit 1) (.reg 260))
  , .scalar (.binop 262 .mul (.reg rT) (.reg rT))
  , .scalar (.binop 263 .mul (.reg 262) (.reg rT))
  , .scalar (.binop 264 .gt (.reg 263) (.reg 153))
  , .scalar (.binop 265 .add (.reg 261) (.reg 264))
  , .scalar (.binop 266 .ne (.reg 265) (.lit 0))
  , .scalar (.binop 267 .ge (.reg 122) (.lit c.kLo))
  , .scalar (.binop 268 .lt (.reg 122) (.lit c.kHi))
  , .scalar (.binop 269 .mul (.reg 267) (.reg 268))
  , .scalar (.binop 270 .mul (.reg 266) (.reg 269))
  , .scalar (.binop 271 .mul (.reg 270) (.reg 161))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 271))
  , .scalar (.binop rVCbrtHi .add (.reg rVCbrtHi) (.reg 271)) ]

/-- The helper is the literal production slice after the incremental-root
budget guard: 34 prefix instructions, 24 proposal instructions, then 13
budget/counter instructions. -/
theorem cbrtLowerGuardBody_eq_slice (c : CellCfg) :
    (c.logBody.drop 79).take 14 = cbrtLowerGuardBody c := by
  rfl

def cbrtLowerFailure (t bound : Nat) : Nat :=
  if t < 2 ^ 21 ∧ t * t * t ≤ bound then 0 else 1

theorem cbrtLowerFailure_eq_zero_iff (t bound : Nat) :
    cbrtLowerFailure t bound = 0 ↔
      t < 2 ^ 21 ∧ t * t * t ≤ bound := by
  simp [cbrtLowerFailure]

/-- On a tested final round, the exact emitted slice adds precisely the
fail-closed lower-bound bit to the aggregate and its dedicated counter. -/
theorem cbrtLowerGuardBody_run (c : CellCfg) (index : Nat) (s : AState)
    (t bound cell v vh : Nat)
    (ht : s.regs rT = t) (hbound : s.regs 153 = bound)
    (hcell : s.regs 122 = cell) (hlast : s.regs 161 = 1)
    (hlo : c.kLo ≤ cell) (hhi : cell < c.kHi)
    (hkloM : c.kLo < M) (hkhiM : c.kHi < M)
    (hv : s.regs rViol = v) (hvh : s.regs rVCbrtHi = vh)
    (hvM : v + cbrtLowerFailure t bound < M)
    (hvhM : vh + cbrtLowerFailure t bound < M) :
    let out := arun index s (cbrtLowerGuardBody c)
    out.regs rViol = v + cbrtLowerFailure t bound ∧
      out.regs rVCbrtHi = vh + cbrtLowerFailure t bound := by
  have ht' : s.regs 195 = t := by simpa [rT] using ht
  have hv' : s.regs 190 = v := by simpa [rViol] using hv
  have hvh' : s.regs 254 = vh := by simpa [rVCbrtHi] using hvh
  have hlimM : (2 ^ 21 : Nat) < M := by decide
  have hlimMod : (2097152 : Nat) % M = 2097152 :=
    Nat.mod_eq_of_lt hlimM
  have hkloMod : c.kLo % M = c.kLo := Nat.mod_eq_of_lt hkloM
  have hkhiMod : c.kHi % M = c.kHi := Nat.mod_eq_of_lt hkhiM
  by_cases htlim : t < 2 ^ 21
  · have ht2 : t * t < 2 ^ 42 := by
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt htlim htlim)
        (by decide)
    have ht3 : t * t * t < M := by
      have h := Nat.mul_lt_mul_of_lt_of_lt ht2 htlim
      exact Nat.lt_trans (by simpa using h) (by decide)
    have ht3Mod : t * t * t % M = t * t * t := Nat.mod_eq_of_lt ht3
    by_cases hc : t * t * t ≤ bound
    · have hf : cbrtLowerFailure t bound = 0 := by
        simp [cbrtLowerFailure, htlim, hc]
      have hvLt : v < M := by simpa [hf] using hvM
      have hvhLt : vh < M := by simpa [hf] using hvhM
      have hbit :
          (if (1 + (M - if t < 2097152 % M then 1 else 0) +
              if bound < t * t * t then 1 else 0) % M = 0 then 0 else 1) = 0 := by
        simp [hlimMod, htlim, Nat.not_lt.mpr hc, M]
      simp [cbrtLowerGuardBody, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, AState.writeReg, rT, rViol, rVCbrtHi, ht', hbound,
        hcell, hlast, hlo, hhi, hkloM, hkhiM, hv, hvh, htlim, hc, ht2, ht3,
        hv', hvh', hf, hbit, hvLt, hvhLt,
        Nat.mod_eq_of_lt]
    · have hf : cbrtLowerFailure t bound = 1 := by
        simp [cbrtLowerFailure, htlim, hc]
      have hgt : bound < t * t * t := Nat.lt_of_not_ge hc
      have hvLt : v + 1 < M := by simpa [hf] using hvM
      have hvhLt : vh + 1 < M := by simpa [hf] using hvhM
      have hbit :
          (if (1 + (M - if t < 2097152 % M then 1 else 0) +
              if bound < t * t * t then 1 else 0) % M = 0 then 0 else 1) = 1 := by
        simp [hlimMod, htlim, hgt, M]
      have hwrapOne : (1 + (M - 1) + 1) % M = 1 := by
        decide
      simp [cbrtLowerGuardBody, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, AState.writeReg, rT, rViol, rVCbrtHi, ht', hbound,
        hcell, hlast, hlo, hhi, hkloM, hkhiM, hv, hvh, htlim, hc, hgt, ht2,
        ht3, ht3Mod, hkloMod, hkhiMod, hv', hvh', hf, hbit, hwrapOne,
        hlimMod, hvLt, hvhLt,
        Nat.mod_eq_of_lt]
  · have hf : cbrtLowerFailure t bound = 1 := by
      simp [cbrtLowerFailure, htlim]
    have hvLt : v + 1 < M := by simpa [hf] using hvM
    have hvhLt : vh + 1 < M := by simpa [hf] using hvhM
    have hoverZero : (1 + 0) % M ≠ 0 := by decide
    have hoverOne : (1 + 1) % M ≠ 0 := by decide
    by_cases hcMod : bound < t * t * t % M
    ·
      simp [cbrtLowerGuardBody, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, AState.writeReg, rT, rViol, rVCbrtHi, ht', hbound,
        hcell, hlast, hlo, hhi, hkloMod, hkhiMod, htlim, hcMod, hf, hlimMod,
        hoverZero, hoverOne, hvLt, hvhLt, hv', hvh', Nat.mod_eq_of_lt]
    ·
      simp [cbrtLowerGuardBody, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, AState.writeReg, rT, rViol, rVCbrtHi, ht', hbound,
        hcell, hlast, hlo, hhi, hkloMod, hkhiMod, htlim, hcMod, hf, hlimMod,
        hoverZero, hoverOne, hvLt, hvhLt, hv', hvh', Nat.mod_eq_of_lt]

#print axioms cbrtLowerGuardBody_eq_slice
#print axioms cbrtLowerGuardBody_run

end LeanCompCert.Ports.Prop1224Cell
