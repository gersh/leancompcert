import LeanCompCert.Ports.R2SegMarkingReset

/-! # Post-hit power decision for the `R₂*` marking loop -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

/-- The first five instructions after the literal marking-cell store decide
whether to keep the current power, bump to the next power of the same prime,
or step to the next prime-table row. -/
def markAdvanceFlagsInstrs (c : R2Cfg) : List Instr :=
  [ .binop 52 .mul (.reg 8) (.reg 27)
  , .binop 150 .mul (.reg rQ) (.reg rBp)
  , .binop 151 .le (.reg 150) (.lit c.hi)
  , .binop 152 .mul (.reg 52) (.reg 151)
  , .binop 153 .sub (.reg 52) (.reg 152) ]

def markAdvanceFlagsBody (c : R2Cfg) : List AInstr :=
  lift (markAdvanceFlagsInstrs c)

theorem markAdvanceFlagsBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 53).take (markAdvanceFlagsBody c).length =
      markAdvanceFlagsBody c := by
  rfl

def advanceActive (inMark pastWindow : Nat) : Nat :=
  inMark * pastWindow

def R2Cfg.powerFits (c : R2Cfg) (power prime : Nat) : Nat :=
  if power * prime ≤ c.hi then 1 else 0

def R2Cfg.bumpPower (c : R2Cfg)
    (inMark pastWindow power prime : Nat) : Nat :=
  advanceActive inMark pastWindow * c.powerFits power prime

def R2Cfg.stepPrime (c : R2Cfg)
    (inMark pastWindow power prime : Nat) : Nat :=
  advanceActive inMark pastWindow -
    c.bumpPower inMark pastWindow power prime

/-- Exact semantics of the power-decision slice.  The two input selectors are
bits; consequently `bumpPower` and `stepPrime` are disjoint bits whose sum is
the active exhausted-window bit.  The multiplication and `hi` hypotheses are
the literal machine-word guards used by the production program. -/
theorem markAdvanceFlagsBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (h8 : s.regs 8 ≤ 1) (h27 : s.regs 27 ≤ 1)
    (hmul : s.regs rQ * s.regs rBp < M) (hhi : c.hi < M) :
    let active := advanceActive (s.regs 8) (s.regs 27)
    let bump := c.bumpPower (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let step := c.stepPrime (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let out := arun k s (markAdvanceFlagsBody c)
    out.regs 52 = active ∧
      out.regs 150 = s.regs rQ * s.regs rBp ∧
      out.regs 151 = c.powerFits (s.regs rQ) (s.regs rBp) ∧
      out.regs 152 = bump ∧ out.regs 153 = step ∧
      out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.arr = s.arr := by
  have hmul' : s.regs 3 * s.regs 170 < M := by
    simpa [rQ, rBp] using hmul
  have hmulMod :
      (s.regs 3 * s.regs 170) % M = s.regs 3 * s.regs 170 :=
    Nat.mod_eq_of_lt hmul'
  have hhiMod : c.hi % M = c.hi := Nat.mod_eq_of_lt hhi
  have h1M : (1 : Nat) < M := by decide
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt h1M
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  simp only [markAdvanceFlagsBody, arun_lift]
  by_cases ha : s.regs 8 = 0
  · by_cases hp : s.regs 27 = 0
    · simp [markAdvanceFlagsInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, advanceActive, R2Cfg.powerFits,
        R2Cfg.bumpPower, R2Cfg.stepPrime, ha, hp, hmulMod, hhiMod,
        rQ, rBp]
    · have hp1 : s.regs 27 = 1 := by omega
      simp [markAdvanceFlagsInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, advanceActive, R2Cfg.powerFits,
        R2Cfg.bumpPower, R2Cfg.stepPrime, ha, hp1, hmulMod, hhiMod,
        rQ, rBp]
  · have ha1 : s.regs 8 = 1 := by omega
    by_cases hp : s.regs 27 = 0
    · simp [markAdvanceFlagsInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, advanceActive, R2Cfg.powerFits,
        R2Cfg.bumpPower, R2Cfg.stepPrime, ha1, hp, hmulMod, hhiMod,
        rQ, rBp]
    · have hp1 : s.regs 27 = 1 := by omega
      by_cases hf : s.regs rQ * s.regs rBp ≤ c.hi
      · have hf' : s.regs 3 * s.regs 170 ≤ c.hi := by
          simpa [rQ, rBp] using hf
        simp [markAdvanceFlagsInstrs, srun, RegState.set, sdest, sval,
          denoteOperand, denoteOp, advanceActive, R2Cfg.powerFits,
          R2Cfg.bumpPower, R2Cfg.stepPrime, ha1, hp1, hf', hmulMod,
          hhiMod, honeMod, hzero, rQ, rBp]
      · have hf' : ¬s.regs 3 * s.regs 170 ≤ c.hi := by
          simpa [rQ, rBp] using hf
        simp [markAdvanceFlagsInstrs, srun, RegState.set, sdest, sval,
          denoteOperand, denoteOp, advanceActive, R2Cfg.powerFits,
          R2Cfg.bumpPower, R2Cfg.stepPrime, ha1, hp1, hf', hmulMod,
          hhiMod, honeMod, rQ, rBp]

#print axioms markAdvanceFlagsBody_run

end LeanCompCert.Ports.R2SegSieve
