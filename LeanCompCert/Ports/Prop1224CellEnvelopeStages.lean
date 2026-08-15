import LeanCompCert.Ports.Prop1224Cell
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Scalar stages of the Proposition 12.2.4 cell envelope

The emitted five-instruction block is split into small scalar stages.  This is
only a proof boundary: `envelopeScalar_eq_stages` proves that concatenating
the stages recovers the literal emitted block.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.Prop1224Margin

def envelopeScalar (c : CellCfg) : List Instr :=
  [ .binop 213 .shl (.lit c.afHi) (.lit 5)
  , .binop 214 .add (.reg 213) (.reg rT)
  , .binop 215 .sub (.reg 214) (.lit 1)
  , .binop 216 .udiv (.reg 215) (.reg rT)
  , .binop 217 .shl (.reg 216) (.lit (C - E)) ]

theorem envelopeBlock_eq_lift (c : CellCfg) :
    c.envelopeBlock = lift (envelopeScalar c) := by rfl

def envelopeNumeratorScalar (c : CellCfg) : List Instr :=
  (envelopeScalar c).take 1

def envelopeCeilInputScalar (c : CellCfg) : List Instr :=
  ((envelopeScalar c).drop 1).take 2

def envelopeDivideScalar (c : CellCfg) : List Instr :=
  ((envelopeScalar c).drop 3).take 1

def envelopeRescaleScalar (c : CellCfg) : List Instr :=
  (envelopeScalar c).drop 4

theorem envelopeScalar_eq_stages (c : CellCfg) :
    envelopeScalar c = envelopeNumeratorScalar c ++
      envelopeCeilInputScalar c ++ envelopeDivideScalar c ++
      envelopeRescaleScalar c := by rfl

end LeanCompCert.Ports.Prop1224Cell
