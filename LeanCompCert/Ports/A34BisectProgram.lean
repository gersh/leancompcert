import LeanCompCert.Ports.A34Bisect
import LeanCompCert.Ports.A36BisectProgram
import LeanCompCert.Verified.Decide

/-!
# Rolled LeanCompCert verifier for Appendix A.34

One loop iteration checks one fixed-point row from `A34Bisect`.  The program
reuses the directed-operation builders from `A36BisectProgram`; only the
expression graph and the `[1/10,36]` grid are new.  Its emitted C has constant
size at every depth.
-/

namespace LeanCompCert.Ports.A34BisectProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.A34Bisect
open LeanCompCert.Ports.A36BisectProgram

set_option maxRecDepth 4000000

def rFail : Nat := 0
def rT : Nat := 49
def rG : Nat := 50
def rU : Nat := 51
def rOne : Nat := 52
def rTwo : Nat := 53
def rCLo : Nat := 54
def rCHi : Nat := 55
def rHalfLo : Nat := 56
def rHalfHi : Nat := 57
def rDen : Nat := 58
def rDenM : Nat := 59
def regCount : Nat := 60

def SC : Nat := 16777216

/-- Outward endpoints of grid cell `idx` for the exact grid
`(2^d + 359*i)/(10*2^d)`. -/
def cellInstrsAt (d : Nat) : List Instr :=
  let den := 10 * 2 ^ d
  let base := 2 ^ d
  [ .binop rT .mul .idx (.lit 359)
  , .binop rT .add (.reg rT) (.lit base)
  , .binop rT .shl (.reg rT) (.lit 24)
  , .binop 1 .udiv (.reg rT) (.reg rDen)
  , .binop rT .mul .idx (.lit 359)
  , .binop rT .add (.reg rT) (.lit (base + 359))
  , .binop rT .shl (.reg rT) (.lit 24)
  , .binop rT .add (.reg rT) (.reg rDenM)
  , .binop 2 .udiv (.reg rT) (.reg rDen) ]

/-- OR the failure flag with `a > b`. -/
def failIfGt (a b : Nat) : List Instr :=
  [ .binop rT .gt (.reg a) (.reg b)
  , .binop rFail .bor (.reg rFail) (.reg rT) ]

/-- The depth-independent arithmetic and checking part of one row. -/
def bodyTail : List Instr :=
  iMul 3 4 1 2 1 2 rT ++                              -- ρ²
  iAdd 5 6 rOne rOne 3 4 ++                           -- 1+ρ²
  iSqrtGuess 7 8 5 6 rT rG rU ++
  sqrtCheckInstrs 5 6 7 8 rT rG ++                    -- j
  iAdd 9 10 rOne rOne 7 8 ++                          -- 1+j
  iDiv 11 12 9 10 rTwo rTwo rT rG ++                 -- (1+j)/2
  iSqrtGuess 13 14 11 12 rT rG rU ++
  sqrtCheckInstrs 11 12 13 14 rT rG ++                -- υ
  iAdd 15 16 13 14 7 8 ++                             -- υ+j
  iMul 17 18 rTwo rTwo 13 14 rT ++                    -- 2υ
  iMul 19 20 17 18 15 16 rT ++                       -- denominator
  [ .binop rT .eq (.reg 19) (.lit 0)
  , .binop rFail .bor (.reg rFail) (.reg rT) ] ++
  iDiv 21 22 1 2 19 20 rT rG ++                      -- x
  iMul 23 24 21 22 21 22 rT ++                       -- x²
  iAdd 25 26 rOne rOne 23 24 ++                       -- 1+x²
  iSqrtGuess 27 28 25 26 rT rG rU ++
  sqrtCheckInstrs 25 26 27 28 rT rG ++                -- sqrt(1+x²)
  failIfGt 22 27 ++
  iSub 29 30 27 28 21 22 rT ++                       -- Υ
  iMul 31 32 rTwo rTwo 13 14 rT ++                    -- 2υ
  iAdd 33 34 9 10 31 32 ++                           -- 1+j+2υ
  iSqrtGuess 35 36 33 34 rT rG rU ++
  sqrtCheckInstrs 33 34 35 36 rT rG ++                -- W
  iMul 37 38 13 14 13 14 rT ++                       -- υ²
  failIfGt 14 37 ++
  iSub 39 40 37 38 13 14 rT ++                       -- υ²-υ
  iMul 41 42 rCLo rCHi 35 36 rT ++                   -- cW
  failIfGt rHalfHi 41 ++
  iSub 43 44 41 42 rHalfLo rHalfHi rT ++             -- cW-1/2
  iMul 45 46 1 2 29 30 rT ++                         -- ρΥ
  iMul 47 48 45 46 43 44 rT ++                       -- ρΥ(cW-1/2)
  failIfGt 40 47

/-- One complete fail-closed A.34 interval row. -/
def bodyAt (d : Nat) : List Instr := cellInstrsAt d ++ bodyTail

def initInstrs (d : Nat) : List Instr :=
  let den := 10 * 2 ^ d
  [ .mov rOne (.lit SC)
  , .mov rTwo (.lit (2 * SC))
  , .mov rCLo (.lit (qC 29888 100000).lo)
  , .mov rCHi (.lit (qC 29888 100000).hi)
  , .mov rHalfLo (.lit (qC 1 2).lo)
  , .mov rHalfHi (.lit (qC 1 2).hi)
  , .mov rDen (.lit den)
  , .mov rDenM (.lit (den - 1)) ]

def programAt (d : Nat) : Program :=
  { regCount := regCount
    loopCount := 2 ^ d
    init := initInstrs d
    body := bodyAt d
    epilogue := []
    output := rFail }

def program : Program := programAt depth

theorem cell_wf (d : Nat) :
    ∀ instr ∈ cellInstrsAt d, instr.WF regCount := by
  intro instr h
  simp only [cellInstrsAt, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem tail_wf : ∀ instr ∈ bodyTail, instr.WF regCount := by decide

theorem body_wf (d : Nat) : ∀ instr ∈ bodyAt d, instr.WF regCount := by
  intro instr h
  rw [bodyAt] at h
  rcases List.mem_append.mp h with h | h
  · exact cell_wf d instr h
  · exact tail_wf instr h

theorem init_wf (d : Nat) : ∀ instr ∈ initInstrs d, instr.WF regCount := by
  intro instr h
  simp only [initInstrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem programAt_wf (d : Nat) : (programAt d).WF :=
  ⟨show rFail < regCount by decide, init_wf d, body_wf d,
    by intro instr h; cases h⟩

theorem program_wf : program.WF := programAt_wf depth

def computation : LeanCompCert.Verified.Computation :=
  program.toComputation "A34Bisect20" program_wf

/-- Small rejecting control: the depth-3 grid is too coarse. -/
theorem reject_depth3 : (programAt 3).denote = some 1 := by decide +kernel

end LeanCompCert.Ports.A34BisectProgram
