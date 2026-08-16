import LeanCompCert.Ports.Prop1224Cell

/-!
# Shared compiled logarithm and cube-root table for Proposition 12.2.4

Both `log r` and `(20000r)^(1/3)` depend only on `r`, not on the runtime row
`q`.  This program computes their conservative integer representatives once:

* `lnLo[r] = floor(2^E log r)` through the proved 24-round fixed logarithm;
* `cbrtLo[r] = floor(2^5 (20000r)^(1/3))` by an 18-bit high-to-low search.

The cube is exact because every candidate is below `2^18`, hence its cube is
below `2^54`.  Both endpoint inequalities are checked by the emitted code.
The logarithm's one-step exponent cursor is likewise checked on every row.
-/

namespace LeanCompCert.Ports.Prop1224LogCbrtTable

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Prop1224Margin (E S)
open LeanCompCert.Ports.ArraySegSieve
  (ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Cell (L2lo32 lnShift)

structure Cfg where
  rows : Nat
  lnBase : Nat
  cbrtBase : Nat
  resultCell : Nat
  arrayLen : Nat
  deriving Repr

def r : Nat := 0
def rEx : Nat := 1
def rTh : Nat := 2
def rXm : Nat := 3
def rAa : Nat := 4
def rT : Nat := 5
def rViol : Nat := 6
def regCount : Nat := 96

def init : List AInstr :=
  [ .scalar (.mov r (.lit 1))
  , .scalar (.mov rTh (.lit 2)) ]

/-- One fixed-point logarithm squaring round, verbatim from
`Prop1224Cell.logBody`. -/
def logRound : List AInstr :=
  [ .scalar (.binop 20 .lshr (.reg rXm) (.lit 32))
  , .scalar (.binop 21 .band (.reg rXm) (.lit 4294967295))
  , .scalar (.binop 22 .mul (.reg 20) (.reg 20))
  , .scalar (.binop 23 .mul (.reg 20) (.reg 21))
  , .scalar (.binop 24 .mul (.reg 21) (.reg 21))
  , .scalar (.binop 25 .lshr (.reg 23) (.lit 29))
  , .scalar (.binop 26 .band (.reg 23) (.lit 536870911))
  , .scalar (.binop 27 .lshr (.reg 24) (.lit 62))
  , .scalar (.binop 28 .band (.reg 24) (.lit 4611686018427387903))
  , .scalar (.binop 29 .shl (.reg 26) (.lit 33))
  , .scalar (.binop 30 .add (.reg 29) (.reg 28))
  , .scalar (.binop 31 .ge (.reg 30) (.lit 4611686018427387904))
  , .scalar (.binop 32 .shl (.reg 22) (.lit 2))
  , .scalar (.binop 33 .add (.reg 32) (.reg 25))
  , .scalar (.binop 34 .add (.reg 33) (.reg 27))
  , .scalar (.binop 35 .add (.reg 34) (.reg 31))
  , .scalar (.binop 36 .ge (.reg 35) (.lit 9223372036854775808))
  , .scalar (.binop rXm .lshr (.reg 35) (.reg 36))
  , .scalar (.binop 37 .shl (.reg rAa) (.lit 1))
  , .scalar (.binop rAa .add (.reg 37) (.reg 36)) ]

def logRounds : List AInstr := (List.replicate S logRound).flatten

/-- High-to-low integer cube-root bits.  `cbrtBits 18` tries bits 17 ... 0. -/
def cbrtBits : Nat → List AInstr
  | 0 => []
  | n + 1 =>
      [ .scalar (.binop 50 .add (.reg rT) (.lit (2 ^ n)))
      , .scalar (.binop 51 .mul (.reg 50) (.reg 50))
      , .scalar (.binop 52 .mul (.reg 51) (.reg 50))
      , .scalar (.binop 53 .le (.reg 52) (.reg 49))
      , .scalar (.binop 54 .mul (.reg 53) (.lit (2 ^ n)))
      , .scalar (.binop rT .add (.reg rT) (.reg 54)) ] ++ cbrtBits n

def body (c : Cfg) : List AInstr :=
  [ -- incremental floor(log2 r), with a completion guard
    .scalar (.binop 10 .ge (.reg r) (.reg rTh))
  , .scalar (.binop rEx .add (.reg rEx) (.reg 10))
  , .scalar (.binop 11 .mul (.reg 10) (.reg rTh))
  , .scalar (.binop rTh .add (.reg rTh) (.reg 11))
  , .scalar (.binop 12 .ge (.reg r) (.reg rTh))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 12))
    -- normalized mantissa and fixed log accumulator
  , .scalar (.binop 13 .sub (.lit 62) (.reg rEx))
  , .scalar (.binop 14 .band (.reg 13) (.lit 63))
  , .scalar (.binop rXm .shl (.reg r) (.reg 14))
  , .scalar (.mov rAa (.lit 0)) ] ++
  logRounds ++
  [ .scalar (.binop 40 .shl (.reg rEx) (.lit S))
  , .scalar (.binop 41 .add (.reg 40) (.reg rAa))
  , .scalar (.binop 42 .mul (.reg 41) (.lit L2lo32))
  , .scalar (.binop 43 .lshr (.reg 42) (.lit lnShift))
    -- exact 18-bit lower cube root of 2^15 * 20000r
  , .scalar (.mov rT (.lit 0))
  , .scalar (.binop 48 .mul (.lit 20000) (.reg r))
  , .scalar (.binop 49 .shl (.reg 48) (.lit 15)) ] ++
  cbrtBits 18 ++
  [ -- both defining cube-root inequalities, plus the explicit word guard
    .scalar (.binop 55 .lt (.reg rT) (.lit 262144))
  , .scalar (.binop 56 .sub (.lit 1) (.reg 55))
  , .scalar (.binop 57 .mul (.reg rT) (.reg rT))
  , .scalar (.binop 58 .mul (.reg 57) (.reg rT))
  , .scalar (.binop 59 .gt (.reg 58) (.reg 49))
  , .scalar (.binop 60 .add (.reg 56) (.reg 59))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 60))
  , .scalar (.binop 61 .add (.reg rT) (.lit 1))
  , .scalar (.binop 62 .mul (.reg 61) (.reg 61))
  , .scalar (.binop 63 .mul (.reg 62) (.reg 61))
  , .scalar (.binop 64 .le (.reg 63) (.reg 49))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 64))
    -- retained table values
  , .scalar (.binop 70 .add (.reg r) (.lit c.lnBase))
  , .store 70 43
  , .scalar (.binop 71 .add (.reg r) (.lit c.cbrtBase))
  , .store 71 rT
  , .scalar (.binop r .add (.reg r) (.lit 1)) ]

def epilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov 80 (.lit c.resultCell)), .store 80 rViol ]

def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.rows
  init := init
  body := body c
  epilogue := epilogue c
  output := rViol
}

theorem init_all : init.all (ainstrWFB regCount) = true := by rfl

theorem logRound_all : logRound.all (ainstrWFB regCount) = true := by rfl

theorem logRounds_all : logRounds.all (ainstrWFB regCount) = true := by
  simp only [logRounds, List.all_flatten, List.all_replicate]
  exact logRound_all

theorem cbrtBits_all (n : Nat) :
    (cbrtBits n).all (ainstrWFB regCount) = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact all_append (by rfl) ih

set_option maxRecDepth 100000 in
theorem body_all (c : Cfg) : (body c).all (ainstrWFB regCount) = true := by
  obtain ⟨rows, lnBase, cbrtBase, resultCell, arrayLen⟩ := c
  rfl

theorem epilogue_all (c : Cfg) :
    (epilogue c).all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : Cfg) : (program c).WF :=
  ⟨show rViol < regCount by decide,
   forall_wf_of_all init_all,
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (program c).arrayLen base)
    (n : Nat) (hDenote : (program c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c).initialMCC base) (program c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c) base hBase n hDenote

#print axioms program_compiled

end LeanCompCert.Ports.Prop1224LogCbrtTable
