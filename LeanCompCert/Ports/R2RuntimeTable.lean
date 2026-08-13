import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Verified.ArrayPipeline

/-!
# Compiled construction of the R2 production mark table

The former production artifact carried 13,415 packed prime/logarithm literals.
Constructing those literals in Lean took minutes and made CompCert consume
about 9.3 GiB while compiling the initializer.  This module moves that work to
two small compiled programs over the same array later consumed by `r2Program`:

1. `r2RootMarkProgram` marks composites through `floor (sqrt hi)` by a finite
   `(n,d)` grid;
2. `r2RootPackProgram` scans that finite interval, computes `lnFix 24 n` with
   the verified fixed-log instruction round, and appends packed prime entries.

The main sweep then uses `r2RuntimeProgram`, whose initializer seeds registers
only.  No prime/log table is evaluated or emitted by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (L2hi L2lo seedRegs)

def runtimeRoot : Nat := 144914
def runtimeDivCap : Nat := 380
def runtimePrimeCount : Nat := 13415
def runtimeScale : Nat := 24

/-- Production configuration without an evaluated prime list.  The dummy tail
exists only to carry the verified table length through the current `R2Cfg`
interface; `r2RuntimeProgram` never emits it. -/
def runtimeProductionCfg : R2Cfg :=
  { lo := 145000
    segLen := 1000000
    segCount := 21000
    sc := runtimeScale
    markSteps := 3558013
    logSteps := 5973595
    streamCap := 391534
    table := []
    tableLenOverride := some runtimePrimeCount
    firstEntryOverride := some (packEntry 2
      (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale 2) 1) }

/-! ## Stage one: composite marks -/

def rootMarkSink (c : R2Cfg) : Nat := c.segLen

def rootMarkDecode : List AInstr :=
  let width := 379
  [ .scalar (.binop 10 .udiv .idx (.lit width))
  , .scalar (.binop 11 .add (.reg 10) (.lit 2))       -- n
  , .scalar (.binop 12 .urem .idx (.lit width))
  , .scalar (.binop 13 .add (.reg 12) (.lit 2)) ]     -- d

def rootMarkWitness : List AInstr :=
  [ .scalar (.binop 14 .mul (.reg 13) (.reg 13))
  , .scalar (.binop 15 .le (.reg 14) (.reg 11))
  , .scalar (.binop 16 .urem (.reg 11) (.reg 13))
  , .scalar (.binop 17 .eq (.reg 16) (.lit 0)) ]

def rootMarkTarget (c : R2Cfg) : List AInstr :=
  [ .scalar (.binop 18 .mul (.reg 15) (.reg 17))      -- composite witness
  , .scalar (.binop 19 .mul (.reg 18) (.reg 11))
  , .scalar (.binop 20 .sub (.lit 1) (.reg 18))
  , .scalar (.binop 21 .mul (.reg 20) (.lit (rootMarkSink c)))
  , .scalar (.binop 22 .add (.reg 19) (.reg 21)) ]

def rootMarkBody (c : R2Cfg) : List AInstr :=
  rootMarkDecode ++ rootMarkWitness ++ rootMarkTarget c ++ [.store 22 18]

def r2RootMarkProgram (c : R2Cfg := runtimeProductionCfg) : AProgram :=
  { regCount := regCount
    arrayLen := c.arrayLen
    loopCount := (runtimeRoot - 1) * (runtimeDivCap - 1)
    init := []
    body := rootMarkBody c
    epilogue := [.scalar (.mov 0 (.lit 0))]
    output := 0 }

theorem rootMarkBody_all (c : R2Cfg) :
    (rootMarkBody c).all (ainstrWFB regCount) = true := by rfl

theorem r2RootMarkProgram_wf (c : R2Cfg) : (r2RootMarkProgram c).WF := by
  unfold r2RootMarkProgram
  refine ⟨show 0 < regCount by decide, ?_, forall_wf_of_all (rootMarkBody_all c),
    forall_wf_of_all (by rfl)⟩
  intro a h
  cases h

/-! ## Stage two: fixed-log packing -/

def rpEx : Nat := 2
def rpTh : Nat := 3
def rpWrite : Nat := 4
def rpXm : Nat := 5
def rpAa : Nat := 6

/-- One scan/log round.  `idx / S + 2` is the candidate and `idx % S` its
fixed-log round.  Every candidate gets exactly `S` rounds; only an unmarked
candidate is appended. -/
def rootPackBody (c : R2Cfg) : List AInstr :=
  let S := runtimeScale
  [ .scalar (.binop 10 .udiv .idx (.lit S))
  , .scalar (.binop 11 .add (.reg 10) (.lit 2))       -- n
  , .scalar (.binop 12 .urem .idx (.lit S))           -- round
  , .scalar (.binop 13 .eq (.reg 12) (.lit 0))        -- start
  , .scalar (.binop 14 .add (.reg 12) (.lit 1))
  , .scalar (.binop 15 .eq (.reg 14) (.lit S))        -- finish
  , .load 16 11
  , .scalar (.binop 17 .eq (.reg 16) (.lit 0))        -- prime
    -- incremental floor(log2 n), updated only on the first round
  , .scalar (.binop 18 .ge (.reg 11) (.reg rpTh))
  , .scalar (.binop 19 .mul (.reg 18) (.reg 13))
  , .scalar (.binop rpEx .add (.reg rpEx) (.reg 19))
  , .scalar (.binop 20 .mul (.reg 19) (.reg rpTh))
  , .scalar (.binop rpTh .add (.reg rpTh) (.reg 20))
    -- initialise the normalised mantissa and fractional accumulator
  , .scalar (.binop 21 .sub (.lit 62) (.reg rpEx))
  , .scalar (.binop 22 .band (.reg 21) (.lit 63))
  , .scalar (.binop 23 .shl (.reg 11) (.reg 22))
  , .scalar (.binop 24 .sub (.lit 1) (.reg 13))
  , .scalar (.binop 25 .mul (.reg 13) (.reg 23))
  , .scalar (.binop 26 .mul (.reg 24) (.reg rpXm))
  , .scalar (.binop rpXm .add (.reg 25) (.reg 26))
  , .scalar (.binop rpAa .mul (.reg rpAa) (.reg 24))
    -- Ports.LogFixPort.logRoundBody, with local register names
  , .scalar (.binop 27 .lshr (.reg rpXm) (.lit 32))
  , .scalar (.binop 28 .band (.reg rpXm) (.lit 4294967295))
  , .scalar (.binop 29 .mul (.reg 27) (.reg 27))
  , .scalar (.binop 30 .mul (.reg 27) (.reg 28))
  , .scalar (.binop 31 .mul (.reg 28) (.reg 28))
  , .scalar (.binop 32 .lshr (.reg 30) (.lit 29))
  , .scalar (.binop 33 .band (.reg 30) (.lit 536870911))
  , .scalar (.binop 34 .lshr (.reg 31) (.lit 62))
  , .scalar (.binop 35 .band (.reg 31) (.lit 4611686018427387903))
  , .scalar (.binop 36 .shl (.reg 33) (.lit 33))
  , .scalar (.binop 37 .add (.reg 36) (.reg 35))
  , .scalar (.binop 38 .ge (.reg 37) (.lit 4611686018427387904))
  , .scalar (.binop 39 .shl (.reg 29) (.lit 2))
  , .scalar (.binop 40 .add (.reg 39) (.reg 32))
  , .scalar (.binop 41 .add (.reg 40) (.reg 34))
  , .scalar (.binop 42 .add (.reg 41) (.reg 38))
  , .scalar (.binop 43 .ge (.reg 42) (.lit 9223372036854775808))
  , .scalar (.binop rpXm .lshr (.reg 42) (.reg 43))
  , .scalar (.binop 44 .shl (.reg rpAa) (.lit 1))
  , .scalar (.binop rpAa .add (.reg 44) (.reg 43))
    -- lnFix S n: high word of logFix times the fixed ln(2) constant
  , .scalar (.binop 45 .shl (.reg rpEx) (.lit S))
  , .scalar (.binop 46 .add (.reg 45) (.reg rpAa))
  , .scalar (.binop 47 .band (.reg 46) (.lit 4294967295))
  , .scalar (.binop 48 .lshr (.reg 46) (.lit 32))
  , .scalar (.binop 49 .mul (.reg 47) (.lit L2lo))
  , .scalar (.binop 50 .mul (.reg 47) (.lit L2hi))
  , .scalar (.binop 51 .mul (.reg 48) (.lit L2lo))
  , .scalar (.binop 52 .mul (.reg 48) (.lit L2hi))
  , .scalar (.binop 53 .lshr (.reg 49) (.lit 32))
  , .scalar (.binop 54 .add (.reg 50) (.reg 51))
  , .scalar (.binop 55 .add (.reg 54) (.reg 53))
  , .scalar (.binop 56 .lshr (.reg 55) (.lit 32))
  , .scalar (.binop 57 .add (.reg 52) (.reg 56))        -- lnFix n
    -- append packed `(n, lnFix n, first=1)` on the final round of a prime
  , .scalar (.binop 58 .mul (.reg 15) (.reg 17))
  , .scalar (.binop 59 .add (.reg rpWrite) (.lit c.tableBase))
  , .scalar (.binop 60 .mul (.reg 58) (.reg 59))
  , .scalar (.binop 61 .sub (.lit 1) (.reg 58))
  , .scalar (.binop 62 .mul (.reg 61) (.lit c.streamSink))
  , .scalar (.binop 63 .add (.reg 60) (.reg 62))
  , .scalar (.binop 64 .shl (.reg 57) (.lit valBits))
  , .scalar (.binop 65 .add (.reg 11) (.reg 64))
  , .scalar (.binop 66 .add (.reg 65) (.lit (1 <<< 63)))
  , .store 63 66
  , .scalar (.binop rpWrite .add (.reg rpWrite) (.reg 58))
    -- clear the composite plane after the candidate's final round
  , .scalar (.binop 67 .mul (.reg 15) (.reg 11))
  , .scalar (.binop 68 .sub (.lit 1) (.reg 15))
  , .scalar (.binop 69 .mul (.reg 68) (.lit c.streamSink))
  , .scalar (.binop 70 .add (.reg 67) (.reg 69))
  , .store 70 0 ]

def rootPackInit : List AInstr :=
  seedRegs [(rpEx, 1), (rpTh, 4), (rpWrite, 0)]

def rootPackEpilogue (c : R2Cfg) : List AInstr :=
  [ .scalar (.binop 10 .add (.reg rpWrite) (.lit c.tableBase))
  , .scalar (.mov 11 (.lit (packEntry 1 0 0)))
  , .store 10 11 ]

def r2RootPackProgram (c : R2Cfg := runtimeProductionCfg) : AProgram :=
  { regCount := regCount
    arrayLen := c.arrayLen
    loopCount := (runtimeRoot - 1) * runtimeScale
    init := rootPackInit
    body := rootPackBody c
    epilogue := rootPackEpilogue c
    output := rpWrite }

theorem rootPackBody_all (c : R2Cfg) :
    (rootPackBody c).all (ainstrWFB regCount) = true := by rfl

theorem r2RootPackProgram_wf (c : R2Cfg) : (r2RootPackProgram c).WF :=
  ⟨show rpWrite < regCount by decide,
   forall_wf_of_all (by rfl), forall_wf_of_all (rootPackBody_all c),
   forall_wf_of_all (by rfl)⟩

/-! ## Stage three: main sweep with the resident table -/

def r2RuntimeProgram (c : R2Cfg) (s : R2Seed) : AProgram :=
  { regCount := regCount
    arrayLen := c.arrayLen
    loopCount := c.period * c.segCount
    init := seedRegs (c.seedList s)
    body := c.body
    epilogue := c.epilogue
    output := outputReg }

theorem r2RuntimeProgram_wf (c : R2Cfg) (s : R2Seed) :
    (r2RuntimeProgram c s).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (seedRegs_all _ (seedList_ok c s)),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem r2RootMarkProgram_compiled (c : R2Cfg) (base : Int)
    (hBase : BaseOk (r2RootMarkProgram c).arrayLen base)
    (n : Nat) (hDenote : (r2RootMarkProgram c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((r2RootMarkProgram c).initialMCC base)
          (r2RootMarkProgram c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(r2RootMarkProgram c).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (r2RootMarkProgram_wf c) base hBase n hDenote

theorem r2RootPackProgram_compiled (c : R2Cfg) (base : Int)
    (hBase : BaseOk (r2RootPackProgram c).arrayLen base)
    (n : Nat) (hDenote : (r2RootPackProgram c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((r2RootPackProgram c).initialMCC base)
          (r2RootPackProgram c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(r2RootPackProgram c).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (r2RootPackProgram_wf c) base hBase n hDenote

theorem r2RuntimeProgram_compiled (c : R2Cfg) (s : R2Seed) (base : Int)
    (hBase : BaseOk (r2RuntimeProgram c s).arrayLen base)
    (n : Nat) (hDenote : (r2RuntimeProgram c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((r2RuntimeProgram c s).initialMCC base)
          (r2RuntimeProgram c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(r2RuntimeProgram c s).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (r2RuntimeProgram_wf c s) base hBase n hDenote

/-- The actual three-function runtime path: composite marking, fixed-log table
packing, then the sparse R2 sweep, all on one caller-owned array.  The source
run hypotheses are the remaining algorithmic-refinement layer; the theorem
below proves that the three compiled CCIR executions compose without resetting
the resident table between calls. -/
theorem r2RuntimePipeline_compiled (c : R2Cfg) (s : R2Seed) (base : Int)
    (hBase : BaseOk c.arrayLen base)
    (marked packed out : AState)
    (hMark : (r2RootMarkProgram c).runFromArray (fun _ => 0) = some marked)
    (hPack : (r2RootPackProgram c).runFromArray marked.arr = some packed)
    (hMain : (r2RuntimeProgram c s).runFromArray packed.arr = some out) :
    ∃ mMark mPack mOut,
      Verified.MemFragment.evalMCCSequence
          ((r2RootMarkProgram c).initialMCCWithMem base
            (initialMem c.arrayLen base))
          (r2RootMarkProgram c).compile = some mMark ∧
      Verified.MemFragment.evalMCCSequence
          ((r2RootPackProgram c).initialMCCWithMem base mMark.mem)
          (r2RootPackProgram c).compile = some mPack ∧
      Verified.MemFragment.evalMCCSequence
          ((r2RuntimeProgram c s).initialMCCWithMem base mPack.mem)
          (r2RuntimeProgram c s).compile = some mOut ∧
      ARel (r2RuntimeProgram c s).regCount (r2RuntimeProgram c s).arrayLen
        base out mOut := by
  apply AProgram.evalCC_compile_fromArray_three
    (r2RootMarkProgram c) (r2RootPackProgram c) (r2RuntimeProgram c s)
    (r2RootMarkProgram_wf c) (r2RootPackProgram_wf c)
    (r2RuntimeProgram_wf c s) rfl rfl base hBase (fun _ => 0)
    (initialMem c.arrayLen base)
  · intro k hk
    exact initialMem_cell c.arrayLen base hk
  · intro _ _
    exact M_pos
  · exact hMark
  · exact hPack
  · exact hMain

#print axioms r2RootMarkProgram_wf
#print axioms r2RootPackProgram_wf
#print axioms r2RuntimeProgram_wf
#print axioms r2RootMarkProgram_compiled
#print axioms r2RootPackProgram_compiled
#print axioms r2RuntimeProgram_compiled
#print axioms r2RuntimePipeline_compiled

end LeanCompCert.Ports.R2SegSieve
