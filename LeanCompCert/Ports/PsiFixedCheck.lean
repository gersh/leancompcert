import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Ports.TrialDivisionFold
import LeanCompCert.Verified.Straight

/-!
# A ψ fixed-point slope check in the proved 64-bit fragment

The consumer's certificate (`AnalyticNT.ChebyshevPsi.checkAllPsiLeMul` /
`checkPsiLeMulFrom`) folds a fixed-point upper bound on the von Mangoldt
function over `n = 1, …, N` and compares the running sum against a slope at
every step.  Its per-`n` term is `⌈logUB (minFac n) · 2⁴⁰⌉` on prime powers
and `0` elsewhere, where `logUB` is a truncated-Maclaurin rational upper bound
on `log`.

This module supplies the same scan as a `Reflect.Program`: one flat loop of
`fuel · (td + 67)` rounds, `td + 67` rounds per candidate `n`:

* rounds `0 … td−1` — **trial phase**: divisor `d = rr + 2`; record the first
  divisor of `n` (that first hit is `minFac n` whenever `minFac n ≤ td + 1`);
* rounds `td … td+23` — **E phase**: 24 doubling steps compute `e` and
  `2^e` with `2^e ≤ pb < 2^(e+1)` for the base `pb` (the recorded divisor,
  or `n` itself when none was found), and 24 modular-power steps decide
  whether `n ∣ pb^j` for some `j ≤ 24` — exactly the prime-power test;
* round `td+24` — **X round**: the fixed-point argument
  `xh = ⌈(pb − 2^e)·2²⁸ / pb⌉`;
* rounds `td+25 … td+65` — **series phase**: 41 rounds of
  `t ← ⌈t·xh/2²⁸⌉`, accumulating `⌈t/(i+1)⌉` for `i < 40` and the tail
  `2·t₄₁` — an upward-rounded evaluation of the same 40-term Maclaurin
  majorant the certificate's `logUB` uses, at scale `2²⁸`;
* round `td+66` — **F round**: add `pp · (e·L2C + sum)` to the accumulator
  and test it against `n · K`, masked below `lo`.

Every intermediate the mathematics needs is either proved to stay in range or
**guarded**: the `ok` flag is cleared if the X-round quotient leaves
`[0, 2²⁷]`, if the series sum leaves `[0, 2³³]`, or if the accumulator add
wraps.  The output is `pass · ok`, so a run that returns `1` asserts the
conjunction it claims: no guard fired *and* every masked slope test held.

## What is proved here

`psProgram_denote`: the register program's `Program.denote` is a flat fold of
`psRound`, a transparent `Nat` function.  The re-blocking into candidates and
the closed form of one block live in `Ports/PsiFixedCheckSpec.lean`; the
identification of the per-candidate term with the certificate's own
`⌈logUB (minFac n)·2⁴⁰⌉` needs Mathlib (`Nat.minFac`, `IsPrimePow`, `ℚ`) and
is proved on the consumer side.

Nothing here is a certificate, nothing here asserts that any execution
happened, and nothing here adds an axiom.
-/

set_option maxRecDepth 8192

namespace LeanCompCert.Ports.PsiFixedCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight
open LeanCompCert.Ports.TrialDivisionFold (sel divStep)

/-! ## §1 Constants and parameters -/

/-- The fixed-point scale `2²⁸`. -/
def SC : Nat := 2 ^ 28

/-- `⌈(6931471808/10¹⁰)·2²⁸⌉ = 186065280`: an upper bound on `log 2 · 2²⁸` in
units of `2⁻²⁸`, matching the certificate's `log2UB = 6931471808/10¹⁰`.

Defined as the plain numeral: a definition body containing a closed `Nat`
division would be re-evaluated by the kernel's unaccelerated recursion at
every defeq that touches it (measured: `(kernel) deep recursion detected`).
`L2C_ub` is the fact consumers need. -/
def L2C : Nat := 186065280

/-- `log2UB ≤ L2C · 2⁻²⁸`, in cleared-denominator form. -/
theorem L2C_ub : 6931471808 * 2 ^ 28 ≤ L2C * 10 ^ 10 := by decide

/-- The series-sum guard: the true sum stays below `42·2²⁷ < 2³³`. -/
def CAP : Nat := 2 ^ 33

/-- Rounds per candidate beyond the trial phase: 24 E rounds, the X round,
41 series rounds, and the F round. -/
def extraRounds : Nat := 67

/-- One instance of the family: candidates `n ∈ [start, start + fuel)`,
`td` trial divisors per candidate, slope test `acc ≤ n · K` for `n ≥ lo`. -/
structure Params where
  /-- First candidate. -/
  start : Nat
  /-- Number of candidates. -/
  fuel : Nat
  /-- Number of trial divisors per candidate (`d = 2, …, td + 1`). -/
  td : Nat
  /-- The slope numerator, in units of `2⁻²⁸` per candidate. -/
  K : Nat
  /-- The first candidate at which the slope test is enforced. -/
  lo : Nat
  deriving Repr, DecidableEq

/-- Rounds per candidate. -/
def Params.R (P : Params) : Nat := P.td + extraRounds

/-- The scan ceiling `start + fuel`. -/
def Params.T (P : Params) : Nat := P.start + P.fuel

/-- Sizing side conditions; all decidable at each concrete instance. -/
structure Params.Sane (P : Params) : Prop where
  /-- At least one candidate. -/
  fuelPos : 0 < P.fuel
  /-- Candidates are positive. -/
  startPos : 0 < P.start
  /-- At least one trial divisor. -/
  tdPos : 0 < P.td
  /-- The scan ceiling fits the E phase (`e ≤ 23`, `v ≤ 24`). -/
  topSmall : P.start + P.fuel ≤ 2 ^ 24
  /-- The largest trial divisor stays below the scan ceiling. -/
  tdSmall : P.td + 2 ≤ P.start + P.fuel
  /-- The slope constant keeps `n · K` inside a word. -/
  kSmall : P.K < 2 ^ 30
  /-- The window edge is inside the scan. -/
  loSmall : P.lo ≤ P.start + P.fuel

/-! ## §2 Register layout

Registers `0 … 11` are carried across rounds; `12 … 49` are recomputed every
round; `50 …` are `Straight` temporaries.

| reg | meaning | | reg | meaning |
| --- | --- | --- | --- | --- |
| `0` | accumulator | | `24` | `pb`, the base |
| `1` | slope-test flag | | `25` | `n % d` |
| `2` | guard flag | | `26` | `d ∣ n` |
| `3` | recorded divisor `p` | | `27` | first-hit mask |
| `4` | found flag | | `28` | `2·pw` |
| `5` | `e` | | `29` | E-step condition |
| `6` | `pw = 2^e` | | `30` | `pow · pb` |
| `7` | `pow = pb^j mod n` | | `31` | `(pow·pb) % n` |
| `8` | prime-power flag | | `32`–`34` | X-round scratch |
| `9` | series power `t` | | `35`–`38` | `gX`, `xcap`, `tn`, `tq` |
| `10` | series sum | | `39`–`41` | `dv`, `tnm`, `term` |
| `11` | `xh` | | `42`–`48` | series/F scratch |
| `12` | `rr = k % R` | | `49` | epilogue output |
| `13` | `q = k / R` | | | |
| `14` | `n` | `15` | `d` | |
| `16`–`23` | phase masks | | | |
-/

/-- Temporaries start at `50`. -/
def cursor : Nat := 50

/-- Machine size: `50` named registers plus expression temporaries. -/
def regCount : Nat := 100

/-! ## §3 The loop body -/

/-- Decoding, phase masks, per-candidate reset, and the base `pb`. -/
def blkA (P : Params) : List Assign :=
  [ ⟨16, .bin .lt (.reg 12) (.lit P.td)⟩
  , ⟨17, .bin .mul (.bin .ge (.reg 12) (.lit P.td))
      (.bin .lt (.reg 12) (.lit (P.td + 24)))⟩
  , ⟨18, .bin .eq (.reg 12) (.lit (P.td + 24))⟩
  , ⟨19, .bin .mul (.bin .ge (.reg 12) (.lit (P.td + 25)))
      (.bin .lt (.reg 12) (.lit (P.td + 66)))⟩
  , ⟨20, .bin .mul (.bin .ge (.reg 12) (.lit (P.td + 25)))
      (.bin .lt (.reg 12) (.lit (P.td + 65)))⟩
  , ⟨21, .bin .eq (.reg 12) (.lit (P.td + 65))⟩
  , ⟨22, .bin .eq (.reg 12) (.lit (P.td + 66))⟩
  , ⟨23, .bin .eq (.reg 12) (.lit 0)⟩
  , ⟨14, .bin .add (.reg 13) (.lit P.start)⟩
  , ⟨15, .bin .add (.reg 12) (.lit 2)⟩
  , ⟨3, sel (.reg 23) (.lit 1) (.reg 3)⟩
  , ⟨4, sel (.reg 23) (.lit 0) (.reg 4)⟩
  , ⟨5, sel (.reg 23) (.lit 0) (.reg 5)⟩
  , ⟨6, sel (.reg 23) (.lit 1) (.reg 6)⟩
  , ⟨7, sel (.reg 23) (.lit 1) (.reg 7)⟩
  , ⟨8, sel (.reg 23) (.lit 0) (.reg 8)⟩
  , ⟨9, sel (.reg 23) (.lit 0) (.reg 9)⟩
  , ⟨10, sel (.reg 23) (.lit 0) (.reg 10)⟩
  , ⟨11, sel (.reg 23) (.lit 0) (.reg 11)⟩
  , ⟨24, sel (.reg 4) (.reg 3) (.reg 14)⟩ ]

/-- Trial updates and the E-phase doubling; `pm = pow · pb` feeds the modular
power step. -/
def blkB : List Assign :=
  [ ⟨26, .bin .eq (.reg 25) (.lit 0)⟩
  , ⟨27, .bin .mul (.bin .mul (.reg 16) (.bin .bxor (.reg 4) (.lit 1)))
      (.reg 26)⟩
  , ⟨3, sel (.reg 27) (.reg 15) (.reg 3)⟩
  , ⟨4, .bin .bor (.reg 4) (.bin .mul (.reg 16) (.reg 26))⟩
  , ⟨28, .bin .mul (.reg 6) (.lit 2)⟩
  , ⟨29, .bin .mul (.reg 17) (.bin .le (.reg 28) (.reg 24))⟩
  , ⟨5, .bin .add (.reg 5) (.reg 29)⟩
  , ⟨6, sel (.reg 29) (.reg 28) (.reg 6)⟩
  , ⟨30, .bin .mul (.reg 7) (.reg 24)⟩ ]

/-- E-phase finish and the X-round numerator. -/
def blkC : List Assign :=
  [ ⟨7, sel (.reg 17) (.reg 31) (.reg 7)⟩
  , ⟨8, .bin .bor (.reg 8) (.bin .mul (.reg 17) (.bin .eq (.reg 31) (.lit 0)))⟩
  , ⟨32, .bin .mul (.bin .le (.reg 6) (.reg 24))
      (.bin .sub (.reg 24) (.reg 6))⟩
  , ⟨33, .bin .add (.bin .mul (.lit SC) (.reg 32))
      (.bin .sub (.reg 24) (.lit 1))⟩ ]

/-- The X-round assignment (guarded), and the series product. -/
def blkD : List Assign :=
  [ ⟨35, .bin .le (.reg 34) (.lit (2 ^ 27))⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .bor (.reg 35) (.bin .bxor (.reg 18) (.lit 1)))⟩
  , ⟨36, .bin .add (.bin .mul (.reg 35) (.reg 34))
      (.bin .mul (.lit (2 ^ 27)) (.bin .bxor (.reg 35) (.lit 1)))⟩
  , ⟨11, sel (.reg 18) (.reg 36) (.reg 11)⟩
  , ⟨9, .bin .add (.bin .mul (.lit SC) (.reg 18))
      (.bin .mul (.bin .bxor (.reg 18) (.lit 1)) (.reg 9))⟩
  , ⟨10, sel (.reg 18) (.lit 0) (.reg 10)⟩
  , ⟨37, .bin .add (.lit (SC - 1)) (.bin .mul (.reg 9) (.reg 11))⟩ ]

/-- The series divisor. -/
def blkE (P : Params) : List Assign :=
  [ ⟨39, sel (.reg 20) (.bin .sub (.reg 12) (.lit (P.td + 24))) (.lit 1)⟩
  , ⟨40, .bin .add (.reg 38) (.bin .sub (.reg 39) (.lit 1))⟩ ]

/-- Series accumulation (guarded) and the F round. -/
def blkF (P : Params) : List Assign :=
  [ ⟨9, sel (.reg 19) (.reg 38) (.reg 9)⟩
  , ⟨42, .bin .add (.bin .mul (.reg 20) (.reg 41))
      (.bin .mul (.reg 21) (.bin .mul (.lit 2) (.reg 38)))⟩
  , ⟨43, .bin .add (.reg 10) (.reg 42)⟩
  , ⟨44, .bin .le (.reg 43) (.lit CAP)⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .bor (.reg 44) (.bin .bxor (.reg 19) (.lit 1)))⟩
  , ⟨45, .bin .add (.bin .mul (.reg 44) (.reg 43))
      (.bin .mul (.lit CAP) (.bin .bxor (.reg 44) (.lit 1)))⟩
  , ⟨10, sel (.reg 19) (.reg 45) (.reg 10)⟩
  , ⟨46, .bin .mul (.reg 8) (.bin .add (.bin .mul (.lit L2C) (.reg 5)) (.reg 10))⟩
  , ⟨47, .bin .add (.reg 0) (.bin .mul (.reg 22) (.reg 46))⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .ge (.reg 47) (.reg 0))⟩
  , ⟨0, .reg 47⟩
  , ⟨48, .bin .bor (.bin .le (.reg 0) (.bin .mul (.reg 14) (.lit P.K)))
      (.bin .lt (.reg 14) (.lit P.lo))⟩
  , ⟨1, .bin .mul (.reg 1) (.bin .bor (.reg 48) (.bin .bxor (.reg 22) (.lit 1)))⟩ ]

/-- The loop body. -/
def psBody (P : Params) : List Instr :=
  [ .binop 12 .urem .idx (.lit P.R)
  , .binop 13 .udiv .idx (.lit P.R) ] ++
  block cursor (blkA P) ++
  [ .binop 25 .urem (.reg 14) (.reg 15) ] ++
  block cursor blkB ++
  [ .binop 31 .urem (.reg 30) (.reg 14) ] ++
  block cursor blkC ++
  [ .binop 34 .udiv (.reg 33) (.reg 24) ] ++
  block cursor blkD ++
  [ .binop 38 .udiv (.reg 37) (.lit SC) ] ++
  block cursor (blkE P) ++
  [ .binop 41 .udiv (.reg 40) (.reg 39) ] ++
  block cursor (blkF P)

/-- Initialisation: the two flags start set, the divisor/power state starts at
its reset values so the invariant holds before the first reset. -/
def psInit : List Instr :=
  [ .mov 1 (.lit 1), .mov 2 (.lit 1), .mov 3 (.lit 1), .mov 6 (.lit 1)
  , .mov 7 (.lit 1) ]

/-- Accept exactly when every masked slope test held and no guard fired. -/
def psEpilogue : List Instr :=
  [ .binop 49 .mul (.reg 1) (.reg 2) ]

/-- The whole program. -/
def psProgram (P : Params) : Program := {
  regCount := regCount
  loopCount := P.fuel * P.R
  init := psInit
  body := psBody P
  epilogue := psEpilogue
  output := 49
}

/-! ## §4 Well-formedness -/

theorem blkA_wf (P : Params) : ∀ a ∈ blkA P, a.WF cursor := by
  intro a ha
  simp only [blkA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkA_room (P : Params) :
    ∀ a ∈ blkA P, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem blkB_wf : ∀ a ∈ blkB, a.WF cursor := by
  intro a ha
  simp only [blkB, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkB_room :
    ∀ a ∈ blkB, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkB, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem blkC_wf : ∀ a ∈ blkC, a.WF cursor := by
  intro a ha
  simp only [blkC, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkC_room :
    ∀ a ∈ blkC, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkC, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> simp [depth, sel, cursor, regCount]

theorem blkD_wf : ∀ a ∈ blkD, a.WF cursor := by
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkD_room :
    ∀ a ∈ blkD, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem blkE_wf (P : Params) : ∀ a ∈ blkE P, a.WF cursor := by
  intro a ha
  simp only [blkE, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkE_room (P : Params) :
    ∀ a ∈ blkE P, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkE, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl <;> simp [depth, sel, cursor, regCount]

theorem blkF_wf (P : Params) : ∀ a ∈ blkF P, a.WF cursor := by
  intro a ha
  simp only [blkF, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkF_room (P : Params) :
    ∀ a ∈ blkF P, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkF, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem psBody_wf (P : Params) : ∀ i ∈ psBody P, i.WF regCount := by
  intro i hi
  have hcur : cursor ≤ regCount := by simp [cursor, regCount]
  have hi' : i ∈
      ([ Instr.binop 12 .urem .idx (.lit P.R)
       , Instr.binop 13 .udiv .idx (.lit P.R) ] ++
        (block cursor (blkA P) ++
          ([Instr.binop 25 .urem (.reg 14) (.reg 15)] ++
            (block cursor blkB ++
              ([Instr.binop 31 .urem (.reg 30) (.reg 14)] ++
                (block cursor blkC ++
                  ([Instr.binop 34 .udiv (.reg 33) (.reg 24)] ++
                    (block cursor blkD ++
                      ([Instr.binop 38 .udiv (.reg 37) (.lit SC)] ++
                        (block cursor (blkE P) ++
                          ([Instr.binop 41 .udiv (.reg 40) (.reg 39)] ++
                            block cursor (blkF P)))))))))))) := by
    simpa [psBody, List.append_assoc] using hi
  rcases List.mem_append.mp hi' with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨by simp [regCount], trivial, trivial⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount (blkA P) (blkA_wf P) hcur (blkA_room P) i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount blkB blkB_wf hcur blkB_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount blkC blkC_wf hcur blkC_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount blkD blkD_wf hcur blkD_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount (blkE P) (blkE_wf P) hcur (blkE_room P) i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  · exact block_wf cursor regCount (blkF P) (blkF_wf P) hcur (blkF_room P) i h

theorem psProgram_wf (P : Params) : (psProgram P).WF := by
  refine ⟨by simp [psProgram, regCount], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ psInit := hi
    simp only [psInit, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [psProgram, regCount], trivial⟩
  · exact psBody_wf P
  · intro i hi
    have hi' : i ∈ psEpilogue := hi
    simp only [psEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl
    exact ⟨by simp [psProgram, regCount],
      by show (1 : Nat) < (psProgram P).regCount; simp [psProgram, regCount],
      by show (2 : Nat) < (psProgram P).regCount; simp [psProgram, regCount]⟩

/-! ## §5 The `Nat`-level round -/

/-- The twelve carried registers. -/
structure Vals where
  /-- Register `0`. -/
  acc : Nat
  /-- Register `1`. -/
  pass : Nat
  /-- Register `2`. -/
  ok : Nat
  /-- Register `3`. -/
  p : Nat
  /-- Register `4`. -/
  fnd : Nat
  /-- Register `5`. -/
  e : Nat
  /-- Register `6`. -/
  pw : Nat
  /-- Register `7`. -/
  pow : Nat
  /-- Register `8`. -/
  pp : Nat
  /-- Register `9`. -/
  t : Nat
  /-- Register `10`. -/
  sum : Nat
  /-- Register `11`. -/
  xh : Nat
  deriving DecidableEq, Repr

/-- Read the carried registers out of a machine state. -/
def valsOf (s : RegState) : Vals :=
  ⟨s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7, s 8, s 9, s 10, s 11⟩

/-- The `Nat`-level meaning of one flat round. -/
def psRound (P : Params) (k : Nat) (v : Vals) : Vals :=
  let rr := k % P.R
  let n := P.start + k / P.R
  let d := rr + 2
  let isT : Nat := if rr < P.td then 1 else 0
  let isE : Nat :=
    (if P.td ≤ rr then 1 else 0) * (if rr < P.td + 24 then 1 else 0)
  let isX : Nat := if rr = P.td + 24 then 1 else 0
  let isS : Nat :=
    (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 66 then 1 else 0)
  let isM : Nat :=
    (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 65 then 1 else 0)
  let isL : Nat := if rr = P.td + 65 then 1 else 0
  let isF : Nat := if rr = P.td + 66 then 1 else 0
  -- per-candidate reset
  let p0 := if rr = 0 then 1 else v.p
  let fnd0 := if rr = 0 then 0 else v.fnd
  let e0 := if rr = 0 then 0 else v.e
  let pw0 := if rr = 0 then 1 else v.pw
  let pow0 := if rr = 0 then 1 else v.pow
  let pp0 := if rr = 0 then 0 else v.pp
  let t0 := if rr = 0 then 0 else v.t
  let sum0 := if rr = 0 then 0 else v.sum
  let xh0 := if rr = 0 then 0 else v.xh
  let pb := if fnd0 = 1 then p0 else n
  -- trial phase
  let hit : Nat := if n % d = 0 then 1 else 0
  let p1 := if isT * (fnd0 ^^^ 1) * hit = 1 then d else p0
  let fnd1 := fnd0 ||| isT * hit
  -- E phase
  let tw2 := pw0 * 2
  let cE := isE * (if tw2 ≤ pb then 1 else 0)
  let e1 := e0 + cE
  let pw1 := if cE = 1 then tw2 else pw0
  let pr := pow0 * pb % n
  let pow1 := if isE = 1 then pr else pow0
  let pp1 := pp0 ||| isE * (if pr = 0 then 1 else 0)
  -- X round
  let xn1 := (if pw1 ≤ pb then 1 else 0) * (pb - pw1)
  let xq := (SC * xn1 + (pb - 1)) / pb
  let gX : Nat := if xq ≤ 2 ^ 27 then 1 else 0
  let ok1 := v.ok * (gX ||| isX ^^^ 1)
  let xcap := if gX = 1 then xq else 2 ^ 27
  let xh1 := if isX = 1 then xcap else xh0
  let t1 := if isX = 1 then SC else t0
  let sum1 := if isX = 1 then 0 else sum0
  -- series phase
  let tq := ((SC - 1) + t1 * xh1) / SC
  let dv := if isM = 1 then rr - (P.td + 24) else 1
  let term := (tq + (dv - 1)) / dv
  let t2 := if isS = 1 then tq else t1
  let scn := isM * term + isL * (2 * tq)
  let sum2 := sum1 + scn
  let gS : Nat := if sum2 ≤ CAP then 1 else 0
  let ok2 := ok1 * (gS ||| isS ^^^ 1)
  let scap := if gS = 1 then sum2 else CAP
  let sum3 := if isS = 1 then scap else sum1
  -- F round
  let lam := pp1 * (L2C * e1 + sum3)
  let acc1 := (v.acc + isF * lam) % M
  let ok3 := ok2 * (if v.acc ≤ acc1 then 1 else 0)
  let chk : Nat :=
    (if acc1 ≤ n * P.K then 1 else 0) ||| (if n < P.lo then 1 else 0)
  let pass1 := v.pass * (chk ||| isF ^^^ 1)
  { acc := acc1, pass := pass1, ok := ok3, p := p1, fnd := fnd1, e := e1,
    pw := pw1, pow := pow1, pp := pp1, t := t2, sum := sum3, xh := xh1 }

/-- The state invariant: exactly what keeps every machine truncation a no-op
and every register-divisor nonzero. -/
structure PSInv (P : Params) (s : RegState) : Prop where
  /-- Every register holds a word. -/
  word : ∀ i, s i < M
  /-- The slope-test flag is a bit. -/
  passLe : s 1 ≤ 1
  /-- The guard flag is a bit. -/
  okLe : s 2 ≤ 1
  /-- The recorded divisor is positive. -/
  pPos : 0 < s 3
  /-- The recorded divisor is inside the scan. -/
  pLe : s 3 ≤ P.T
  /-- The found flag is a bit. -/
  fndLe : s 4 ≤ 1
  /-- The doubling register is `2^e`. -/
  pwPow : s 6 = 2 ^ s 5
  /-- The doubling register stays inside the scan. -/
  pwLe : s 6 ≤ P.T
  /-- The modular power stays inside the scan. -/
  powLe : s 7 ≤ P.T
  /-- The prime-power flag is a bit. -/
  ppLe : s 8 ≤ 1
  /-- The series power stays at scale. -/
  tLe : s 9 ≤ SC
  /-- The series sum respects its guard. -/
  sumLe : s 10 ≤ CAP
  /-- The series argument stays below `2²⁷`. -/
  xhLe : s 11 ≤ 2 ^ 27

/-! ## §6 Machine-arithmetic helpers -/

private theorem lit0 : (0 : Nat) % M = 0 := by decide
private theorem lit1 : (1 : Nat) % M = 1 := by decide
private theorem lit2 : (2 : Nat) % M = 2 := by decide
private theorem litSC : SC % M = SC := by decide
private theorem litSC1 : (SC - 1) % M = SC - 1 := by decide
private theorem litCAP : CAP % M = CAP := by decide
private theorem lit27 : (134217728 : Nat) % M = 134217728 := by decide
private theorem litL2C : L2C % M = L2C := by decide

private theorem two24_lt_M : (2 : Nat) ^ 24 < M := by decide

/-- `a − b` computed in `u64`, for `b ≤ a < 2⁶⁴`. -/
private theorem subM (a b : Nat) (hba : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hb : b < M := Nat.lt_of_le_of_lt hba ha
  rw [show a + (M - b) = M + (a - b) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a - b < M by omega)]

/-! ### Sizing consequences of `Sane` -/

theorem Params.Sane.RPos {P : Params} (hP : P.Sane) : 0 < P.R := by
  have := hP.tdPos
  simp only [Params.R, extraRounds]
  omega

theorem Params.Sane.RLtM {P : Params} (hP : P.Sane) : P.R < M := by
  have h1 := hP.tdSmall
  have h2 := hP.topSmall
  have h3 : P.R = P.td + 67 := rfl
  have h4 : (2 : Nat) ^ 24 + 67 < M := by decide
  omega

theorem Params.Sane.RModM {P : Params} (hP : P.Sane) : P.R % M = P.R :=
  Nat.mod_eq_of_lt hP.RLtM

theorem Params.Sane.TLtM {P : Params} (hP : P.Sane) : P.T < M := by
  have := hP.topSmall
  have := two24_lt_M
  simp only [Params.T]
  omega

theorem Params.Sane.loopLtM {P : Params} (hP : P.Sane) {k : Nat}
    (hk : k < P.fuel * P.R) : k < M := by
  have hf : P.fuel ≤ 2 ^ 24 := by have := hP.topSmall; have := hP.startPos; omega
  have hr : P.R ≤ 2 ^ 24 + 67 := by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    show P.td + 67 ≤ 2 ^ 24 + 67
    omega
  have : P.fuel * P.R ≤ 2 ^ 24 * (2 ^ 24 + 67) :=
    Nat.mul_le_mul hf hr
  have hlt : (2 : Nat) ^ 24 * (2 ^ 24 + 67) < M := by decide
  omega

/-- The candidate decoded at a visited index is inside the scan range. -/
theorem Params.Sane.qLt {P : Params} (hP : P.Sane) {k : Nat}
    (hk : k < P.fuel * P.R) : k / P.R < P.fuel :=
  (Nat.div_lt_iff_lt_mul hP.RPos).mpr hk

/-! ## §7 Staged evaluation of the body -/

/-- The two index-decoding divisions. -/
def idxStep (R k : Nat) (s : RegState) : RegState :=
  (s.set 12 ((denoteOp .urem (k % M) (R % M)).getD 0)).set 13
    ((denoteOp .udiv (k % M) (R % M)).getD 0)

/-- A division instruction whose divisor is a literal. -/
def divLitStep (dest : Nat) (op : Op) (a c : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp op (s a) (c % M)).getD 0)

/-- After index decoding. -/
def st1 (P : Params) (k : Nat) (s : RegState) : RegState := idxStep P.R k s

/-- After the decode/reset block. -/
def st2 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st1 P k s) (blkA P)

/-- After the trial division. -/
def st3 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 25 .urem 14 15 (st2 P k s)

/-- After the trial/E block. -/
def st4 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st3 P k s) blkB

/-- After the modular-power division. -/
def st5 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 31 .urem 30 14 (st4 P k s)

/-- After the E-finish block. -/
def st6 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st5 P k s) blkC

/-- After the X-round division. -/
def st7 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 34 .udiv 33 24 (st6 P k s)

/-- After the X-assignment block. -/
def st8 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st7 P k s) blkD

/-- After the series-scale division. -/
def st9 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divLitStep 38 .udiv 37 SC (st8 P k s)

/-- After the series-divisor block. -/
def st10 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st9 P k s) (blkE P)

/-- After the series-term division. -/
def st11 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 41 .udiv 40 39 (st10 P k s)

/-- The whole round. -/
def psRun (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st11 P k s) (blkF P)

theorem psRun_eq_st (P : Params) (k : Nat) (s : RegState) :
    psRun P k s = run k (st11 P k s) (blkF P) := rfl

section Stage1

variable {P : Params} {k : Nat} {s : RegState}

private theorem idx12 (hP : P.Sane) (hk : k < P.fuel * P.R) :
    st1 P k s 12 = k % P.R := by
  have hne : P.R ≠ 0 := by have := hP.RPos; omega
  have h : k % P.R < M :=
    Nat.lt_trans (Nat.mod_lt _ hP.RPos) hP.RLtM
  simp [st1, idxStep, RegState.set, denoteOp, hP.RModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne, Nat.mod_eq_of_lt h]

private theorem idx13 (hP : P.Sane) (hk : k < P.fuel * P.R) :
    st1 P k s 13 = k / P.R := by
  have hne : P.R ≠ 0 := by have := hP.RPos; omega
  simp [st1, idxStep, RegState.set, denoteOp, hP.RModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self k P.R)
      (hP.loopLtM hk))]

private theorem idxOther (j : Nat) (h12 : j ≠ 12) (h13 : j ≠ 13) :
    st1 P k s j = s j := by
  simp [st1, idxStep, RegState.set, h12, h13]

end Stage1

/-- Everything the decode/reset block computes, from an abstract incoming
state. -/
theorem blkA_spec (P : Params) (k : Nat) (t : RegState) (rr q : Nat)
    (h12 : t 12 = rr) (h13 : t 13 = q)
    (htd : P.td % M = P.td)
    (htd24 : (P.td + 24) % M = P.td + 24)
    (htd25 : (P.td + 25) % M = P.td + 25)
    (htd65 : (P.td + 65) % M = P.td + 65)
    (htd66 : (P.td + 66) % M = P.td + 66)
    (hstartM : P.start % M = P.start)
    (hnM : (q + P.start) % M = P.start + q)
    (hnM' : (P.start + q) % M = P.start + q)
    (hdM : (rr + 2) % M = rr + 2)
    (h3M : t 3 % M = t 3) (h4M : t 4 % M = t 4) (h5M : t 5 % M = t 5)
    (h6M : t 6 % M = t 6) (h7M : t 7 % M = t 7) (h8M : t 8 % M = t 8)
    (h9M : t 9 % M = t 9) (h10M : t 10 % M = t 10) (h11M : t 11 % M = t 11)
    (hfnd : t 4 = 0 ∨ t 4 = 1) :
    run k t (blkA P) 0 = t 0 ∧ run k t (blkA P) 1 = t 1 ∧
    run k t (blkA P) 2 = t 2 ∧
    run k t (blkA P) 12 = rr ∧
    run k t (blkA P) 14 = P.start + q ∧
    run k t (blkA P) 15 = rr + 2 ∧
    run k t (blkA P) 16 = (if rr < P.td then 1 else 0) ∧
    run k t (blkA P) 17 =
      (if P.td ≤ rr then 1 else 0) * (if rr < P.td + 24 then 1 else 0) ∧
    run k t (blkA P) 18 = (if rr = P.td + 24 then 1 else 0) ∧
    run k t (blkA P) 19 =
      (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 66 then 1 else 0) ∧
    run k t (blkA P) 20 =
      (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 65 then 1 else 0) ∧
    run k t (blkA P) 21 = (if rr = P.td + 65 then 1 else 0) ∧
    run k t (blkA P) 22 = (if rr = P.td + 66 then 1 else 0) ∧
    run k t (blkA P) 3 = (if rr = 0 then 1 else t 3) ∧
    run k t (blkA P) 4 = (if rr = 0 then 0 else t 4) ∧
    run k t (blkA P) 5 = (if rr = 0 then 0 else t 5) ∧
    run k t (blkA P) 6 = (if rr = 0 then 1 else t 6) ∧
    run k t (blkA P) 7 = (if rr = 0 then 1 else t 7) ∧
    run k t (blkA P) 8 = (if rr = 0 then 0 else t 8) ∧
    run k t (blkA P) 9 = (if rr = 0 then 0 else t 9) ∧
    run k t (blkA P) 10 = (if rr = 0 then 0 else t 10) ∧
    run k t (blkA P) 11 = (if rr = 0 then 0 else t 11) ∧
    run k t (blkA P) 24 =
      (if (if rr = 0 then 0 else t 4) = 1
        then (if rr = 0 then 1 else t 3) else P.start + q) := by
  have hif : ∀ b : Nat, (if b = 0 then 1 else 0) % M = if b = 0 then 1 else 0 := by
    intro b; split <;> decide
  have hmm : ∀ (p q : Prop) [Decidable p] [Decidable q],
      ((if p then 1 else 0) * (if q then (1 : Nat) else 0)) % M =
        (if p then 1 else 0) * (if q then 1 else 0) := by
    intro p q _ _; split <;> split <;> decide
  by_cases hz : rr = 0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA, evalExpr, denoteOp, RegState.set, sel, h12, h13, hz,
        htd, htd24, htd25, htd65, htd66, hstartM, hnM, hnM', hdM, hif, hmm,
        lit1, lit2]
  · rcases hfnd with hf | hf <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA, evalExpr, denoteOp, RegState.set, sel, h12, h13, hz, hf,
        htd, htd24, htd25, htd65, htd66, hstartM, hnM, hnM', hdM, hif, hmm,
        lit1, lit2, h3M, h4M, h5M, h6M, h7M, h8M, h9M, h10M, h11M]

/-! ### The trial/E block, split in two -/

/-- The trial updates. -/
def blkB1 : List Assign :=
  [ ⟨26, .bin .eq (.reg 25) (.lit 0)⟩
  , ⟨27, .bin .mul (.bin .mul (.reg 16) (.bin .bxor (.reg 4) (.lit 1)))
      (.reg 26)⟩
  , ⟨3, sel (.reg 27) (.reg 15) (.reg 3)⟩
  , ⟨4, .bin .bor (.reg 4) (.bin .mul (.reg 16) (.reg 26))⟩ ]

/-- The E-phase doubling and the modular-power product. -/
def blkB2 : List Assign :=
  [ ⟨28, .bin .mul (.reg 6) (.lit 2)⟩
  , ⟨29, .bin .mul (.reg 17) (.bin .le (.reg 28) (.reg 24))⟩
  , ⟨5, .bin .add (.reg 5) (.reg 29)⟩
  , ⟨6, sel (.reg 29) (.reg 28) (.reg 6)⟩
  , ⟨30, .bin .mul (.reg 7) (.reg 24)⟩ ]

theorem blkB_split : blkB = blkB1 ++ blkB2 := rfl

/-- What the trial updates compute, from an abstract incoming state. -/
theorem blkB1_spec (k : Nat) (t : RegState) (nmd isT fnd0 d p0 : Nat)
    (h25 : t 25 = nmd) (h16 : t 16 = isT) (h4 : t 4 = fnd0)
    (h15 : t 15 = d) (h3 : t 3 = p0)
    (hisT : isT = 0 ∨ isT = 1) (hfnd : fnd0 = 0 ∨ fnd0 = 1)
    (hdM : d < M) (hpM : p0 < M) :
    run k t blkB1 3 =
      (if isT * (fnd0 ^^^ 1) * (if nmd = 0 then 1 else 0) = 1
        then d else p0) ∧
    run k t blkB1 4 = (fnd0 ||| isT * (if nmd = 0 then 1 else 0)) := by
  rcases hisT with hT | hT <;> rcases hfnd with hF | hF <;>
    by_cases hz : nmd = 0 <;>
      refine ⟨?_, ?_⟩ <;>
        simp [run, blkB1, evalExpr, denoteOp, RegState.set, sel, h25, h16, h4,
          h15, h3, hT, hF, hz, lit0, lit1, Nat.mod_eq_of_lt hdM,
          Nat.mod_eq_of_lt hpM]

/-- What the doubling and the power product compute. -/
theorem blkB2_spec (k : Nat) (t : RegState) (isE pw0 pb e0 pow0 : Nat)
    (h17 : t 17 = isE) (h6 : t 6 = pw0) (h24 : t 24 = pb)
    (h5 : t 5 = e0) (h7 : t 7 = pow0)
    (hisE : isE = 0 ∨ isE = 1)
    (hpwM : pw0 * 2 < M) (heM : e0 + 1 < M) (hpmM : pow0 * pb < M) :
    run k t blkB2 5 = e0 + isE * (if pw0 * 2 ≤ pb then 1 else 0) ∧
    run k t blkB2 6 =
      (if isE * (if pw0 * 2 ≤ pb then 1 else 0) = 1 then pw0 * 2 else pw0) ∧
    run k t blkB2 30 = pow0 * pb := by
  have hpw0M : pw0 < M := by omega
  have he0M : e0 < M := by omega
  rcases hisE with hE | hE <;> by_cases hle : pw0 * 2 ≤ pb <;>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [run, blkB2, evalExpr, denoteOp, RegState.set, sel, h17, h6, h24,
        h5, h7, hE, hle, lit1, lit2, Nat.mod_eq_of_lt hpwM,
        Nat.mod_eq_of_lt heM, Nat.mod_eq_of_lt hpmM,
        Nat.mod_eq_of_lt hpw0M, Nat.mod_eq_of_lt he0M]

/-- What the E-finish and the X-round numerator compute. -/
theorem blkC_spec (k : Nat) (t : RegState) (isE pr pow0 pp0 pw1 pb : Nat)
    (h17 : t 17 = isE) (h31 : t 31 = pr) (h7 : t 7 = pow0)
    (h8 : t 8 = pp0) (h6 : t 6 = pw1) (h24 : t 24 = pb)
    (hisE : isE = 0 ∨ isE = 1)
    (hpb1 : 1 ≤ pb) (hpbM : pb ≤ 2 ^ 24) (hpw1M : pw1 < M)
    (hprM : pr < M) (hpow0M : pow0 < M) (hpp0 : pp0 ≤ 1) :
    run k t blkC 7 = (if isE = 1 then pr else pow0) ∧
    run k t blkC 8 = (pp0 ||| isE * (if pr = 0 then 1 else 0)) ∧
    run k t blkC 33 =
      SC * ((if pw1 ≤ pb then 1 else 0) * (pb - pw1)) + (pb - 1) := by
  have hpbM' : pb < M := by have := two24_lt_M; omega
  have hsub1 : (pb + (M - 1)) % M = pb - 1 := subM pb 1 hpb1 hpbM'
  have hxn1M : SC * (pb - pw1) < M := by
    have h1 : pb - pw1 ≤ 2 ^ 24 := by omega
    have h2 : SC * (pb - pw1) ≤ SC * 2 ^ 24 := Nat.mul_le_mul_left _ h1
    have h3 : SC * 2 ^ 24 < M := by decide
    omega
  have hxnM : SC * (pb - pw1) + (pb - 1) < M := by
    have h1 : pb - pw1 ≤ 2 ^ 24 := by omega
    have h2 : SC * (pb - pw1) ≤ SC * 2 ^ 24 := Nat.mul_le_mul_left _ h1
    have h3 : SC * 2 ^ 24 + 2 ^ 24 < M := by decide
    omega
  have hpb1M : (pb - 1) % M = pb - 1 := Nat.mod_eq_of_lt (by omega)
  have hppor : (pp0 ||| 1) % M = pp0 ||| 1 := by
    rcases (show pp0 = 0 ∨ pp0 = 1 by omega) with h | h <;> subst h <;> decide
  by_cases hle : pw1 ≤ pb
  · have hsubp : (pb + (M - pw1)) % M = pb - pw1 := subM pb pw1 hle hpbM'
    rcases hisE with hE | hE <;> by_cases hz : pr = 0 <;>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [run, blkC, evalExpr, denoteOp, RegState.set, sel, h17, h31, h7,
          h8, h6, h24, hE, hz, hle, lit0, lit1, litSC, hsubp, hpb1M, hppor,
          Nat.mod_eq_of_lt hpbM', Nat.mod_eq_of_lt hpw1M,
          Nat.mod_eq_of_lt hprM, Nat.mod_eq_of_lt hpow0M, hsub1,
          Nat.mod_eq_of_lt hxn1M, Nat.mod_eq_of_lt hxnM,
          Nat.mod_eq_of_lt (show pp0 < M by omega)]
  · rcases hisE with hE | hE <;> by_cases hz : pr = 0 <;>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [run, blkC, evalExpr, denoteOp, RegState.set, sel, h17, h31, h7,
          h8, h6, h24, hE, hz, hle, lit0, lit1, litSC, hpb1M, hppor,
          Nat.mod_eq_of_lt hpbM', Nat.mod_eq_of_lt hpw1M,
          Nat.mod_eq_of_lt hprM, Nat.mod_eq_of_lt hpow0M, hsub1,
          Nat.mod_eq_of_lt (show pp0 < M by omega)]

/-- What the X assignment and the series product compute. -/
theorem blkD_spec (k : Nat) (t : RegState) (xq isX ok0 xh0 t0 sum0 : Nat)
    (h34 : t 34 = xq) (h18 : t 18 = isX) (h2 : t 2 = ok0)
    (h11 : t 11 = xh0) (h9 : t 9 = t0) (h10 : t 10 = sum0)
    (hisX : isX = 0 ∨ isX = 1) (hok0 : ok0 ≤ 1)
    (hxqM : xq < M) (hxh0 : xh0 ≤ 2 ^ 27) (ht0 : t0 ≤ SC)
    (hsum0M : sum0 < M) :
    run k t blkD 2 = ok0 * ((if xq ≤ 2 ^ 27 then 1 else 0) ||| isX ^^^ 1) ∧
    run k t blkD 11 =
      (if isX = 1 then (if (if xq ≤ 2 ^ 27 then 1 else 0) = 1 then xq else 2 ^ 27)
        else xh0) ∧
    run k t blkD 9 = (if isX = 1 then SC else t0) ∧
    run k t blkD 10 = (if isX = 1 then 0 else sum0) ∧
    run k t blkD 37 =
      (SC - 1) +
        (if isX = 1 then SC else t0) *
          (if isX = 1 then (if (if xq ≤ 2 ^ 27 then 1 else 0) = 1 then xq else 2 ^ 27)
            else xh0) := by
  have hSCM : SC < M := by decide
  have h27M : (2 : Nat) ^ 27 < M := by decide
  have hokM : ok0 < M := by omega
  have hxh0M : xh0 < M := by omega
  have ht0M : t0 < M := by omega
  have hSC27 : SC * 2 ^ 27 + SC < M := by decide
  have hxqSC : ∀ h : xq ≤ 2 ^ 27, SC * xq < M := by
    intro h
    have := Nat.mul_le_mul_left SC h
    omega
  have ht0xh0 : t0 * xh0 < M := by
    have := Nat.mul_le_mul ht0 hxh0
    omega
  have ht0xh0' : (SC - 1) + t0 * xh0 < M := by
    rw [Nat.add_comm]
    have := Nat.mul_le_mul ht0 hxh0
    omega
  by_cases hg : xq ≤ 2 ^ 27
  · have hm1 : SC * xq < M := hxqSC hg
    have hm2 : (SC - 1) + SC * xq < M := by
      rw [Nat.add_comm]
      have h1 := Nat.mul_le_mul_left SC hg
      have h2 : SC * 2 ^ 27 + SC < M := by decide
      omega
    rcases hisX with hX | hX <;>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkD, evalExpr, denoteOp, RegState.set, sel, h34, h18, h2,
          h11, h9, h10, hX, hg, lit0, lit1, lit27, litSC, litSC1,
          Nat.mod_eq_of_lt hxqM, Nat.mod_eq_of_lt hsum0M,
          Nat.mod_eq_of_lt hokM, Nat.mod_eq_of_lt hxh0M,
          Nat.mod_eq_of_lt ht0M, Nat.mod_eq_of_lt ht0xh0,
          Nat.mod_eq_of_lt ht0xh0', Nat.mod_eq_of_lt hm1,
          Nat.mod_eq_of_lt hm2]
  · rcases hisX with hX | hX <;>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkD, evalExpr, denoteOp, RegState.set, sel, h34, h18, h2,
          h11, h9, h10, hX, hg, lit0, lit1, lit27, litSC, litSC1,
          Nat.mod_eq_of_lt hxqM, Nat.mod_eq_of_lt hsum0M,
          Nat.mod_eq_of_lt hokM, Nat.mod_eq_of_lt hxh0M,
          Nat.mod_eq_of_lt ht0M, Nat.mod_eq_of_lt ht0xh0,
          Nat.mod_eq_of_lt ht0xh0',
          Nat.mod_eq_of_lt (show SC * 2 ^ 27 < M by decide),
          Nat.mod_eq_of_lt (show (SC - 1) + SC * 2 ^ 27 < M by decide)]

/-- What the series-divisor block computes. -/
theorem blkE_spec (P : Params) (k : Nat) (t : RegState) (isM rr tq : Nat)
    (h20 : t 20 = isM) (h12 : t 12 = rr) (h38 : t 38 = tq)
    (hisM : isM = 0 ∨ isM = 1)
    (hMrr : isM = 1 → P.td + 25 ≤ rr)
    (hrrB : rr < 2 ^ 25) (htd24 : (P.td + 24) % M = P.td + 24)
    (htqM : tq ≤ SC) :
    run k t (blkE P) 39 = (if isM = 1 then rr - (P.td + 24) else 1) ∧
    run k t (blkE P) 40 =
      tq + ((if isM = 1 then rr - (P.td + 24) else 1) - 1) := by
  have hSCM : SC < M := by decide
  have h25M : (2 : Nat) ^ 25 < M := by decide
  have htqM' : tq < M := by omega
  have hrrM : rr < M := by omega
  have haddM : ∀ a : Nat, a < M → (a + (1 + (M - 1))) % M = a := by
    intro a ha
    rw [show 1 + (M - 1) = M by decide, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ha
  rcases hisM with hI | hI
  · refine ⟨?_, ?_⟩ <;>
      simp [run, blkE, evalExpr, denoteOp, RegState.set, sel, h20, h12, h38,
        hI, lit1, Nat.mod_eq_of_lt htqM', haddM tq htqM']
  · have hrr : P.td + 25 ≤ rr := hMrr hI
    have hsub : (rr + (M - (P.td + 24))) % M = rr - (P.td + 24) :=
      subM rr (P.td + 24) (by omega) hrrM
    have hdv1 : 1 ≤ rr - (P.td + 24) := by omega
    have hdvM : rr - (P.td + 24) < M := by omega
    have hsub2 : (rr - (P.td + 24) + (M - 1)) % M = rr - (P.td + 24) - 1 :=
      subM _ 1 hdv1 hdvM
    have hsumM : tq + (rr - (P.td + 24) - 1) < M := by
      have h1 : rr - (P.td + 24) - 1 < 2 ^ 25 := by omega
      have h2 : SC + 2 ^ 25 < M := by decide
      omega
    refine ⟨?_, ?_⟩ <;>
      simp [run, blkE, evalExpr, denoteOp, RegState.set, sel, h20, h12, h38,
        hI, lit1, htd24, hsub, hsub2, Nat.mod_eq_of_lt htqM',
        Nat.mod_eq_of_lt hdvM, Nat.mod_eq_of_lt hsumM]

/-! ### The series/F block, split in two -/

/-- The guarded series accumulation. -/
def blkF1 : List Assign :=
  [ ⟨9, sel (.reg 19) (.reg 38) (.reg 9)⟩
  , ⟨42, .bin .add (.bin .mul (.reg 20) (.reg 41))
      (.bin .mul (.reg 21) (.bin .mul (.lit 2) (.reg 38)))⟩
  , ⟨43, .bin .add (.reg 10) (.reg 42)⟩
  , ⟨44, .bin .le (.reg 43) (.lit CAP)⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .bor (.reg 44) (.bin .bxor (.reg 19) (.lit 1)))⟩
  , ⟨45, .bin .add (.bin .mul (.reg 44) (.reg 43))
      (.bin .mul (.lit CAP) (.bin .bxor (.reg 44) (.lit 1)))⟩
  , ⟨10, sel (.reg 19) (.reg 45) (.reg 10)⟩ ]

/-- The F round: the term, the accumulator, and the two masked tests. -/
def blkF2 (P : Params) : List Assign :=
  [ ⟨46, .bin .mul (.reg 8) (.bin .add (.bin .mul (.lit L2C) (.reg 5)) (.reg 10))⟩
  , ⟨47, .bin .add (.reg 0) (.bin .mul (.reg 22) (.reg 46))⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .ge (.reg 47) (.reg 0))⟩
  , ⟨0, .reg 47⟩
  , ⟨48, .bin .bor (.bin .le (.reg 0) (.bin .mul (.reg 14) (.lit P.K)))
      (.bin .lt (.reg 14) (.lit P.lo))⟩
  , ⟨1, .bin .mul (.reg 1) (.bin .bor (.reg 48) (.bin .bxor (.reg 22) (.lit 1)))⟩ ]

theorem blkF_split (P : Params) : blkF P = blkF1 ++ blkF2 P := rfl

/-- What the guarded series accumulation computes. -/
theorem blkF1_spec (k : Nat) (t : RegState)
    (isS isM isL tq term t1 sum1 ok1 : Nat)
    (h19 : t 19 = isS) (h20 : t 20 = isM) (h21 : t 21 = isL)
    (h38 : t 38 = tq) (h41 : t 41 = term) (h9 : t 9 = t1)
    (h10 : t 10 = sum1) (h2 : t 2 = ok1)
    (hisS : isS ≤ 1) (hisM : isM ≤ 1) (hisL : isL ≤ 1)
    (htq : tq ≤ SC) (hterm : term ≤ SC) (hsum1 : sum1 ≤ CAP)
    (hok1 : ok1 ≤ 1) (ht1M : t1 < M) :
    run k t blkF1 9 = (if isS = 1 then tq else t1) ∧
    run k t blkF1 2 =
      ok1 * ((if sum1 + (isM * term + isL * (2 * tq)) ≤ CAP then 1 else 0)
        ||| isS ^^^ 1) ∧
    run k t blkF1 10 =
      (if isS = 1 then
        (if sum1 + (isM * term + isL * (2 * tq)) ≤ CAP
          then sum1 + (isM * term + isL * (2 * tq)) else CAP)
       else sum1) := by
  have hSCM : SC < M := by decide
  have hCAPM : CAP < M := by decide
  have hmt : isM * term ≤ term := by
    rcases (show isM = 0 ∨ isM = 1 by omega) with h | h <;> simp [h]
  have hlt2 : isL * (2 * tq) ≤ 2 * tq := by
    rcases (show isL = 0 ∨ isL = 1 by omega) with h | h <;> simp [h]
  have hmtM : isM * term < M := by omega
  have h2tqM : 2 * tq < M := by
    have : 2 * SC < M := by decide
    omega
  have hltM : isL * (2 * tq) < M := by omega
  have hscnM : isM * term + isL * (2 * tq) < M := by
    have : SC + 2 * SC < M := by decide
    omega
  have hsum2M : sum1 + (isM * term + isL * (2 * tq)) < M := by
    have : CAP + (SC + 2 * SC) < M := by decide
    omega
  have h1M : (1 : Nat) < M := by decide
  have hok1M : ok1 < M := by omega
  have hsum1M : sum1 < M := by omega
  have htqM : tq < M := by omega
  have htermM : term < M := by omega
  rcases (show isS = 0 ∨ isS = 1 by omega) with hS | hS <;> subst hS <;>
    by_cases hg : sum1 + (isM * term + isL * (2 * tq)) ≤ CAP <;>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [run, blkF1, evalExpr, denoteOp, RegState.set, sel, h19,
          h20, h21, h38, h41, h9, h10, h2, hg, lit1, lit2, litCAP,
          Nat.mod_eq_of_lt hmtM, Nat.mod_eq_of_lt h2tqM,
          Nat.mod_eq_of_lt hltM, Nat.mod_eq_of_lt hscnM,
          Nat.mod_eq_of_lt hsum2M, Nat.mod_eq_of_lt hok1M,
          Nat.mod_eq_of_lt hsum1M, Nat.mod_eq_of_lt htqM,
          Nat.mod_eq_of_lt ht1M]

end LeanCompCert.Ports.PsiFixedCheck
