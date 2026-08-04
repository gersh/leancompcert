import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Verified.Straight

/-!
# A dyadic prime-fold in the proved 64-bit fragment

The tail of a Ramaré-style `CE` estimate is a sum over the primes of a window
of a term built from `n`, from `k = ⌊log₂ n⌋`, and from a `2⁶⁴` fixed-point
image of `log 2`.  Every ingredient of that term is a *long division*, so the
whole thing is a scalar `Nat` fold whose per-element work is

* a trial-division primality test, and
* four fixed-point divisions assembled into one rounded value.

A `Reflect.Program` has exactly one loop of statically fixed length, so this
has to be **flattened**: the candidate and the round are both decoded from the
single loop index, one candidate occupies `R` consecutive rounds, and the
per-candidate term is accumulated once, at the last round of its block.

This module supplies that program and proves what it denotes:

* `ceRound` is the `Nat`-level meaning of one flat round;
* `ceProgram_denote` proves that `Program.denote` is the flat fold of
  `ceRound` over `List.range (len · R)`;
* `BlockedFold.foldl_range_mul` re-blocks that into `len` blocks of `R`.

## Four divisions, and why they are all defined

`denoteOp .udiv _ 0 = none` is the only way this body can fail, so every
divisor has to be proved nonzero *under the invariant*:

| divisor | why it is nonzero |
| --- | --- |
| `R` | `12 ≤ R` (`Params.Sane.RBig`) |
| `vA` | `denA > 0` or `C > 0` |
| `vB` | `denB > 0` or `C > 0` |
| `d` | `d ≥ 2` |

`C = n·(n−1) > 0` follows from `20000 < lo ≤ n`; `denA, denB > 0` follow from
`0 < pk ≤ n`, which is part of the invariant.

## Why the invariant has to mention the index

The dyadic exponent is carried, not recomputed: `pk` doubles at the first
round of a block exactly when `2·pk ≤ n`.  Whether that doubling is *allowed*
to fire depends on how far the candidate has advanced since the last one, and
the register file does not record the loop index.  So the invariant here is
`Inv c index s`, an **index-dependent** predicate, and
`Program.denote_eq_foldl_index` below is the corresponding fold bridge — the
same simulation argument as `RS62LadderEncoding.Program.denote_eq_foldl_mem`
with the invariant allowed to advance with the index.

## What is and is not proved here

Proved: the register program's `Program.denote` is a flat fold of `ceRound`, a
transparent `Nat` function; that fold re-blocks per candidate; and (in
`Ports/CeDyadicBlock.lean`) one block is one candidate.

Not here: that the per-candidate term bounds anything analytic, or that the
trial-division verdict is primality.  Those statements mention `Nat.Prime` and
`ℚ`, live in Mathlib's vocabulary, and this library has no Mathlib dependency;
they are proved on the consumer side and imported there, not assumed.

Nothing here is a certificate, nothing here asserts that any execution
happened, and nothing here adds an axiom.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LeanCompCert.Ports.CeDyadicFold

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

/-! ## §1 Parameters -/

/-- One instance of the family: scan the candidates `n ∈ [lo, lo + len)`,
spending `R` rounds on each. -/
structure Params where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Rounds per candidate; also the number of trial divisors. -/
  R : Nat
  /-- `⌊log₂ lo⌋`. -/
  k0 : Nat
  /-- `0` = lower (floor / max), `1` = upper (ceil / min). -/
  up : Nat
  /-- The `2⁶⁴` fixed-point image of `log 2`, rounded the safe way. -/
  lfx : Nat
  /-- The certified accumulator bound. -/
  bound : Nat
  deriving Repr, DecidableEq

/-- The sizing side conditions.  All decidable, all discharged by `decide` at
each concrete instance. -/
structure Params.Sane (c : Params) : Prop where
  /-- Makes `k·q₀` and `base + fB` words; see §2. -/
  loBig : 20000 < c.lo
  /-- At least one candidate. -/
  lenPos : 0 < c.len
  /-- Rounds `0 … 10` and `R − 1` must be distinct. -/
  RBig : 12 ≤ c.R
  /-- Keeps the round counter inside a word. -/
  RSmall : c.R < 2 ^ 31
  /-- `n < 2²⁵`, so `13·n² < 2⁵⁴`. -/
  topSmall : c.lo + c.len ≤ 2 ^ 25
  /-- Keeps the flat loop index inside a word. -/
  loopSmall : c.len * c.R < 2 ^ 48
  /-- Seeds the dyadic exponent. -/
  k0lo : 2 ^ c.k0 ≤ c.lo
  /-- Seeds the dyadic exponent. -/
  k0hi : c.lo < 2 ^ (c.k0 + 1)
  /-- The rounding direction is a bit. -/
  upBit : c.up ≤ 1
  /-- The fixed-point log is a word. -/
  lfxLt : c.lfx < 2 ^ 64
  /-- The certified bound is a word. -/
  boundLt : c.bound < 2 ^ 64

/-- The candidate the flat index `k` decodes to. -/
def cand (c : Params) (k : Nat) : Nat := c.lo + k / c.R

/-- The round-within-block the flat index `k` decodes to. -/
def rnd (c : Params) (k : Nat) : Nat := k % c.R

/-! ## §2 Shift-and-divide, the fixed-point long division

`sd D N` is `N · 2⁶⁴ / D` computed in eight byte-wide steps, each of which is
one 64-bit `udiv`.  The register program performs those eight steps at rounds
`1 … 8` of every block; this is the `Nat`-level function it realises, and it
is the one the consumer identifies with its own certificate term.
-/

/-- One byte-wide step of the shift-and-divide. -/
def sdStep (D : Nat) (s : Nat × Nat) : Nat × Nat :=
  (s.1 * 256 + (s.2 * 256) / D, (s.2 * 256) % D)

/-- `i` byte-wide steps. -/
def sdRun (D : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | i + 1, s => sdRun D i (sdStep D s)

/-- The whole eight-step division: `sd D N ≈ (N · 2⁶⁴ / D, N · 2⁶⁴ % D)`. -/
def sd (D N : Nat) : Nat × Nat := sdRun D 8 (0, N)

/-- `sdRun` peels its **last** step, which is the direction the register
program advances in. -/
theorem sdRun_succ (D i : Nat) :
    ∀ s : Nat × Nat, sdRun D (i + 1) s = sdStep D (sdRun D i s) := by
  induction i with
  | zero => intro s; rfl
  | succ i ih => intro s; exact ih (sdStep D s)

/-- The pair `(a, b)` stands for the number `a · D + b`, and each step
multiplies that number by `256`. -/
theorem sdRun_repr (D : Nat) :
    ∀ (i a b : Nat),
      (sdRun D i (a, b)).1 * D + (sdRun D i (a, b)).2 = (a * D + b) * 256 ^ i := by
  intro i
  induction i with
  | zero => intro a b; simp [sdRun]
  | succ i ih =>
      intro a b
      have hs : sdRun D (i + 1) (a, b) = sdRun D i (sdStep D (a, b)) := rfl
      rw [hs]
      have hstep : sdStep D (a, b) = (a * 256 + (b * 256) / D, (b * 256) % D) :=
        rfl
      rw [hstep, ih]
      have hdm : D * (b * 256 / D) + b * 256 % D = b * 256 :=
        Nat.div_add_mod (b * 256) D
      have hpow : (256 : Nat) ^ (i + 1) = 256 ^ i * 256 := rfl
      have hexp : (a * 256 + b * 256 / D) * D + b * 256 % D
          = (a * D + b) * 256 := by
        have h1 : (a * 256 + b * 256 / D) * D
            = a * 256 * D + b * 256 / D * D := Nat.add_mul _ _ _
        have h2 : b * 256 / D * D = D * (b * 256 / D) := Nat.mul_comm _ _
        have h3 : (a * D + b) * 256 = a * D * 256 + b * 256 := Nat.add_mul _ _ _
        have h4 : a * 256 * D = a * D * 256 := by
          rw [Nat.mul_assoc, Nat.mul_comm 256 D, ← Nat.mul_assoc]
        omega
      rw [hpow, ← Nat.mul_assoc, hexp, Nat.mul_right_comm]

/-- After at least one step the remainder is a genuine remainder. -/
theorem sdRun_snd_lt (D : Nat) (hD : 0 < D) :
    ∀ (i a b : Nat), b < D → (sdRun D i (a, b)).2 < D := by
  intro i
  induction i with
  | zero => intro a b hb; exact hb
  | succ i ih =>
      intro a b _
      have hs : sdRun D (i + 1) (a, b) = sdRun D i (sdStep D (a, b)) := rfl
      rw [hs]
      exact ih _ _ (Nat.mod_lt _ hD)

/-- Recovering the quotient and remainder from the representation. -/
theorem divmod_of_repr {D a b x : Nat} (hD : 0 < D) (hb : b < D)
    (h : a * D + b = x) : x / D = a ∧ x % D = b := by
  have hc : a * D = D * a := Nat.mul_comm _ _
  have hx : x = b + D * a := by omega
  subst hx
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

/-- **The specification of `sd`.**  The eight byte-wide steps compute the
64-bit fixed-point quotient and remainder exactly. -/
theorem sd_spec {D N : Nat} (hD : 0 < D) (hN : N < D) :
    (sd D N).1 = N * 2 ^ 64 / D ∧ (sd D N).2 = N * 2 ^ 64 % D := by
  have hsd : sd D N = sdRun D 8 (0, N) := rfl
  have hrepr := sdRun_repr D 8 0 N
  have hlt := sdRun_snd_lt D hD 8 0 N hN
  have hpow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hz : (0 * D + N) * 256 ^ 8 = N * 2 ^ 64 := by
    rw [Nat.zero_mul, Nat.zero_add, hpow]
  rw [hsd]
  have h := divmod_of_repr (a := (sdRun D 8 (0, N)).1)
    (b := (sdRun D 8 (0, N)).2) hD hlt (by rw [hrepr, hz])
  exact ⟨h.1.symm, h.2.symm⟩

/-! ## §3 The evaluation calculus

Every assignment below is proved by composing these, rather than by unfolding
`evalExpr`: each one turns one machine operation into ordinary `Nat`
arithmetic under exactly the side condition that makes the `u64` truncation a
no-op.  `sel_eval` is the important one — it retires a branch without a case
split, which is what keeps a body with a dozen masks from exploding.
-/

private theorem litM {v : Nat} (h : v < M) : v % M = v := Nat.mod_eq_of_lt h

theorem ev_reg (k : Nat) (t : RegState) (i : Nat) :
    evalExpr k t (.reg i) = t i := rfl

theorem ev_lit {k : Nat} {t : RegState} {v : Nat} (h : v < M) :
    evalExpr k t (.lit v) = v := litM h

theorem ev_idx {k : Nat} {t : RegState} (h : k < M) :
    evalExpr k t .idx = k := litM h

private theorem ev_bin (k : Nat) (t : RegState) (op : Op) (a b : Expr) :
    evalExpr k t (.bin op a b) =
      (denoteOp op (evalExpr k t a) (evalExpr k t b)).getD 0 := rfl

theorem ev_add {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) (h : x + y < M) :
    evalExpr k t (.bin .add a b) = x + y := by
  rw [ev_bin, ha, hb]; simp [denoteOp, litM h]

theorem ev_sub {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) (hle : y ≤ x)
    (hx : x < M) : evalExpr k t (.bin .sub a b) = x - y := by
  rw [ev_bin, ha, hb]
  have hMy : y ≤ M := Nat.le_trans hle (Nat.le_of_lt hx)
  have : x + (M - y) = M + (x - y) := by omega
  simp [denoteOp, this, Nat.add_mod_left, litM (show x - y < M by omega)]

theorem ev_mul {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) (h : x * y < M) :
    evalExpr k t (.bin .mul a b) = x * y := by
  rw [ev_bin, ha, hb]; simp [denoteOp, litM h]

theorem ev_bor {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) (h : (x ||| y) < M) :
    evalExpr k t (.bin .bor a b) = x ||| y := by
  rw [ev_bin, ha, hb]; simp [denoteOp, litM h]

theorem ev_bxor {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) (h : (x ^^^ y) < M) :
    evalExpr k t (.bin .bxor a b) = x ^^^ y := by
  rw [ev_bin, ha, hb]; simp [denoteOp, litM h]

theorem ev_eq {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) :
    evalExpr k t (.bin .eq a b) = if x = y then 1 else 0 := by
  rw [ev_bin, ha, hb]; rfl

theorem ev_ne {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) :
    evalExpr k t (.bin .ne a b) = if x = y then 0 else 1 := by
  rw [ev_bin, ha, hb]
  by_cases h : x = y <;> simp [denoteOp, h]

theorem ev_le {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) :
    evalExpr k t (.bin .le a b) = if x ≤ y then 1 else 0 := by
  rw [ev_bin, ha, hb]; rfl

theorem ev_ge {k : Nat} {t : RegState} {a b : Expr} {x y : Nat}
    (ha : evalExpr k t a = x) (hb : evalExpr k t b = y) :
    evalExpr k t (.bin .ge a b) = if x ≥ y then 1 else 0 := by
  rw [ev_bin, ha, hb]; rfl

/-- Branchless select for a `0/1` condition: `c·a + (c ⊕ 1)·b`. -/
def sel (c a b : Expr) : Expr :=
  .bin .add (.bin .mul c a) (.bin .mul (.bin .bxor c (.lit 1)) b)

/-- **The select, retired without a case split.** -/
theorem sel_eval {k : Nat} {t : RegState} {ec ea eb : Expr} {cv av bv : Nat}
    (hc : evalExpr k t ec = cv) (hcle : cv ≤ 1)
    (ha : cv = 1 → evalExpr k t ea = av) (hb : cv = 0 → evalExpr k t eb = bv)
    (hav : av < M) (hbv : bv < M) :
    evalExpr k t (sel ec ea eb) = if cv = 1 then av else bv := by
  have hM : (1 : Nat) < M := by decide
  rcases (show cv = 0 ∨ cv = 1 by omega) with h | h
  · have hbv' := hb h
    subst h
    have h1 : evalExpr k t (.bin .mul ec ea) = 0 * evalExpr k t ea :=
      ev_mul hc rfl (by rw [Nat.zero_mul]; exact M_pos)
    have hx : evalExpr k t (.bin .bxor ec (.lit 1)) = 0 ^^^ 1 :=
      ev_bxor hc (ev_lit hM) (by decide)
    have h2 : evalExpr k t (.bin .mul (.bin .bxor ec (.lit 1)) eb)
        = (0 ^^^ 1) * bv := ev_mul hx hbv' (by simpa using hbv)
    show (denoteOp .add (evalExpr k t (.bin .mul ec ea))
      (evalExpr k t (.bin .mul (.bin .bxor ec (.lit 1)) eb))).getD 0 = _
    rw [h1, h2]
    simp [denoteOp, litM hbv]
  · have hav' := ha h
    subst h
    have h1 : evalExpr k t (.bin .mul ec ea) = 1 * av :=
      ev_mul hc hav' (by simpa using hav)
    have hx : evalExpr k t (.bin .bxor ec (.lit 1)) = 1 ^^^ 1 :=
      ev_bxor hc (ev_lit hM) (by decide)
    have h2 : evalExpr k t (.bin .mul (.bin .bxor ec (.lit 1)) eb)
        = (1 ^^^ 1) * evalExpr k t eb :=
      ev_mul hx rfl (by simp [show (1 : Nat) ^^^ 1 = 0 from by decide]; exact M_pos)
    show (denoteOp .add (evalExpr k t (.bin .mul ec ea))
      (evalExpr k t (.bin .mul (.bin .bxor ec (.lit 1)) eb))).getD 0 = _
    rw [h1, h2]
    simp [denoteOp, litM hav]

/-! ### Bit-sized values -/

theorem bit_bor {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : (x ||| y) ≤ 1 := by
  rcases (show x = 0 ∨ x = 1 by omega) with h | h <;>
    rcases (show y = 0 ∨ y = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
      decide

theorem bit_bxor {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : (x ^^^ y) ≤ 1 := by
  rcases (show x = 0 ∨ x = 1 by omega) with h | h <;>
    rcases (show y = 0 ∨ y = 1 by omega) with h' | h' <;> subst h <;> subst h' <;>
      decide

/-! ## §4 Register layout

| reg | meaning | | reg | meaning | | reg | meaning |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `0` | `acc` | | `20` | `C = n(n−1)` | | `40` | `FB` |
| `1` | `ok` | | `21` | `d` | | `41` | `a1` |
| `2` | `pk` | | `22` | `n²` | | `42` | `ge` |
| `3` | `kk` | | `23` | `pk²` | | `43` | `cb` |
| `4` | `cf` | | `24` | `n·pk` | | `44` | `uA` |
| `5` | `qA` | | `25` | `U` | | `45` | `vA` |
| `6` | `rA` | | `26` | `V` | | `46` | `uB` |
| `7` | `qB` | | `27` | `numA` | | `47` | `vB` |
| `8` | `rB` | | `28` | `denA` | | `48` | `wA` |
| `9` | `q0` | | `29` | `numB` | | `49` | `wB` |
| `10` | `r0` | | `30` | `denB` | | `50` | `n / d` |
| `11` | `fA` | | `31` | `act` | | `51` | `zA` |
| `12` | `fB` | | `32` | `isq` | | `52` | `zB` |
| `13` | `idx / R` | | `33` | `isf` | | `53` | `n % d` |
| `14` | `rr` | | `34` | `qA0` | | `54` | `d ∣ n` |
| `15` | `n` | | `35` | `rA0` | | `55` | `FA2` |
| `16` | `first` | | `36` | `qB0` | | `56` | `FB2` |
| `17` | `last` | | `37` | `rB0` | | `57` | `a1b` |
| `18` | `2·pk` | | `38` | `cf0` | | `58` | `ge2` |
| `19` | `dob` | | `39` | `FA` | | `59` | `tA` |

and `60` `base`, `61` `tB`, `62` `t`, `63` `ct`, `64`/`65` the epilogue.
-/

/-- Registers `0 … 79` are named; `80 …` are `Straight` temporaries. -/
def cursor : Nat := 80

/-- The machine's register count. -/
def regCount : Nat := 200

/-- One `udiv` instruction's `Nat`-level effect. -/
def divStep (dest a b : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp .udiv (s a) (s b)).getD 0)

/-- The index-decoding division, whose divisor is a literal. -/
def idxStep (R k : Nat) (s : RegState) : RegState :=
  s.set 13 ((denoteOp .udiv (k % M) (R % M)).getD 0)

/-! ## §5 The loop body -/

/-- Index decoding: the round, the candidate, and the two block-edge masks. -/
def blkDec (c : Params) : List Assign :=
  [ ⟨14, .bin .sub .idx (.bin .mul (.reg 13) (.lit c.R))⟩
  , ⟨15, .bin .add (.lit c.lo) (.reg 13)⟩
  , ⟨16, .bin .eq (.reg 14) (.lit 0)⟩
  , ⟨17, .bin .eq (.reg 14) (.lit (c.R - 1))⟩ ]

/-- The dyadic bump: `pk` doubles at the first round of a block when `2·pk`
still fits below the candidate. -/
def blkBump : List Assign :=
  [ ⟨18, .bin .mul (.reg 2) (.lit 2)⟩
  , ⟨19, .bin .mul (.reg 16) (.bin .le (.reg 18) (.reg 15))⟩
  , ⟨2, sel (.reg 19) (.reg 18) (.reg 2)⟩
  , ⟨3, .bin .add (.reg 3) (.reg 19)⟩ ]

/-- The geometry of one candidate, and this round's trial divisor. -/
def blkGeom : List Assign :=
  [ ⟨20, .bin .mul (.reg 15) (.bin .sub (.reg 15) (.lit 1))⟩
  , ⟨21, sel (.reg 16) (.lit 2)
      (.bin .add (.bin .mul (.lit 2) (.reg 14)) (.lit 1))⟩
  , ⟨22, .bin .mul (.reg 15) (.reg 15)⟩
  , ⟨23, .bin .mul (.reg 2) (.reg 2)⟩
  , ⟨24, .bin .mul (.reg 15) (.reg 2)⟩
  , ⟨25, .bin .sub (.reg 22) (.reg 23)⟩
  , ⟨26, .bin .sub (.bin .mul (.lit 4) (.reg 23)) (.reg 22)⟩ ]

/-- The four fixed-point operands, selected by the rounding direction.  `up`
is a compile-time parameter, so this select happens in Lean, not at run time:
the emitted C carries only the branch the instance uses. -/
def blkNum (c : Params) : List Assign :=
  [ ⟨27, if c.up = 1 then .reg 25 else .bin .mul (.lit 3) (.reg 25)⟩
  , ⟨28, if c.up = 1 then .bin .mul (.lit 2) (.reg 24)
      else .bin .add (.bin .add (.reg 22) (.bin .mul (.lit 4) (.reg 24)))
        (.reg 23)⟩
  , ⟨29, if c.up = 1 then .bin .mul (.lit 3) (.reg 26) else .reg 26⟩
  , ⟨30, if c.up = 1 then
        .bin .add (.bin .add (.bin .mul (.lit 4) (.reg 23))
          (.bin .mul (.lit 8) (.reg 24))) (.reg 22)
      else .bin .mul (.lit 4) (.reg 24)⟩ ]

/-- The round-kind masks: the eight division rounds, the `log 2` round, and
the finalisation round. -/
def blkMask : List Assign :=
  [ ⟨31, .bin .mul (.bin .le (.lit 1) (.reg 14)) (.bin .le (.reg 14) (.lit 8))⟩
  , ⟨32, .bin .eq (.reg 14) (.lit 9)⟩
  , ⟨33, .bin .eq (.reg 14) (.lit 10)⟩ ]

/-- The per-candidate reset. -/
def blkRst : List Assign :=
  [ ⟨34, sel (.reg 16) (.lit 0) (.reg 5)⟩
  , ⟨35, sel (.reg 16) (.reg 27) (.reg 6)⟩
  , ⟨36, sel (.reg 16) (.lit 0) (.reg 7)⟩
  , ⟨37, sel (.reg 16) (.reg 29) (.reg 8)⟩
  , ⟨38, sel (.reg 16) (.lit 0) (.reg 4)⟩ ]

/-- The rounded quotients and the sign of the assembly. -/
def blkFAB (c : Params) : List Assign :=
  [ ⟨39, .bin .add (.reg 34)
      (.bin .mul (.lit c.up) (.bin .ne (.reg 35) (.lit 0)))⟩
  , ⟨40, .bin .add (.reg 36)
      (.bin .mul (.lit (1 - c.up)) (.bin .ne (.reg 37) (.lit 0)))⟩
  , ⟨41, .bin .mul (.bin .add (.reg 3) (.lit 1)) (.reg 10)⟩
  , ⟨42, .bin .le (.reg 41) (.reg 40)⟩
  , ⟨43, .bin .bxor (.reg 42) (.lit c.up)⟩ ]

/-- The first division slot. -/
def blkUVa (c : Params) : List Assign :=
  [ ⟨44, sel (.reg 31) (.bin .mul (.reg 35) (.lit 256))
      (sel (.reg 32) (.lit c.lfx)
        (sel (.reg 33)
          (.bin .add (.bin .add (.bin .mul (.reg 3) (.reg 10)) (.reg 39))
            (.bin .mul (.lit c.up) (.bin .sub (.reg 20) (.lit 1))))
          (.lit 0)))⟩
  , ⟨45, sel (.reg 31) (.reg 28) (.reg 20)⟩ ]

/-- `|FB − a1|`, materialised into register `66` so that neither machine
subtraction can underflow. -/
def blkAbs : List Assign :=
  [ ⟨66, sel (.reg 42) (.bin .sub (.reg 40) (.reg 41))
      (.bin .sub (.reg 41) (.reg 40))⟩ ]

/-- The second division slot. -/
def blkUVb : List Assign :=
  [ ⟨46, sel (.reg 31) (.bin .mul (.reg 37) (.lit 256))
      (sel (.reg 33)
        (.bin .add (.reg 66)
          (.bin .mul (.reg 43) (.bin .sub (.reg 20) (.lit 1))))
        (.lit 0))⟩
  , ⟨47, sel (.reg 31) (.reg 30) (.reg 20)⟩ ]

/-- The two division slots. -/
def blkUV (c : Params) : List Assign := blkUVa c ++ blkUVb

/-- The division-free stretch before the three data `udiv`s. -/
def blkA (c : Params) : List Assign :=
  blkDec c ++ (blkBump ++ (blkGeom ++ (blkNum c ++ (blkMask ++ (blkRst ++
    (blkFAB c ++ (blkAbs ++ (blkUVa c ++ blkUVb))))))))

/-- The remainders, and the trial-division verdict. -/
def blkZ : List Assign :=
  [ ⟨51, .bin .sub (.reg 44) (.bin .mul (.reg 48) (.reg 45))⟩
  , ⟨52, .bin .sub (.reg 46) (.bin .mul (.reg 49) (.reg 47))⟩
  , ⟨53, .bin .sub (.reg 15) (.bin .mul (.reg 50) (.reg 21))⟩
  , ⟨54, .bin .eq (.reg 53) (.lit 0)⟩
  , ⟨4, .bin .bor (.reg 38) (.reg 54)⟩ ]

/-- The carried division state. -/
def blkUpd : List Assign :=
  [ ⟨5, sel (.reg 31)
      (.bin .add (.bin .mul (.reg 34) (.lit 256)) (.reg 48)) (.reg 34)⟩
  , ⟨6, sel (.reg 31) (.reg 51) (.reg 35)⟩
  , ⟨7, sel (.reg 31)
      (.bin .add (.bin .mul (.reg 36) (.lit 256)) (.reg 49)) (.reg 36)⟩
  , ⟨8, sel (.reg 31) (.reg 52) (.reg 37)⟩
  , ⟨9, sel (.reg 32) (.reg 48) (.reg 9)⟩
  , ⟨10, sel (.reg 32) (.reg 51) (.reg 10)⟩
  , ⟨11, sel (.reg 33) (.reg 48) (.reg 11)⟩
  , ⟨12, sel (.reg 33) (.reg 49) (.reg 12)⟩ ]

/-- The assembly's straight prefix. -/
def blkAsmA (c : Params) : List Assign :=
  [ ⟨55, .bin .add (.reg 5) (.bin .mul (.lit c.up) (.bin .ne (.reg 6) (.lit 0)))⟩
  , ⟨56, .bin .add (.reg 7)
      (.bin .mul (.lit (1 - c.up)) (.bin .ne (.reg 8) (.lit 0)))⟩
  , ⟨57, .bin .mul (.bin .add (.reg 3) (.lit 1)) (.reg 10)⟩
  , ⟨58, .bin .le (.reg 57) (.reg 56)⟩
  , ⟨59, .bin .add (.bin .mul (.reg 3) (.reg 9)) (.reg 11)⟩
  , ⟨60, .bin .mul (.bin .add (.reg 3) (.lit 1)) (.reg 9)⟩ ]

/-- The rounded second branch. -/
def blkT1 : List Assign :=
  [ ⟨61, sel (.reg 58)
      (sel (.bin .le (.reg 12) (.reg 60)) (.bin .sub (.reg 60) (.reg 12))
        (.reg 59))
      (.bin .add (.reg 60) (.reg 12))⟩ ]

/-- The rounding direction's choice between the two branches. -/
def blkT2 (c : Params) : List Assign :=
  [ ⟨62, if c.up = 1 then
        sel (.bin .le (.reg 59) (.reg 61)) (.reg 59) (.reg 61)
      else sel (.bin .le (.reg 59) (.reg 61)) (.reg 61) (.reg 59)⟩ ]

/-- The block-edge and trial-division masks. -/
def blkT3 : List Assign :=
  [ ⟨63, .bin .mul
      (.bin .mul (.reg 17) (.bin .eq (.reg 4) (.lit 0))) (.reg 62)⟩ ]

/-- Masked accumulation, with the unsigned-wrap check. -/
def blkAcc : List Assign :=
  [ ⟨1, .bin .mul (.reg 1) (.bin .ge (.bin .add (.reg 0) (.reg 63)) (.reg 0))⟩
  , ⟨0, .bin .add (.reg 0) (.reg 63)⟩ ]

/-- The division-free stretch after the three data `udiv`s. -/
def blkB (c : Params) : List Assign :=
  blkZ ++ (blkUpd ++ (blkAsmA c ++ (blkT1 ++ (blkT2 c ++ (blkT3 ++ blkAcc)))))

/-- The loop body: four `udiv`s and two straight-line blocks.  The `++`s are
parenthesised to the right so that `denoteInstrs_append` peels one stage at a
time. -/
def ceBody (c : Params) : List Instr :=
  [ .binop 13 .udiv .idx (.lit c.R) ] ++
    (block cursor (blkA c) ++
      ([ .binop 48 .udiv (.reg 44) (.reg 45) ] ++
        ([ .binop 49 .udiv (.reg 46) (.reg 47) ] ++
          ([ .binop 50 .udiv (.reg 15) (.reg 21) ] ++
            block cursor (blkB c)))))

/-- The `Nat`-level meaning of one flat round. -/
def ceRun (c : Params) (k : Nat) (s : RegState) : RegState :=
  let s := idxStep c.R k s
  let s := run k s (blkA c)
  let s := divStep 48 44 45 s
  let s := divStep 49 46 47 s
  let s := divStep 50 15 21 s
  run k s (blkB c)

/-- Initialisation: the no-wrap flag, and the dyadic exponent's seed. -/
def ceInit (c : Params) : List Instr :=
  [ .mov 1 (.lit 1), .mov 2 (.lit (2 ^ c.k0)), .mov 3 (.lit c.k0) ]

/-- Accept exactly when no accumulator step wrapped and the total is on the
certified side of `bound`. -/
def ceEpilogue (c : Params) : List Instr :=
  [ .binop 64 (if c.up = 1 then .le else .ge) (.reg 0) (.lit c.bound)
  , .binop 65 .mul (.reg 1) (.reg 64) ]

/-- The whole program. -/
def ceProgram (c : Params) : Program := {
  regCount := regCount
  loopCount := c.len * c.R
  init := ceInit c
  body := ceBody c
  epilogue := ceEpilogue c
  output := 65
}

/-! ## §6 The `Nat`-level round -/

/-- The thirteen carried registers. -/
structure Vals where
  /-- Register `0`. -/
  acc : Nat
  /-- Register `1`. -/
  ok : Nat
  /-- Register `2`. -/
  pk : Nat
  /-- Register `3`. -/
  kk : Nat
  /-- Register `4`. -/
  cf : Nat
  /-- Register `5`. -/
  qA : Nat
  /-- Register `6`. -/
  rA : Nat
  /-- Register `7`. -/
  qB : Nat
  /-- Register `8`. -/
  rB : Nat
  /-- Register `9`. -/
  q0 : Nat
  /-- Register `10`. -/
  r0 : Nat
  /-- Register `11`. -/
  fA : Nat
  /-- Register `12`. -/
  fB : Nat
  deriving DecidableEq, Repr

/-- Read the carried registers out of a machine state. -/
def valsOf (s : RegState) : Vals :=
  ⟨s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7, s 8, s 9, s 10, s 11, s 12⟩

set_option linter.unusedVariables false in
/--
**One flat round, in ordinary `Nat` arithmetic.**

Index decoding, the dyadic bump, the geometry of the candidate, one byte of
each of the two fixed-point long divisions, one trial divisor, and an assembly
that is masked so it only contributes at the last round of a block.
-/
def ceRound (c : Params) (idx : Nat) (v : Vals) : Vals :=
  let q     := idx / c.R
  let rr    := idx % c.R
  let n     := c.lo + q
  let first := if rr = 0 then 1 else 0
  let last  := if rr = c.R - 1 then 1 else 0
  let pk2   := v.pk * 2
  let dob   := first * (if pk2 ≤ n then 1 else 0)
  let pk    := if dob = 1 then pk2 else v.pk
  let kk    := v.kk + dob
  let C     := n * (n - 1)
  let d     := if rr = 0 then 2 else 2 * rr + 1
  let n2    := n * n
  let p2    := pk * pk
  let np    := n * pk
  let U     := n2 - p2
  let V     := 4 * p2 - n2
  let numA  := if c.up = 1 then U else 3 * U
  let denA  := if c.up = 1 then 2 * np else n2 + 4 * np + p2
  let numB  := if c.up = 1 then 3 * V else V
  let denB  := if c.up = 1 then 4 * p2 + 8 * np + n2 else 4 * np
  let act   := if 1 ≤ rr ∧ rr ≤ 8 then 1 else 0
  let isq   := if rr = 9 then 1 else 0
  let isf   := if rr = 10 then 1 else 0
  let qA0   := if rr = 0 then 0 else v.qA
  let rA0   := if rr = 0 then numA else v.rA
  let qB0   := if rr = 0 then 0 else v.qB
  let rB0   := if rr = 0 then numB else v.rB
  let cf0   := if rr = 0 then 0 else v.cf
  let FA    := qA0 + c.up * (if rA0 = 0 then 0 else 1)
  let FB    := qB0 + (1 - c.up) * (if rB0 = 0 then 0 else 1)
  let a1    := (kk + 1) * v.r0
  let ge    := if a1 ≤ FB then 1 else 0
  let cb    := ge ^^^ c.up
  let uA    := if act = 1 then rA0 * 256
               else if isq = 1 then c.lfx
               else if isf = 1 then kk * v.r0 + FA + c.up * (C - 1) else 0
  let vA    := if act = 1 then denA else C
  let uB    := if act = 1 then rB0 * 256
               else if isf = 1 then (if ge = 1 then FB - a1 else a1 - FB)
                                     + cb * (C - 1) else 0
  let vB    := if act = 1 then denB else C
  let wA    := uA / vA
  let zA    := uA % vA
  let wB    := uB / vB
  let zB    := uB % vB
  let cf    := cf0 ||| (if n % d = 0 then 1 else 0)
  let qA    := if act = 1 then qA0 * 256 + wA else qA0
  let rA    := if act = 1 then zA else rA0
  let qB    := if act = 1 then qB0 * 256 + wB else qB0
  let rB    := if act = 1 then zB else rB0
  let q0    := if isq = 1 then wA else v.q0
  let r0    := if isq = 1 then zA else v.r0
  let fA    := if isf = 1 then wA else v.fA
  let fB    := if isf = 1 then wB else v.fB
  let FA2   := qA + c.up * (if rA = 0 then 0 else 1)
  let FB2   := qB + (1 - c.up) * (if rB = 0 then 0 else 1)
  let a1b   := (kk + 1) * r0
  let ge2   := if a1b ≤ FB2 then 1 else 0
  let tA    := kk * q0 + fA
  let base  := (kk + 1) * q0
  let tB    := if ge2 = 1 then (if fB ≤ base then base - fB else tA)
               else base + fB
  let t     := if c.up = 1 then min tA tB else max tA tB
  let ct    := last * (if cf = 0 then 1 else 0) * t
  { acc := (v.acc + ct) % M, ok := if v.acc + ct < M then v.ok else 0,
    pk := pk, kk := kk, cf := cf, qA := qA, rA := rA, qB := qB, rB := rB,
    q0 := q0, r0 := r0, fA := fA, fB := fB }

/-! ## §7 Well-formedness

Each block is checked once, per assignment: it writes below the temporary
cursor, reads below it, is division-free, and its compiled temporaries fit
inside `regCount`.  Nothing here depends on the loop length.
-/

private theorem allWF (as : List Assign)
    (h : ∀ a ∈ as, a.dest < cursor ∧ a.expr.RegsBelow cursor ∧
      NoDiv a.expr = true) : ∀ a ∈ as, a.WF cursor := h

theorem blkDec_wf (c : Params) : ∀ a ∈ blkDec c, a.WF cursor := by
  intro a ha
  simp only [blkDec, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkDec_room (c : Params) :
    ∀ a ∈ blkDec c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkDec, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp [depth, cursor, regCount]

theorem blkBump_wf : ∀ a ∈ blkBump, a.WF cursor := by
  intro a ha
  simp only [blkBump, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkBump_room : ∀ a ∈ blkBump, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkBump, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp [depth, sel, cursor, regCount]

theorem blkGeom_wf : ∀ a ∈ blkGeom, a.WF cursor := by
  intro a ha
  simp only [blkGeom, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkGeom_room : ∀ a ∈ blkGeom, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkGeom, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem blkNum_wf (c : Params) : ∀ a ∈ blkNum c, a.WF cursor := by
  intro a ha
  by_cases hup : c.up = 1 <;>
    · simp only [blkNum, hup, if_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkNum_room (c : Params) :
    ∀ a ∈ blkNum c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  by_cases hup : c.up = 1 <;>
    · simp only [blkNum, hup, if_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [depth, cursor, regCount]

theorem blkMask_wf : ∀ a ∈ blkMask, a.WF cursor := by
  intro a ha
  simp only [blkMask, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkMask_room : ∀ a ∈ blkMask, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkMask, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> simp [depth, cursor, regCount]

theorem blkRst_wf : ∀ a ∈ blkRst, a.WF cursor := by
  intro a ha
  simp only [blkRst, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkRst_room : ∀ a ∈ blkRst, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkRst, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [depth, sel, cursor, regCount]

theorem blkFAB_wf (c : Params) : ∀ a ∈ blkFAB c, a.WF cursor := by
  intro a ha
  simp only [blkFAB, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkFAB_room (c : Params) :
    ∀ a ∈ blkFAB c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkFAB, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [depth, cursor, regCount]

theorem blkAbs_wf : ∀ a ∈ blkAbs, a.WF cursor := by
  intro a ha
  simp only [blkAbs, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkAbs_room : ∀ a ∈ blkAbs, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkAbs, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  simp [depth, sel, cursor, regCount]

theorem blkUVa_wf (c : Params) : ∀ a ∈ blkUVa c, a.WF cursor := by
  intro a ha
  simp only [blkUVa, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkUVa_room (c : Params) :
    ∀ a ∈ blkUVa c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkUVa, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> simp [depth, sel, cursor, regCount]

theorem blkUVb_wf : ∀ a ∈ blkUVb, a.WF cursor := by
  intro a ha
  simp only [blkUVb, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkUVb_room : ∀ a ∈ blkUVb, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkUVb, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> simp [depth, sel, cursor, regCount]

theorem blkA_wf (c : Params) : ∀ a ∈ blkA c, a.WF cursor := by
  intro a ha
  simp only [blkA, List.mem_append] at ha
  rcases ha with h | h | h | h | h | h | h | h | h | h
  · exact blkDec_wf c a h
  · exact blkBump_wf a h
  · exact blkGeom_wf a h
  · exact blkNum_wf c a h
  · exact blkMask_wf a h
  · exact blkRst_wf a h
  · exact blkFAB_wf c a h
  · exact blkAbs_wf a h
  · exact blkUVa_wf c a h
  · exact blkUVb_wf a h

theorem blkA_room (c : Params) :
    ∀ a ∈ blkA c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkA, List.mem_append] at ha
  rcases ha with h | h | h | h | h | h | h | h | h | h
  · exact blkDec_room c a h
  · exact blkBump_room a h
  · exact blkGeom_room a h
  · exact blkNum_room c a h
  · exact blkMask_room a h
  · exact blkRst_room a h
  · exact blkFAB_room c a h
  · exact blkAbs_room a h
  · exact blkUVa_room c a h
  · exact blkUVb_room a h

theorem blkZ_wf : ∀ a ∈ blkZ, a.WF cursor := by
  intro a ha
  simp only [blkZ, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkZ_room : ∀ a ∈ blkZ, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkZ, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [depth, cursor, regCount]

theorem blkUpd_wf : ∀ a ∈ blkUpd, a.WF cursor := by
  intro a ha
  simp only [blkUpd, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkUpd_room : ∀ a ∈ blkUpd, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkUpd, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor, regCount]

theorem blkAsmA_wf (c : Params) : ∀ a ∈ blkAsmA c, a.WF cursor := by
  intro a ha
  simp only [blkAsmA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkAsmA_room (c : Params) :
    ∀ a ∈ blkAsmA c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkAsmA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [depth, cursor, regCount]

theorem blkT1_wf : ∀ a ∈ blkT1, a.WF cursor := by
  intro a ha
  simp only [blkT1, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkT1_room : ∀ a ∈ blkT1, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkT1, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  simp [depth, sel, cursor, regCount]

theorem blkT2_wf (c : Params) : ∀ a ∈ blkT2 c, a.WF cursor := by
  intro a ha
  by_cases hup : c.up = 1 <;>
    · simp only [blkT2, hup, if_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      subst ha
      exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkT2_room (c : Params) :
    ∀ a ∈ blkT2 c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  by_cases hup : c.up = 1 <;>
    · simp only [blkT2, hup, if_true, if_false, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      subst ha
      simp [depth, sel, cursor, regCount]

theorem blkT3_wf : ∀ a ∈ blkT3, a.WF cursor := by
  intro a ha
  simp only [blkT3, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkT3_room : ∀ a ∈ blkT3, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkT3, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  simp [depth, cursor, regCount]

theorem blkAcc_wf : ∀ a ∈ blkAcc, a.WF cursor := by
  intro a ha
  simp only [blkAcc, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkAcc_room : ∀ a ∈ blkAcc, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkAcc, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> simp [depth, cursor, regCount]

theorem blkB_wf (c : Params) : ∀ a ∈ blkB c, a.WF cursor := by
  intro a ha
  simp only [blkB, List.mem_append] at ha
  rcases ha with h | h | h | h | h | h | h
  · exact blkZ_wf a h
  · exact blkUpd_wf a h
  · exact blkAsmA_wf c a h
  · exact blkT1_wf a h
  · exact blkT2_wf c a h
  · exact blkT3_wf a h
  · exact blkAcc_wf a h

theorem blkB_room (c : Params) :
    ∀ a ∈ blkB c, cursor + depth a.expr ≤ regCount := by
  intro a ha
  simp only [blkB, List.mem_append] at ha
  rcases ha with h | h | h | h | h | h | h
  · exact blkZ_room a h
  · exact blkUpd_room a h
  · exact blkAsmA_room c a h
  · exact blkT1_room a h
  · exact blkT2_room c a h
  · exact blkT3_room a h
  · exact blkAcc_room a h

theorem ceBody_wf (c : Params) : ∀ i ∈ ceBody c, i.WF regCount := by
  intro i hi
  have hi' : i ∈ ceBody c := hi
  rw [ceBody] at hi'
  rcases List.mem_append.mp hi' with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; exact ⟨by simp [regCount], trivial, trivial⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor regCount (blkA c) (blkA_wf c)
      (by simp [cursor, regCount]) (blkA_room c) i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp [regCount], by simp [Operand.WF, regCount],
      by simp [Operand.WF, regCount]⟩
  · exact block_wf cursor regCount (blkB c) (blkB_wf c)
      (by simp [cursor, regCount]) (blkB_room c) i h

theorem ceProgram_wf (c : Params) : (ceProgram c).WF := by
  refine ⟨by simp [ceProgram, regCount], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ ceInit c := hi
    simp only [ceInit, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl <;>
      exact ⟨by simp [ceProgram, regCount], trivial⟩
  · exact ceBody_wf c
  · intro i hi
    have hi' : i ∈ ceEpilogue c := hi
    simp only [ceEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl <;>
      exact ⟨by simp [ceProgram, regCount],
        by simp [ceProgram, Operand.WF, regCount],
        by simp [ceProgram, Operand.WF, regCount]⟩

/-! ## §8 What each block computes

Every lemma below is stated from an *abstract* incoming state, with one
hypothesis per register the block reads and one per `u64` truncation that has
to be a no-op.  Registers the block does not write are handled by
`Straight.run_untouched` at the call site, so they never appear here.
-/

private theorem l0 : (0 : Nat) % M = 0 := by decide
private theorem l1 : (1 : Nat) % M = 1 := by decide
private theorem l2 : (2 : Nat) % M = 2 := by decide
private theorem l3 : (3 : Nat) % M = 3 := by decide
private theorem l4 : (4 : Nat) % M = 4 := by decide
private theorem l8 : (8 : Nat) % M = 8 := by decide
private theorem l9 : (9 : Nat) % M = 9 := by decide
private theorem l10 : (10 : Nat) % M = 10 := by decide
private theorem l256 : (256 : Nat) % M = 256 := by decide

/-- Machine subtraction is `Nat` subtraction when it does not underflow. -/
theorem subM {x y : Nat} (hle : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have h : x + (M - y) = M + (x - y) := by omega
  rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (show x - y < M by omega)]

theorem blkDec_spec (c : Params) (k : Nat) (t : RegState) (q rr : Nat)
    (h13 : t 13 = q)
    (ekM : k % M = k) (eR : c.R % M = c.R) (eqR : (q * c.R) % M = q * c.R)
    (esub : (k + (M - q * c.R)) % M = rr)
    (elo : c.lo % M = c.lo) (en : (c.lo + q) % M = c.lo + q)
    (eR1 : (c.R - 1) % M = c.R - 1) :
    run k t (blkDec c) 14 = rr ∧
    run k t (blkDec c) 15 = c.lo + q ∧
    run k t (blkDec c) 16 = (if rr = 0 then 1 else 0) ∧
    run k t (blkDec c) 17 = (if rr = c.R - 1 then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkDec, evalExpr, denoteOp, RegState.set, h13, ekM, eR, eqR,
      esub, elo, en, eR1]

theorem blkBump_spec (k : Nat) (t : RegState) (pk kk n first dob : Nat)
    (h2 : t 2 = pk) (h3 : t 3 = kk) (h15 : t 15 = n) (h16 : t 16 = first)
    (hdob : dob ≤ 1)
    (edob : first * (if pk * 2 ≤ n then 1 else 0) = dob)
    (epk2 : (pk * 2) % M = pk * 2) (hpkM : pk < M)
    (ekk : (kk + dob) % M = kk + dob) :
    run k t blkBump 18 = pk * 2 ∧
    run k t blkBump 19 = dob ∧
    run k t blkBump 2 = (if dob = 1 then pk * 2 else pk) ∧
    run k t blkBump 3 = kk + dob := by
  have epkM : pk % M = pk := Nat.mod_eq_of_lt hpkM
  rcases (show dob = 0 ∨ dob = 1 by omega) with h | h <;> subst h
  · have ekk' : kk % M = kk := by simpa using ekk
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkBump, evalExpr, denoteOp, RegState.set, sel, h2, h3, h15,
        h16, epk2, epkM, ekk', edob, l1, l2]
  · have ekk' : (kk + 1) % M = kk + 1 := ekk
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkBump, evalExpr, denoteOp, RegState.set, sel, h2, h3, h15,
        h16, epk2, epkM, ekk', edob, l1, l2]

/-- A product of two `0/1` indicators is the indicator of the conjunction. -/
theorem ind_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1 else 0) * (if Q then 1 else 0)) % M =
      if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, l0, l1]

theorem blkGeom_spec (k : Nat) (t : RegState) (n pk rr first : Nat)
    (h2 : t 2 = pk) (h14 : t 14 = rr) (h15 : t 15 = n) (h16 : t 16 = first)
    (hfirst : first ≤ 1) (hn1 : 1 ≤ n) (hnM : n < M)
    (hCM : n * (n - 1) < M) (hdM : 2 * rr + 1 < M) (h2rrM : 2 * rr < M)
    (hn2M : n * n < M) (hp2M : pk * pk < M) (hpkM : pk < M)
    (hnpM : n * pk < M) (hple : pk * pk ≤ n * n)
    (hVle : n * n ≤ 4 * (pk * pk)) (h4p2M : 4 * (pk * pk) < M) :
    run k t blkGeom 20 = n * (n - 1) ∧
    run k t blkGeom 21 = (if first = 1 then 2 else 2 * rr + 1) ∧
    run k t blkGeom 22 = n * n ∧
    run k t blkGeom 23 = pk * pk ∧
    run k t blkGeom 24 = n * pk ∧
    run k t blkGeom 25 = n * n - pk * pk ∧
    run k t blkGeom 26 = 4 * (pk * pk) - n * n := by
  have e1 : (n + (M - 1)) % M = n - 1 := subM hn1 hnM
  have eC : (n * (n - 1)) % M = n * (n - 1) := Nat.mod_eq_of_lt hCM
  have e2rr : (2 * rr) % M = 2 * rr := Nat.mod_eq_of_lt h2rrM
  have ed : (2 * rr + 1) % M = 2 * rr + 1 := Nat.mod_eq_of_lt hdM
  have en2 : (n * n) % M = n * n := Nat.mod_eq_of_lt hn2M
  have ep2 : (pk * pk) % M = pk * pk := Nat.mod_eq_of_lt hp2M
  have epk : pk % M = pk := Nat.mod_eq_of_lt hpkM
  have enp : (n * pk) % M = n * pk := Nat.mod_eq_of_lt hnpM
  have e4 : (4 * (pk * pk)) % M = 4 * (pk * pk) := Nat.mod_eq_of_lt h4p2M
  have eU : (n * n + (M - pk * pk)) % M = n * n - pk * pk := subM hple hn2M
  have eV : (4 * (pk * pk) + (M - n * n)) % M = 4 * (pk * pk) - n * n :=
    subM hVle h4p2M
  have eUM : (n * n - pk * pk) % M = n * n - pk * pk :=
    Nat.mod_eq_of_lt (by omega)
  have eVM : (4 * (pk * pk) - n * n) % M = 4 * (pk * pk) - n * n :=
    Nat.mod_eq_of_lt (by omega)
  rcases (show first = 0 ∨ first = 1 by omega) with h | h <;> subst h <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkGeom, evalExpr, denoteOp, RegState.set, sel, h2, h14, h15,
        h16, l1, l2, l4, e1, eC, e2rr, ed, en2, ep2, epk, enp, e4, eU, eV, eUM,
        eVM]

theorem blkNum_spec (c : Params) (k : Nat) (t : RegState) (n2 p2 np U V : Nat)
    (h22 : t 22 = n2) (h23 : t 23 = p2) (h24 : t 24 = np) (h25 : t 25 = U)
    (h26 : t 26 = V)
    (hUM : U < M) (hVM : V < M) (hn2M : n2 < M) (hp2M : p2 < M)
    (h3U : 3 * U < M) (h3V : 3 * V < M)
    (h2np : 2 * np < M) (h4np : 4 * np < M) (h8np : 8 * np < M)
    (hs1 : n2 + 4 * np < M) (hs2 : n2 + 4 * np + p2 < M)
    (h4p2 : 4 * p2 < M) (hs3 : 4 * p2 + 8 * np < M)
    (hs4 : 4 * p2 + 8 * np + n2 < M) :
    run k t (blkNum c) 27 = (if c.up = 1 then U else 3 * U) ∧
    run k t (blkNum c) 28 = (if c.up = 1 then 2 * np else n2 + 4 * np + p2) ∧
    run k t (blkNum c) 29 = (if c.up = 1 then 3 * V else V) ∧
    run k t (blkNum c) 30 =
      (if c.up = 1 then 4 * p2 + 8 * np + n2 else 4 * np) := by
  by_cases hu : c.up = 1 <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkNum, evalExpr, denoteOp, RegState.set, hu, h22, h23, h24,
        h25, h26, l3, l4, l8, Nat.mod_eq_of_lt hUM, Nat.mod_eq_of_lt hVM,
        Nat.mod_eq_of_lt hn2M, Nat.mod_eq_of_lt hp2M, Nat.mod_eq_of_lt h3U,
        Nat.mod_eq_of_lt h3V, Nat.mod_eq_of_lt h2np, Nat.mod_eq_of_lt h4np,
        Nat.mod_eq_of_lt h8np, Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt hs2,
        Nat.mod_eq_of_lt h4p2, Nat.mod_eq_of_lt hs3, Nat.mod_eq_of_lt hs4]

theorem blkMask_spec (k : Nat) (t : RegState) (rr : Nat) (h14 : t 14 = rr) :
    run k t blkMask 31 = (if 1 ≤ rr ∧ rr ≤ 8 then 1 else 0) ∧
    run k t blkMask 32 = (if rr = 9 then 1 else 0) ∧
    run k t blkMask 33 = (if rr = 10 then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [run, blkMask, evalExpr, denoteOp, RegState.set, h14, l1, l8, l9, l10,
      ind_mul]

theorem blkRst_spec (k : Nat) (t : RegState)
    (first qA rA qB rB cf numA numB : Nat)
    (h4 : t 4 = cf) (h5 : t 5 = qA) (h6 : t 6 = rA) (h7 : t 7 = qB)
    (h8 : t 8 = rB) (h16 : t 16 = first) (h27 : t 27 = numA)
    (h29 : t 29 = numB) (hfirst : first ≤ 1)
    (hqA : qA < M) (hrA : rA < M) (hqB : qB < M) (hrB : rB < M) (hcf : cf < M)
    (hnumA : numA < M) (hnumB : numB < M) :
    run k t blkRst 34 = (if first = 1 then 0 else qA) ∧
    run k t blkRst 35 = (if first = 1 then numA else rA) ∧
    run k t blkRst 36 = (if first = 1 then 0 else qB) ∧
    run k t blkRst 37 = (if first = 1 then numB else rB) ∧
    run k t blkRst 38 = (if first = 1 then 0 else cf) := by
  rcases (show first = 0 ∨ first = 1 by omega) with h | h <;> subst h <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkRst, evalExpr, denoteOp, RegState.set, sel, h4, h5, h6, h7,
        h8, h16, h27, h29, l0, l1, Nat.mod_eq_of_lt hqA, Nat.mod_eq_of_lt hrA,
        Nat.mod_eq_of_lt hqB, Nat.mod_eq_of_lt hrB, Nat.mod_eq_of_lt hcf,
        Nat.mod_eq_of_lt hnumA, Nat.mod_eq_of_lt hnumB]

/-- The `.ne` comparison, in the shape `ceRound` writes it. -/
private theorem ite_ne_zero (x : Nat) :
    (if ¬ x = 0 then 1 else 0) = if x = 0 then 0 else 1 := by
  by_cases h : x = 0 <;> simp [h]

/-- A bit times an indicator is a word. -/
private theorem mask_mul_lt {u x : Nat} (hu : u ≤ 1) :
    u * (if x = 0 then 0 else 1) < M := by
  have hM : (1 : Nat) < M := by decide
  rcases (show u = 0 ∨ u = 1 by omega) with h | h <;> subst h <;> split <;> omega

theorem blkFAB_spec (c : Params) (k : Nat) (t : RegState)
    (qA0 rA0 qB0 rB0 kk r0 FA FB a1 ge cb : Nat)
    (h3 : t 3 = kk) (h10 : t 10 = r0) (h34 : t 34 = qA0) (h35 : t 35 = rA0)
    (h36 : t 36 = qB0) (h37 : t 37 = rB0) (hup : c.up ≤ 1)
    (eFA : qA0 + c.up * (if rA0 = 0 then 0 else 1) = FA) (hFA : FA < M)
    (eFB : qB0 + (1 - c.up) * (if rB0 = 0 then 0 else 1) = FB) (hFB : FB < M)
    (ea1 : (kk + 1) * r0 = a1) (ha1 : a1 < M) (hkk1 : kk + 1 < M)
    (ege : (if a1 ≤ FB then 1 else 0) = ge)
    (ecb : ge ^^^ c.up = cb) (hcb : cb < M) :
    run k t (blkFAB c) 39 = FA ∧ run k t (blkFAB c) 40 = FB ∧
    run k t (blkFAB c) 41 = a1 ∧ run k t (blkFAB c) 42 = ge ∧
    run k t (blkFAB c) 43 = cb := by
  have eup : c.up % M = c.up := Nat.mod_eq_of_lt (by have := M_pos; omega)
  have eup' : (1 - c.up) % M = 1 - c.up :=
    Nat.mod_eq_of_lt (by have := M_pos; omega)
  have em1 : (c.up * (if rA0 = 0 then 0 else 1)) % M =
      c.up * (if rA0 = 0 then 0 else 1) := Nat.mod_eq_of_lt (mask_mul_lt hup)
  have em2 : ((1 - c.up) * (if rB0 = 0 then 0 else 1)) % M =
      (1 - c.up) * (if rB0 = 0 then 0 else 1) :=
    Nat.mod_eq_of_lt (mask_mul_lt (show 1 - c.up ≤ 1 by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkFAB, evalExpr, denoteOp, RegState.set, h3, h10, h34, h35, h36,
      h37, l0, l1, eup, eup', em1, em2, ite_ne_zero, eFA, eFB, ea1, ege, ecb,
      Nat.mod_eq_of_lt hFA, Nat.mod_eq_of_lt hFB, Nat.mod_eq_of_lt hkk1,
      Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hcb]

theorem blkUVa_spec (c : Params) (k : Nat) (t : RegState)
    (act isq isf rA0 kk r0 FA C denA uA : Nat)
    (h3 : t 3 = kk) (h10 : t 10 = r0) (h20 : t 20 = C) (h28 : t 28 = denA)
    (h31 : t 31 = act) (h32 : t 32 = isq) (h33 : t 33 = isf)
    (h35 : t 35 = rA0) (h39 : t 39 = FA)
    (hact : act ≤ 1) (hisq : isq ≤ 1) (hisf : isf ≤ 1) (hup : c.up ≤ 1)
    (euA : (if act = 1 then rA0 * 256
            else if isq = 1 then c.lfx
            else if isf = 1 then kk * r0 + FA + c.up * (C - 1) else 0) = uA)
    (huA : uA < M)
    (erA256 : rA0 * 256 < M) (hlfx : c.lfx < M) (hC1 : 1 ≤ C) (hCM : C < M)
    (hkr : kk * r0 < M) (hkrFA : kk * r0 + FA < M)
    (hfull : kk * r0 + FA + c.up * (C - 1) < M)
    (hupC : c.up * (C - 1) < M) (hdenA : denA < M) :
    run k t (blkUVa c) 44 = uA ∧
    run k t (blkUVa c) 45 = (if act = 1 then denA else C) := by
  have eup : c.up % M = c.up := Nat.mod_eq_of_lt (by have := M_pos; omega)
  have eC1 : (C + (M - 1)) % M = C - 1 := subM hC1 hCM
  rcases (show act = 0 ∨ act = 1 by omega) with ha | ha <;>
    rcases (show isq = 0 ∨ isq = 1 by omega) with hq | hq <;>
      rcases (show isf = 0 ∨ isf = 1 by omega) with hf | hf <;>
        subst ha <;> subst hq <;> subst hf <;>
          refine ⟨?_, ?_⟩ <;>
            simp [run, blkUVa, evalExpr, denoteOp, RegState.set, sel, h3, h10,
              h20, h28, h31, h32, h33, h35, h39, l0, l1, l256, eup, eC1,
              ← euA, Nat.mod_eq_of_lt erA256, Nat.mod_eq_of_lt hlfx,
              Nat.mod_eq_of_lt hkr, Nat.mod_eq_of_lt hkrFA,
              Nat.mod_eq_of_lt hfull, Nat.mod_eq_of_lt hupC,
              Nat.mod_eq_of_lt hdenA, Nat.mod_eq_of_lt hCM]

theorem blkAbs_spec (k : Nat) (t : RegState) (FB a1 ge ad : Nat)
    (h40 : t 40 = FB) (h41 : t 41 = a1) (h42 : t 42 = ge) (hge : ge ≤ 1)
    (hge0 : ge = 0 → FB ≤ a1) (hge1 : ge = 1 → a1 ≤ FB)
    (ead : (if ge = 1 then FB - a1 else a1 - FB) = ad) (hadM : ad < M)
    (hFB : FB < M) (ha1 : a1 < M) :
    run k t blkAbs 66 = ad := by
  rcases (show ge = 0 ∨ ge = 1 by omega) with hg | hg <;> subst hg
  · have hle := hge0 rfl
    have e : (a1 - FB) % M = a1 - FB := Nat.mod_eq_of_lt (by omega)
    simp [run, blkAbs, evalExpr, denoteOp, RegState.set, sel, h40, h41, h42,
      l1, subM hle ha1, ← ead, e]
  · have hle := hge1 rfl
    have e : (FB - a1) % M = FB - a1 := Nat.mod_eq_of_lt (by omega)
    simp [run, blkAbs, evalExpr, denoteOp, RegState.set, sel, h40, h41, h42,
      l1, subM hle hFB, ← ead, e]

theorem blkUVb_spec (k : Nat) (t : RegState)
    (act isf cb rB0 ad C denB uB : Nat)
    (h20 : t 20 = C) (h30 : t 30 = denB) (h31 : t 31 = act) (h33 : t 33 = isf)
    (h37 : t 37 = rB0) (h43 : t 43 = cb) (h66 : t 66 = ad)
    (hact : act ≤ 1) (hisf : isf ≤ 1) (hcb : cb ≤ 1)
    (euB : (if act = 1 then rB0 * 256
            else if isf = 1 then ad + cb * (C - 1) else 0) = uB)
    (huB : uB < M)
    (erB256 : rB0 * 256 < M) (hC1 : 1 ≤ C) (hCM : C < M) (hadM : ad < M)
    (hcbC : cb * (C - 1) < M) (hdenB : denB < M)
    (hsum : ad + cb * (C - 1) < M) :
    run k t blkUVb 46 = uB ∧
    run k t blkUVb 47 = (if act = 1 then denB else C) := by
  have eC1 : (C + (M - 1)) % M = C - 1 := subM hC1 hCM
  have ecb : cb % M = cb := Nat.mod_eq_of_lt (by have := M_pos; omega)
  rcases (show act = 0 ∨ act = 1 by omega) with ha | ha <;> subst ha <;>
    rcases (show isf = 0 ∨ isf = 1 by omega) with hf | hf <;> subst hf <;>
      refine ⟨?_, ?_⟩ <;>
        simp [run, blkUVb, evalExpr, denoteOp, RegState.set, sel, h20, h30,
          h31, h33, h37, h43, h66, l0, l1, l256, eC1, ecb,
          ← euB, Nat.mod_eq_of_lt erB256, Nat.mod_eq_of_lt hadM,
          Nat.mod_eq_of_lt hcbC, Nat.mod_eq_of_lt hdenB, Nat.mod_eq_of_lt hCM,
          Nat.mod_eq_of_lt hsum]

theorem blkZ_spec (k : Nat) (t : RegState)
    (uA vA uB vB wA wB n dq d cf0 hit cf : Nat)
    (h15 : t 15 = n) (h21 : t 21 = d) (h38 : t 38 = cf0) (h44 : t 44 = uA)
    (h45 : t 45 = vA) (h46 : t 46 = uB) (h47 : t 47 = vB) (h48 : t 48 = wA)
    (h49 : t 49 = wB) (h50 : t 50 = dq)
    (hwAvA : wA * vA ≤ uA) (huA : uA < M) (hwAvAM : wA * vA < M)
    (hwBvB : wB * vB ≤ uB) (huB : uB < M) (hwBvBM : wB * vB < M)
    (hdqd : dq * d ≤ n) (hnM : n < M) (hdqdM : dq * d < M)
    (ehit : (if n - dq * d = 0 then 1 else 0) = hit)
    (ecf : cf0 ||| hit = cf) (hcfM : cf < M) :
    run k t blkZ 51 = uA - wA * vA ∧
    run k t blkZ 52 = uB - wB * vB ∧
    run k t blkZ 53 = n - dq * d ∧
    run k t blkZ 54 = hit ∧
    run k t blkZ 4 = cf := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkZ, evalExpr, denoteOp, RegState.set, h15, h21, h38, h44, h45,
      h46, h47, h48, h49, h50, l0, Nat.mod_eq_of_lt hwAvAM,
      Nat.mod_eq_of_lt hwBvBM, Nat.mod_eq_of_lt hdqdM, subM hwAvA huA,
      subM hwBvB huB, subM hdqd hnM, ehit, ecf, Nat.mod_eq_of_lt hcfM]

theorem blkUpd_spec (k : Nat) (t : RegState)
    (act isq isf qA0 rA0 qB0 rB0 wA wB zA zB q0 r0 fA fB : Nat)
    (h9 : t 9 = q0) (h10 : t 10 = r0) (h11 : t 11 = fA) (h12 : t 12 = fB)
    (h31 : t 31 = act) (h32 : t 32 = isq) (h33 : t 33 = isf)
    (h34 : t 34 = qA0) (h35 : t 35 = rA0) (h36 : t 36 = qB0) (h37 : t 37 = rB0)
    (h48 : t 48 = wA) (h49 : t 49 = wB) (h51 : t 51 = zA) (h52 : t 52 = zB)
    (hact : act ≤ 1) (hisq : isq ≤ 1) (hisf : isf ≤ 1)
    (eqA : act = 1 → (qA0 * 256 + wA) % M = qA0 * 256 + wA)
    (eqA2 : act = 1 → (qA0 * 256) % M = qA0 * 256)
    (eqB : act = 1 → (qB0 * 256 + wB) % M = qB0 * 256 + wB)
    (eqB2 : act = 1 → (qB0 * 256) % M = qB0 * 256)
    (hqA0 : qA0 < M) (hrA0 : rA0 < M) (hqB0 : qB0 < M) (hrB0 : rB0 < M)
    (hzA : zA < M) (hzB : zB < M) (hwA : wA < M) (hwB : wB < M)
    (hq0 : q0 < M) (hr0 : r0 < M) (hfA : fA < M) (hfB : fB < M) :
    run k t blkUpd 5 = (if act = 1 then qA0 * 256 + wA else qA0) ∧
    run k t blkUpd 6 = (if act = 1 then zA else rA0) ∧
    run k t blkUpd 7 = (if act = 1 then qB0 * 256 + wB else qB0) ∧
    run k t blkUpd 8 = (if act = 1 then zB else rB0) ∧
    run k t blkUpd 9 = (if isq = 1 then wA else q0) ∧
    run k t blkUpd 10 = (if isq = 1 then zA else r0) ∧
    run k t blkUpd 11 = (if isf = 1 then wA else fA) ∧
    run k t blkUpd 12 = (if isf = 1 then wB else fB) := by
  rcases (show act = 0 ∨ act = 1 by omega) with ha | ha <;>
    rcases (show isq = 0 ∨ isq = 1 by omega) with hq | hq <;>
      rcases (show isf = 0 ∨ isf = 1 by omega) with hf | hf <;>
        subst ha <;> subst hq <;> subst hf <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [run, blkUpd, evalExpr, denoteOp, RegState.set, sel, h9, h10,
              h11, h12, h31, h32, h33, h34, h35, h36, h37, h48, h49, h51, h52,
              l1, l256, eqA, eqA2, eqB, eqB2, Nat.mod_eq_of_lt hqA0,
              Nat.mod_eq_of_lt hrA0, Nat.mod_eq_of_lt hqB0,
              Nat.mod_eq_of_lt hrB0, Nat.mod_eq_of_lt hzA,
              Nat.mod_eq_of_lt hzB, Nat.mod_eq_of_lt hwA,
              Nat.mod_eq_of_lt hwB, Nat.mod_eq_of_lt hq0,
              Nat.mod_eq_of_lt hr0, Nat.mod_eq_of_lt hfA, Nat.mod_eq_of_lt hfB]

theorem blkAsmA_spec (c : Params) (k : Nat) (t : RegState)
    (kk qA rA qB rB q0 r0 fA FB2 a1b ge2 tA base : Nat)
    (h3 : t 3 = kk) (h5 : t 5 = qA) (h6 : t 6 = rA) (h7 : t 7 = qB)
    (h8 : t 8 = rB) (h9 : t 9 = q0) (h10 : t 10 = r0) (h11 : t 11 = fA)
    (hup : c.up ≤ 1)
    (hFA2 : qA + c.up * (if rA = 0 then 0 else 1) < M)
    (eFB2 : qB + (1 - c.up) * (if rB = 0 then 0 else 1) = FB2) (hFB2 : FB2 < M)
    (ea1b : (kk + 1) * r0 = a1b) (ha1b : a1b < M) (hkk1 : kk + 1 < M)
    (ege2 : (if a1b ≤ FB2 then 1 else 0) = ge2)
    (etA : kk * q0 + fA = tA) (htA : tA < M) (hkq0 : kk * q0 < M)
    (ebase : (kk + 1) * q0 = base) (hbase : base < M) (hqA : qA < M) :
    run k t (blkAsmA c) 56 = FB2 ∧ run k t (blkAsmA c) 57 = a1b ∧
    run k t (blkAsmA c) 58 = ge2 ∧ run k t (blkAsmA c) 59 = tA ∧
    run k t (blkAsmA c) 60 = base := by
  have eup : c.up % M = c.up := Nat.mod_eq_of_lt (by have := M_pos; omega)
  have eup' : (1 - c.up) % M = 1 - c.up :=
    Nat.mod_eq_of_lt (by have := M_pos; omega)
  have em1 : (c.up * (if rA = 0 then 0 else 1)) % M =
      c.up * (if rA = 0 then 0 else 1) := Nat.mod_eq_of_lt (mask_mul_lt hup)
  have em2 : ((1 - c.up) * (if rB = 0 then 0 else 1)) % M =
      (1 - c.up) * (if rB = 0 then 0 else 1) :=
    Nat.mod_eq_of_lt (mask_mul_lt (show 1 - c.up ≤ 1 by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkAsmA, evalExpr, denoteOp, RegState.set, h3, h5, h6, h7, h8,
      h9, h10, h11, l0, l1, eup, eup', em1, em2, ite_ne_zero, eFB2, ea1b, ege2,
      etA, ebase, Nat.mod_eq_of_lt hFB2, Nat.mod_eq_of_lt ha1b,
      Nat.mod_eq_of_lt hkk1, Nat.mod_eq_of_lt htA, Nat.mod_eq_of_lt hkq0,
      Nat.mod_eq_of_lt hbase]

theorem blkT1_spec (k : Nat) (t : RegState) (fB tA base ge2 tB : Nat)
    (h12 : t 12 = fB) (h58 : t 58 = ge2) (h59 : t 59 = tA) (h60 : t 60 = base)
    (hge2 : ge2 ≤ 1)
    (etB : (if ge2 = 1 then (if fB ≤ base then base - fB else tA)
            else base + fB) = tB)
    (htB : tB < M) (hbfB : base + fB < M) (hfB : fB < M) (htA : tA < M)
    (hbase : base < M) :
    run k t blkT1 61 = tB := by
  have etBM : tB % M = tB := Nat.mod_eq_of_lt htB
  rcases (show ge2 = 0 ∨ ge2 = 1 by omega) with hg | hg <;> subst hg
  · have e : base + fB = tB := by simpa using etB
    simp [run, blkT1, evalExpr, denoteOp, RegState.set, sel, h12, h58, h59,
      h60, l1, e, etBM]
  · by_cases hle : fB ≤ base
    · have e : base - fB = tB := by simpa [hle] using etB
      simp [run, blkT1, evalExpr, denoteOp, RegState.set, sel, h12, h58, h59,
        h60, l1, hle, subM hle hbase, e, etBM]
    · have e : tA = tB := by simpa [hle] using etB
      simp [run, blkT1, evalExpr, denoteOp, RegState.set, sel, h12, h58, h59,
        h60, l1, hle, e, etBM]

theorem blkT2_spec (c : Params) (k : Nat) (t : RegState) (tA tB tt : Nat)
    (h59 : t 59 = tA) (h61 : t 61 = tB)
    (et : (if c.up = 1 then min tA tB else max tA tB) = tt) (htt : tt < M)
    (htA : tA < M) (htB : tB < M) :
    run k t (blkT2 c) 62 = tt := by
  have emin : min tA tB = if tA ≤ tB then tA else tB := Nat.min_def
  have emax : max tA tB = if tA ≤ tB then tB else tA := Nat.max_def
  rw [emin, emax] at et
  by_cases hu : c.up = 1
  · rw [if_pos hu] at et
    by_cases hab : tA ≤ tB
    · rw [if_pos hab] at et
      subst et
      simp [run, blkT2, evalExpr, denoteOp, RegState.set, sel, h59, h61, l1,
        hu, hab, Nat.mod_eq_of_lt htA]
    · rw [if_neg hab] at et
      subst et
      simp [run, blkT2, evalExpr, denoteOp, RegState.set, sel, h59, h61, l1,
        hu, hab, Nat.mod_eq_of_lt htB]
  · rw [if_neg hu] at et
    by_cases hab : tA ≤ tB
    · rw [if_pos hab] at et
      subst et
      simp [run, blkT2, evalExpr, denoteOp, RegState.set, sel, h59, h61, l1,
        hu, hab, Nat.mod_eq_of_lt htB]
    · rw [if_neg hab] at et
      subst et
      simp [run, blkT2, evalExpr, denoteOp, RegState.set, sel, h59, h61, l1,
        hu, hab, Nat.mod_eq_of_lt htA]

theorem blkT3_spec (k : Nat) (t : RegState) (cf last tt ct : Nat)
    (h4 : t 4 = cf) (h17 : t 17 = last) (h62 : t 62 = tt) (hlast : last ≤ 1)
    (ect : last * (if cf = 0 then 1 else 0) * tt = ct) (hct : ct < M)
    (htt : tt < M) :
    run k t blkT3 63 = ct := by
  have hM1 : (1 : Nat) < M := by decide
  have hmask : last * (if cf = 0 then 1 else 0) ≤ 1 := by
    rcases (show last = 0 ∨ last = 1 by omega) with h | h <;> subst h <;>
      split <;> omega
  have emask : (last * (if cf = 0 then 1 else 0)) % M =
      last * (if cf = 0 then 1 else 0) := Nat.mod_eq_of_lt (by omega)
  simp [run, blkT3, evalExpr, denoteOp, RegState.set, h4, h17, h62, l0, emask,
    ect, Nat.mod_eq_of_lt hct]

theorem blkAcc_spec (k : Nat) (t : RegState) (acc ok ct : Nat)
    (h0 : t 0 = acc) (h1 : t 1 = ok) (h63 : t 63 = ct)
    (hacc : acc < M) (hok : ok ≤ 1) (hct : ct < M) :
    run k t blkAcc 1 = (if acc + ct < M then ok else 0) ∧
    run k t blkAcc 0 = (acc + ct) % M := by
  have hM : 1 < M := by decide
  have eok : ok % M = ok := Nat.mod_eq_of_lt (by omega)
  by_cases hw : acc + ct < M
  · have ege : acc ≤ (acc + ct) % M := by rw [Nat.mod_eq_of_lt hw]; omega
    refine ⟨?_, ?_⟩ <;>
      simp [run, blkAcc, evalExpr, denoteOp, RegState.set, h0, h1, h63, eok,
        ege, hw]
  · have h3 : (acc + ct) % M = acc + ct - M := by
      have e1 : (acc + ct - M) % M = acc + ct - M := Nat.mod_eq_of_lt (by omega)
      have e2 := Nat.add_mod_left M (acc + ct - M)
      rw [show M + (acc + ct - M) = acc + ct by omega] at e2
      omega
    have ege : ¬ (acc ≤ (acc + ct) % M) := by rw [h3]; omega
    refine ⟨?_, ?_⟩ <;>
      simp [run, blkAcc, evalExpr, denoteOp, RegState.set, h0, h1, h63, eok,
        ege, hw]

/-! ## §9 The geometry of one candidate

The four fixed-point operands are determined by `n` and by the dyadic `pk`.
Every size fact the round needs follows from `0 < pk ≤ n < 2·pk` and three
products, which is why this lemma exists: it turns the only non-linear step of
the development into three `Nat.mul_le_mul` applications, after which `omega`
finishes.
-/

/-- The numerator of the first fixed-point division. -/
def numAOf (c : Params) (n pk : Nat) : Nat :=
  if c.up = 1 then n * n - pk * pk else 3 * (n * n - pk * pk)

/-- The denominator of the first fixed-point division. -/
def denAOf (c : Params) (n pk : Nat) : Nat :=
  if c.up = 1 then 2 * (n * pk) else n * n + 4 * (n * pk) + pk * pk

/-- The numerator of the second fixed-point division. -/
def numBOf (c : Params) (n pk : Nat) : Nat :=
  if c.up = 1 then 3 * (4 * (pk * pk) - n * n) else 4 * (pk * pk) - n * n

/-- The denominator of the second fixed-point division. -/
def denBOf (c : Params) (n pk : Nat) : Nat :=
  if c.up = 1 then 4 * (pk * pk) + 8 * (n * pk) + n * n else 4 * (n * pk)

/-- The three products the geometry needs, and nothing else. -/
theorem geom_products {n pk : Nat} (hpk : 0 < pk) (h1 : pk ≤ n)
    (h2 : n < 2 * pk) :
    pk * pk ≤ n * pk ∧ n * pk ≤ n * n ∧ n * n < 2 * (n * pk) ∧
      n * pk < 2 * (pk * pk) ∧ 0 < pk * pk := by
  refine ⟨Nat.mul_le_mul_right pk h1, Nat.mul_le_mul_left n h1, ?_, ?_,
    Nat.mul_pos hpk hpk⟩
  · have : n * n < 2 * pk * n := (Nat.mul_lt_mul_right (by omega : 0 < n)).mpr h2
    have e : 2 * pk * n = 2 * (n * pk) := by
      rw [Nat.mul_assoc, Nat.mul_comm pk n]
    omega
  · have : n * pk < 2 * pk * pk := (Nat.mul_lt_mul_right hpk).mpr h2
    have e : 2 * pk * pk = 2 * (pk * pk) := Nat.mul_assoc _ _ _
    omega

/-- **Every size fact the round needs about the four operands.** -/
theorem geom_facts (c : Params) {n pk : Nat} (hup : c.up ≤ 1) (hpk : 0 < pk)
    (h1 : pk ≤ n) (h2 : n < 2 * pk) :
    0 < denAOf c n pk ∧ 0 < denBOf c n pk ∧
    numAOf c n pk < denAOf c n pk ∧ numBOf c n pk < denBOf c n pk ∧
    4 * numAOf c n pk ≤ 3 * denAOf c n pk ∧
    4 * numBOf c n pk ≤ 3 * denBOf c n pk ∧
    denAOf c n pk ≤ 13 * (n * n) ∧ denBOf c n pk ≤ 13 * (n * n) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := geom_products hpk h1 h2
  by_cases hu : c.up = 1 <;>
    simp only [numAOf, denAOf, numBOf, denBOf, hu, if_true, if_false] <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩

/-! ### What the carried division state is worth -/

/-- The quotient after `i` steps, bounded by the `3/4` ratio of the operands. -/
theorem sdRun_fst_bound {D N i q r : Nat} (hD : 0 < D) (h43 : 4 * N ≤ 3 * D)
    (h : (q, r) = sdRun D i (0, N)) : 4 * q ≤ 3 * 256 ^ i := by
  have hrepr := sdRun_repr D i 0 N
  rw [← h] at hrepr
  have hq : q * D + r = N * 256 ^ i := by simpa using hrepr
  have hle : 4 * (q * D) ≤ 4 * (N * 256 ^ i) := by omega
  have e1 : 4 * (N * 256 ^ i) = (4 * N) * 256 ^ i := by
    rw [Nat.mul_assoc]
  have e2 : (3 * D) * 256 ^ i = (3 * 256 ^ i) * D := by
    rw [Nat.mul_assoc, Nat.mul_comm D (256 ^ i), ← Nat.mul_assoc]
  have h2 : (4 * N) * 256 ^ i ≤ (3 * D) * 256 ^ i :=
    Nat.mul_le_mul_right _ h43
  have h3 : (4 * q) * D ≤ (3 * 256 ^ i) * D := by
    have : 4 * (q * D) = (4 * q) * D := by rw [Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right h3 hD

/-- The remainder after any number of steps is a genuine remainder. -/
theorem sdRun_snd_bound {D N i q r : Nat} (hD : 0 < D) (hN : N < D)
    (h : (q, r) = sdRun D i (0, N)) : r < D := by
  have := sdRun_snd_lt D hD i 0 N hN
  rw [← h] at this
  simpa using this

/-! ## §10 The state invariant -/

/--
The state invariant, **at entry to round `k`**.

`pkLe`/`candLe`/`bumpRnd` are the dyadic part: `pk` may lag the candidate by at
most a factor of two, and it is allowed to be exactly half only at the first
round of a block, which is the only round at which the doubling can fire.
`divA`/`divB` pin the carried division state to `sdRun` exactly, which is what
makes both the word-safety bounds and the block theorem available.
-/
structure Inv (c : Params) (k : Nat) (s : RegState) : Prop where
  /-- Every register holds a word. -/
  word : ∀ i, s i < M
  /-- The no-wrap flag is a bit. -/
  okLe : s 1 ≤ 1
  /-- The composite-witness flag is a bit. -/
  cfLe : s 4 ≤ 1
  /-- `pk = 2^kk`. -/
  pkPow : s 2 = 2 ^ s 3
  /-- The exponent is small. -/
  kkLe : s 3 ≤ 24
  /-- `pk ≤ n`. -/
  pkLe : s 2 ≤ cand c k
  /-- `n ≤ 2·pk`. -/
  candLe : cand c k ≤ 2 * s 2
  /-- `n = 2·pk` only at a block's first round. -/
  bumpRnd : cand c k = 2 * s 2 → rnd c k = 0
  /-- The fixed-point `log 2` quotient is small. -/
  q0Lt : s 9 < 2 ^ 36
  /-- The fixed-point `log 2` remainder is small. -/
  r0Lt : s 10 < 2 ^ 50
  /-- The first finalisation quotient is small. -/
  fALt : s 11 < 2 ^ 36
  /-- The second finalisation quotient is small. -/
  fBLt : s 12 < 2 ^ 36
  /-- The first carried division is exactly `sdRun`. -/
  divA : rnd c k ≠ 0 →
    (s 5, s 6) = sdRun (denAOf c (cand c k) (s 2)) (min (rnd c k - 1) 8)
      (0, numAOf c (cand c k) (s 2))
  /-- The second carried division is exactly `sdRun`. -/
  divB : rnd c k ≠ 0 →
    (s 7, s 8) = sdRun (denBOf c (cand c k) (s 2)) (min (rnd c k - 1) 8)
      (0, numBOf c (cand c k) (s 2))

/-! ### Frames -/

/-- A register no assignment of the block writes keeps its value.  The side
condition only inspects the `dest` fields, which are literals, so `decide`
discharges it at every concrete block. -/
theorem run_frame (k : Nat) (as : List Assign) (j : Nat) (t : RegState)
    (h : as.all (fun a => a.dest != j) = true) : run k t as j = t j := by
  refine run_untouched k as j ?_ t
  intro a ha
  have := List.all_eq_true.mp h a ha
  simpa using this

/-! ## §11 Staged evaluation of the body -/

/-- After index decoding and the whole division-free prefix. -/
def stA (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (idxStep c.R k s) (blkA c)

/-- After the three data divisions. -/
def stW (c : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 50 15 21 (divStep 49 46 47 (divStep 48 44 45 (stA c k s)))

theorem ceRun_eq (c : Params) (k : Nat) (s : RegState) :
    ceRun c k s = run k (stW c k s) (blkB c) := rfl

/-! ## §12 One round, under the invariant

`ceRun_spec` is the load-bearing statement: at an index the loop actually
visits, and in a state satisfying the invariant, all three data divisors are
nonzero, the thirteen carried registers move by exactly `ceRound`, and the
invariant advances to the next index.
-/

/-- `n < 2²⁵` bounds `n²`. -/
private theorem sq_bound {n : Nat} (h : n < 2 ^ 25) : n * n < 2 ^ 50 := by
  have h1 : n * n ≤ (2 ^ 25 - 1) * (2 ^ 25 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 25 - 1) * (2 ^ 25 - 1) < 2 ^ 50 := by decide
  omega

/-- The next index decodes to the same candidate, one round later. -/
private theorem idx_next_lt {R q rr : Nat} (hR : 0 < R) (h : rr + 1 < R) :
    (q * R + rr + 1) / R = q ∧ (q * R + rr + 1) % R = rr + 1 := by
  have he : q * R + rr + 1 = (rr + 1) + R * q := by
    rw [Nat.mul_comm q R]; omega
  rw [he, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt h, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  exact ⟨rfl, rfl⟩

/-- The next index opens the next block. -/
private theorem idx_next_eq {R q rr : Nat} (hR : 0 < R) (h : rr + 1 = R) :
    (q * R + rr + 1) / R = q + 1 ∧ (q * R + rr + 1) % R = 0 := by
  have he : q * R + rr + 1 = 0 + R * (q + 1) := by
    have hm : R * (q + 1) = R * q + R := Nat.mul_succ R q
    have hc : R * q = q * R := Nat.mul_comm _ _
    omega
  rw [he, Nat.add_mul_div_left _ _ hR, Nat.add_mul_mod_self_left]
  simp

/-- `256 ^ i ≤ 2 ^ (8·i)`, in the two shapes the word bounds need. -/
private theorem pow256_le8 {i : Nat} (h : i ≤ 8) : (256 : Nat) ^ i ≤ 2 ^ 64 := by
  have h1 : (256 : Nat) ^ i ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
  have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  omega

private theorem pow256_le7 {i : Nat} (h : i ≤ 7) : (256 : Nat) ^ i ≤ 2 ^ 56 := by
  have h1 : (256 : Nat) ^ i ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) h
  have h2 : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
  omega

/-- A register no later block writes keeps its value. -/
private theorem frame_of (k : Nat) (u w : RegState) (as : List Assign) (j : Nat)
    (hw : w = run k u as) (h : as.all (fun a => a.dest != j) = true) :
    w j = u j := by
  rw [hw]; exact run_frame k as j u h

/-- `ceRound` with every binder named, so that its thirteen output fields are
directly comparable with the registers the body leaves. -/
theorem ceRound_mk (c : Params) (idx : Nat) (v : Vals)
    (q rr n first last pk2 dob pk kk C d n2 p2 np U V numA denA numB denB
      act isq isf qA0 rA0 qB0 rB0 cf0 FA FB a1 ge cb uA vA uB vB wA zA wB zB
      cf qA rA qB rB q0 r0 fA fB FB2 a1b ge2 tA base tB tv ct : Nat)
    (e1 : q = idx / c.R) (e2 : rr = idx % c.R) (e3 : n = c.lo + q)
    (e4 : first = if rr = 0 then 1 else 0)
    (e5 : last = if rr = c.R - 1 then 1 else 0)
    (e6 : pk2 = v.pk * 2)
    (e7 : dob = first * (if pk2 ≤ n then 1 else 0))
    (e8 : pk = if dob = 1 then pk2 else v.pk)
    (e9 : kk = v.kk + dob)
    (e10 : C = n * (n - 1))
    (e11 : d = if rr = 0 then 2 else 2 * rr + 1)
    (e12 : n2 = n * n) (e13 : p2 = pk * pk) (e14 : np = n * pk)
    (e15 : U = n2 - p2) (e16 : V = 4 * p2 - n2)
    (e17 : numA = if c.up = 1 then U else 3 * U)
    (e18 : denA = if c.up = 1 then 2 * np else n2 + 4 * np + p2)
    (e19 : numB = if c.up = 1 then 3 * V else V)
    (e20 : denB = if c.up = 1 then 4 * p2 + 8 * np + n2 else 4 * np)
    (e21 : act = if 1 ≤ rr ∧ rr ≤ 8 then 1 else 0)
    (e22 : isq = if rr = 9 then 1 else 0)
    (e23 : isf = if rr = 10 then 1 else 0)
    (e24 : qA0 = if rr = 0 then 0 else v.qA)
    (e25 : rA0 = if rr = 0 then numA else v.rA)
    (e26 : qB0 = if rr = 0 then 0 else v.qB)
    (e27 : rB0 = if rr = 0 then numB else v.rB)
    (e28 : cf0 = if rr = 0 then 0 else v.cf)
    (e29 : FA = qA0 + c.up * (if rA0 = 0 then 0 else 1))
    (e30 : FB = qB0 + (1 - c.up) * (if rB0 = 0 then 0 else 1))
    (e31 : a1 = (kk + 1) * v.r0)
    (e32 : ge = if a1 ≤ FB then 1 else 0)
    (e33 : cb = ge ^^^ c.up)
    (e34 : uA = if act = 1 then rA0 * 256
                else if isq = 1 then c.lfx
                else if isf = 1 then kk * v.r0 + FA + c.up * (C - 1) else 0)
    (e35 : vA = if act = 1 then denA else C)
    (e36 : uB = if act = 1 then rB0 * 256
                else if isf = 1 then (if ge = 1 then FB - a1 else a1 - FB)
                                      + cb * (C - 1) else 0)
    (e37 : vB = if act = 1 then denB else C)
    (e38 : wA = uA / vA) (e39 : zA = uA % vA)
    (e40 : wB = uB / vB) (e41 : zB = uB % vB)
    (e42 : cf = cf0 ||| (if n % d = 0 then 1 else 0))
    (e43 : qA = if act = 1 then qA0 * 256 + wA else qA0)
    (e44 : rA = if act = 1 then zA else rA0)
    (e45 : qB = if act = 1 then qB0 * 256 + wB else qB0)
    (e46 : rB = if act = 1 then zB else rB0)
    (e47 : q0 = if isq = 1 then wA else v.q0)
    (e48 : r0 = if isq = 1 then zA else v.r0)
    (e49 : fA = if isf = 1 then wA else v.fA)
    (e50 : fB = if isf = 1 then wB else v.fB)
    (e51 : FB2 = qB + (1 - c.up) * (if rB = 0 then 0 else 1))
    (e52 : a1b = (kk + 1) * r0)
    (e53 : ge2 = if a1b ≤ FB2 then 1 else 0)
    (e54 : tA = kk * q0 + fA)
    (e55 : base = (kk + 1) * q0)
    (e56 : tB = if ge2 = 1 then (if fB ≤ base then base - fB else tA)
                else base + fB)
    (e57 : tv = if c.up = 1 then min tA tB else max tA tB)
    (e58 : ct = last * (if cf = 0 then 1 else 0) * tv) :
    ceRound c idx v =
      { acc := (v.acc + ct) % M, ok := if v.acc + ct < M then v.ok else 0,
        pk := pk, kk := kk, cf := cf, qA := qA, rA := rA, qB := qB, rB := rB,
        q0 := q0, r0 := r0, fA := fA, fB := fB } := by
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20
    e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 e32 e33 e34 e35 e36 e37 e38 e39
    e40 e41 e42 e43 e44 e45 e46 e47 e48 e49 e50 e51 e52 e53 e54 e55 e56 e57 e58
  rfl

theorem ceRun_spec (c : Params) (hP : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) {s : RegState} (hs : Inv c k s) :
    stA c k s 45 ≠ 0 ∧ stA c k s 47 ≠ 0 ∧ stA c k s 21 ≠ 0 ∧
      valsOf (ceRun c k s) = ceRound c k (valsOf s) ∧
        Inv c (k + 1) (ceRun c k s) := by
  sorry

/-! ## §13 The body is defined, and agrees with `ceRun` below the cursor -/

private theorem regSet_ne (u : RegState) (i v j : Nat) (h : j ≠ i) :
    (u.set i v) j = u j := by simp [RegState.set, h]

private theorem divStep_ne (dest a b j : Nat) (t : RegState) (h : j ≠ dest) :
    divStep dest a b t j = t j := by simp [divStep, RegState.set, h]

private theorem divStep_congr (dest a b : Nat) (ha : a < cursor)
    (hb : b < cursor) {u t : RegState} (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divStep dest a b u) (divStep dest a b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divStep, RegState.set, hag a ha, hag b hb]
  · rw [divStep_ne _ _ _ _ _ hjd, divStep_ne _ _ _ _ _ hjd]
    exact hag j hj

private theorem udivStep_denote (k dest a b : Nat) (u : RegState)
    (hne : u b ≠ 0) :
    denoteInstrs k u [Instr.binop dest Op.udiv (.reg a) (.reg b)] =
      some (divStep dest a b u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divStep, hne]

private theorem blockStep_agree (k : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (u t : RegState)
    (hag : AgreeBelow cursor u t) :
    ∃ u', denoteInstrs k u (block cursor as) = some u' ∧
      AgreeBelow cursor u' (run k t as) := by
  obtain ⟨u', h1, h2⟩ := block_correct k cursor as hWF u
  exact ⟨u', h1,
    fun r hr => (h2 r hr).trans (run_congr k cursor as hWF u t hag r hr)⟩

private theorem obindSome {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

theorem ceBody_defined (c : Params) (k : Nat) (s : RegState) (hR : c.R % M ≠ 0)
    (h45 : stA c k s 45 ≠ 0) (h47 : stA c k s 47 ≠ 0) (h21 : stA c k s 21 ≠ 0) :
    ∃ s', denoteInstrs k s (ceBody c) = some s' ∧
      AgreeBelow cursor s' (ceRun c k s) := by
  have step1 : denoteInstrs k s [Instr.binop 13 .udiv .idx (.lit c.R)] =
      some (idxStep c.R k s) := by
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, idxStep, hR]
  obtain ⟨u1, hu1, ha1⟩ := blockStep_agree k (blkA c) (blkA_wf c)
    (idxStep c.R k s) (idxStep c.R k s)
    (AgreeBelow.refl cursor (idxStep c.R k s))
  have ha1' : AgreeBelow cursor u1 (stA c k s) := ha1
  have hne1 : u1 45 ≠ 0 := by rw [ha1' 45 (by decide)]; exact h45
  have ha2 : AgreeBelow cursor (divStep 48 44 45 u1)
      (divStep 48 44 45 (stA c k s)) :=
    divStep_congr 48 44 45 (by decide) (by decide) ha1'
  have hne2 : (divStep 48 44 45 u1) 47 ≠ 0 := by
    rw [divStep_ne _ _ _ _ _ (by decide)]
    rw [ha1' 47 (by decide)]; exact h47
  have ha3 : AgreeBelow cursor (divStep 49 46 47 (divStep 48 44 45 u1))
      (divStep 49 46 47 (divStep 48 44 45 (stA c k s))) :=
    divStep_congr 49 46 47 (by decide) (by decide) ha2
  have hne3 : (divStep 49 46 47 (divStep 48 44 45 u1)) 21 ≠ 0 := by
    rw [divStep_ne _ _ _ _ _ (by decide), divStep_ne _ _ _ _ _ (by decide)]
    rw [ha1' 21 (by decide)]; exact h21
  have ha4 : AgreeBelow cursor
      (divStep 50 15 21 (divStep 49 46 47 (divStep 48 44 45 u1)))
      (stW c k s) :=
    divStep_congr 50 15 21 (by decide) (by decide) ha3
  obtain ⟨u5, hu5, ha5⟩ := blockStep_agree k (blkB c) (blkB_wf c)
    (divStep 50 15 21 (divStep 49 46 47 (divStep 48 44 45 u1))) (stW c k s) ha4
  refine ⟨u5, ?_, ha5⟩
  rw [ceBody, denoteInstrs_append, step1, obindSome,
    denoteInstrs_append, hu1, obindSome,
    denoteInstrs_append, udivStep_denote k 48 44 45 u1 hne1, obindSome,
    denoteInstrs_append,
    udivStep_denote k 49 46 47 (divStep 48 44 45 u1) hne2, obindSome,
    denoteInstrs_append,
    udivStep_denote k 50 15 21 (divStep 49 46 47 (divStep 48 44 45 u1)) hne3,
    obindSome, hu5]

/-! ## §14 The step function the fold bridge wants -/

/-- What the emitted body actually leaves in every register. -/
def ceStep (c : Params) (k : Nat) (s : RegState) : RegState :=
  (denoteInstrs k s (ceBody c)).getD s

private theorem denoteOperand_ltM (k : Nat) (u : RegState) (hu : ∀ i, u i < M)
    (o : Operand) : denoteOperand k u o < M := by
  cases o with
  | reg i => exact hu i
  | lit v => exact Nat.mod_lt _ M_pos
  | «idx» => exact Nat.mod_lt _ M_pos

theorem denoteInstrs_lt (k : Nat) :
    ∀ (is : List Instr) (u u' : RegState), denoteInstrs k u is = some u' →
      (∀ i, u i < M) → ∀ i, u' i < M := by
  intro is
  induction is with
  | nil =>
      intro u u' h hu i
      cases h
      exact hu i
  | cons x rest ih =>
      intro u u' h hu
      have hcons : denoteInstrs k u (x :: rest) =
          (denoteInstr k u x).bind fun s' => denoteInstrs k s' rest := rfl
      rw [hcons] at h
      cases hx : denoteInstr k u x with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some u1 =>
          rw [hx, obindSome] at h
          refine ih u1 u' h ?_
          cases x with
          | mov dest src =>
              have hu1 : u1 = u.set dest (denoteOperand k u src) := by
                have : some (u.set dest (denoteOperand k u src)) = some u1 := hx
                exact (Option.some.inj this).symm
              subst hu1
              intro i
              by_cases hd : i = dest
              · subst hd
                simpa [RegState.set] using denoteOperand_ltM k u hu src
              · rw [regSet_ne _ _ _ _ hd]; exact hu i
          | binop dest op l r =>
              have hb : denoteInstr k u (Instr.binop dest op l r) =
                  (denoteOp op (denoteOperand k u l)
                    (denoteOperand k u r)).bind
                      fun res => some (u.set dest res) := rfl
              rw [hb] at hx
              cases hop : denoteOp op (denoteOperand k u l)
                  (denoteOperand k u r) with
              | none => rw [hop] at hx; exact absurd hx (by simp)
              | some res =>
                  rw [hop, obindSome] at hx
                  have hu1 : u1 = u.set dest res := (Option.some.inj hx).symm
                  subst hu1
                  intro i
                  by_cases hd : i = dest
                  · subst hd
                    simpa [RegState.set] using denoteOp_lt op _ _ res hop
                  · rw [regSet_ne _ _ _ _ hd]; exact hu i

/-- The machine step, at a visited index and under the invariant. -/
theorem ceStep_spec (c : Params) (hP : c.Sane) (k : Nat)
    (hk : k < c.len * c.R) (s : RegState) (hs : Inv c k s) :
    denoteInstrs k s (ceBody c) = some (ceStep c k s) ∧
      valsOf (ceStep c k s) = ceRound c k (valsOf s) ∧
      Inv c (k + 1) (ceStep c k s) := by
  have hRM : c.R % M ≠ 0 := by
    have h1 : c.R < M := Nat.lt_trans hP.RSmall (by decide)
    have h2 := hP.RBig
    rw [Nat.mod_eq_of_lt h1]; omega
  obtain ⟨h45, h47, h21, hv, hI⟩ := ceRun_spec c hP hk hs
  obtain ⟨u, hu, hag⟩ := ceBody_defined c k s hRM h45 h47 h21
  have hstep : ceStep c k s = u := by simp [ceStep, hu]
  refine ⟨by rw [hstep]; exact hu, ?_, ?_⟩
  · rw [hstep, ← hv]
    show (⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11,
      u 12⟩ : Vals) = _
    rw [hag 0 (by decide), hag 1 (by decide), hag 2 (by decide),
      hag 3 (by decide), hag 4 (by decide), hag 5 (by decide),
      hag 6 (by decide), hag 7 (by decide), hag 8 (by decide),
      hag 9 (by decide), hag 10 (by decide), hag 11 (by decide),
      hag 12 (by decide)]
    rfl
  · rw [hstep]
    exact
      { word := denoteInstrs_lt k (ceBody c) s u hu hs.word
        okLe := by rw [hag 1 (by decide)]; exact hI.okLe
        cfLe := by rw [hag 4 (by decide)]; exact hI.cfLe
        pkPow := by rw [hag 2 (by decide), hag 3 (by decide)]; exact hI.pkPow
        kkLe := by rw [hag 3 (by decide)]; exact hI.kkLe
        pkLe := by rw [hag 2 (by decide)]; exact hI.pkLe
        candLe := by rw [hag 2 (by decide)]; exact hI.candLe
        bumpRnd := by rw [hag 2 (by decide)]; exact hI.bumpRnd
        q0Lt := by rw [hag 9 (by decide)]; exact hI.q0Lt
        r0Lt := by rw [hag 10 (by decide)]; exact hI.r0Lt
        fALt := by rw [hag 11 (by decide)]; exact hI.fALt
        fBLt := by rw [hag 12 (by decide)]; exact hI.fBLt
        divA := by
          rw [hag 5 (by decide), hag 6 (by decide), hag 2 (by decide)]
          exact hI.divA
        divB := by
          rw [hag 7 (by decide), hag 8 (by decide), hag 2 (by decide)]
          exact hI.divB }

/-! ## §15 The index-restricted fold bridge, with an advancing invariant

`RS62LadderEncoding.Program.denote_eq_foldl_mem` carries a predicate on states
alone.  This body's invariant has to mention the loop index — the dyadic
exponent lags the candidate, and only the index says by how much — so the
bridge is re-proved here with `P : Nat → RegState → Prop`.  It is the same
simulation argument, and it is reusable by any port whose invariant advances.
-/

theorem foldlM_body_eq_foldl_index (body : List Instr)
    (P : Nat → RegState → Prop) (step : Nat → RegState → RegState) (bound : Nat)
    (hStep : ∀ i s, i < bound → P i s →
      denoteInstrs i s body = some (step i s))
    (hClosed : ∀ i s, i < bound → P i s → P (i + 1) (step i s)) :
    ∀ (m a : Nat), a + m ≤ bound → ∀ s : RegState, P a s →
      (List.range' a m).foldlM (fun s i => denoteInstrs i s body) s =
        some ((List.range' a m).foldl (fun s i => step i s) s) := by
  intro m
  induction m with
  | zero => intro a _ s _; rfl
  | succ m ih =>
      intro a hb s hP
      have hlt : a < bound := by omega
      show (denoteInstrs a s body).bind
        (fun s => (List.range' (a + 1) m).foldlM
          (fun s i => denoteInstrs i s body) s) = _
      rw [hStep a s hlt hP]
      exact ih (a + 1) (by omega) (step a s) (hClosed a s hlt hP)

theorem foldl_index_closed (P : Nat → RegState → Prop)
    (step : Nat → RegState → RegState) (bound : Nat)
    (hClosed : ∀ i s, i < bound → P i s → P (i + 1) (step i s)) :
    ∀ (m a : Nat), a + m ≤ bound → ∀ s : RegState, P a s →
      P (a + m) ((List.range' a m).foldl (fun s i => step i s) s) := by
  intro m
  induction m with
  | zero => intro a _ s hP; simpa using hP
  | succ m ih =>
      intro a hb s hP
      have hlt : a < bound := by omega
      have := ih (a + 1) (by omega) (step a s) (hClosed a s hlt hP)
      have he : a + 1 + m = a + (m + 1) := by omega
      rw [he] at this
      exact this

/-- **The range-loop bridge, with an index-dependent invariant.** -/
theorem Program.denote_eq_foldl_index (p : Program) (P : Nat → RegState → Prop)
    (step : Nat → RegState → RegState) (fin : RegState → RegState)
    (s₀ : RegState)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P 0 s₀)
    (hStep : ∀ i s, i < p.loopCount → P i s →
      denoteInstrs i s p.body = some (step i s))
    (hClosed : ∀ i s, i < p.loopCount → P i s → P (i + 1) (step i s))
    (hEpilogue : ∀ s, denoteInstrs 0 s p.epilogue = some (fin s)) :
    p.denote =
      some (fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀) p.output) := by
  have hrange : List.range p.loopCount = List.range' 0 p.loopCount :=
    List.range_eq_range'
  show (denoteInstrs 0 initialState p.init).bind _ = _
  rw [hInit]
  show ((List.range p.loopCount).foldlM
    (fun s index => denoteInstrs index s p.body) s₀).bind _ = _
  rw [hrange]
  rw [foldlM_body_eq_foldl_index p.body P step p.loopCount hStep hClosed
    p.loopCount 0 (by omega) s₀ hP₀]
  show ((denoteInstrs 0 _ p.epilogue).bind _) = _
  rw [hEpilogue _]
  rfl

/-! ## §16 Initialisation, epilogue, and the whole program -/

/-- `lo < 2²⁵`. -/
theorem Params.Sane.loLt {c : Params} (hP : c.Sane) : c.lo < 2 ^ 25 := by
  have := hP.topSmall; have := hP.lenPos; omega

/-- `k₀ ≤ 24`, because `2^k₀ ≤ lo < 2²⁵`. -/
theorem Params.Sane.k0Le {c : Params} (hP : c.Sane) : c.k0 ≤ 24 := by
  rcases Nat.lt_or_ge c.k0 25 with h | h
  · omega
  · have hp : (2 : Nat) ^ 25 ≤ 2 ^ c.k0 := Nat.pow_le_pow_right (by decide) h
    have h1 := hP.k0lo
    have h2 := hP.loLt
    omega

/-- The carried registers after `ceInit`. -/
def initVals (c : Params) : Vals :=
  ⟨0, 1, 2 ^ c.k0, c.k0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The register file after `ceInit`. -/
def ceInitState (c : Params) : RegState :=
  ((initialState.set 1 (1 % M)).set 2 (2 ^ c.k0 % M)).set 3 (c.k0 % M)

theorem ceInit_denote (c : Params) :
    denoteInstrs 0 initialState (ceInit c) = some (ceInitState c) := rfl

theorem ceInitState_vals (c : Params) (hP : c.Sane) :
    ceInitState c 0 = 0 ∧ ceInitState c 1 = 1 ∧
    ceInitState c 2 = 2 ^ c.k0 ∧ ceInitState c 3 = c.k0 ∧
    (∀ j, 4 ≤ j → ceInitState c j = 0) := by
  have hpk : (2 : Nat) ^ c.k0 < M := by
    have := hP.k0lo; have := hP.loLt
    have : (2 : Nat) ^ 25 < M := by decide
    omega
  have hk0 : c.k0 < M := by
    have h1 := hP.k0Le
    have h2 : (25 : Nat) < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ceInitState, RegState.set, initialState]
  · simp [ceInitState, RegState.set, initialState, l1]
  · simp [ceInitState, RegState.set, initialState, Nat.mod_eq_of_lt hpk]
  · simp [ceInitState, RegState.set, initialState, Nat.mod_eq_of_lt hk0]
  · intro j hj
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    have h3 : j ≠ 3 := by omega
    simp [ceInitState, RegState.set, initialState, h1, h2, h3]

theorem valsOf_ceInitState (c : Params) (hP : c.Sane) :
    valsOf (ceInitState c) = initVals c := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := ceInitState_vals c hP
  simp [valsOf, initVals, e0, e1, e2, e3, e4 4 (by omega), e4 5 (by omega),
    e4 6 (by omega), e4 7 (by omega), e4 8 (by omega), e4 9 (by omega),
    e4 10 (by omega), e4 11 (by omega), e4 12 (by omega)]

theorem ceInitState_inv (c : Params) (hP : c.Sane) : Inv c 0 (ceInitState c) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := ceInitState_vals c hP
  have hR : 0 < c.R := by have := hP.RBig; omega
  have hcand : cand c 0 = c.lo := by simp [cand, Nat.zero_div]
  have hrnd : rnd c 0 = 0 := by simp [rnd]
  have hk0hi := hP.k0hi
  have hpow : (2 : Nat) ^ (c.k0 + 1) = 2 * 2 ^ c.k0 := by
    rw [Nat.pow_succ, Nat.mul_comm]
  exact
    { word := by
        intro i
        simp only [ceInitState, RegState.set, initialState]
        split
        · exact Nat.mod_lt _ M_pos
        · split
          · exact Nat.mod_lt _ M_pos
          · split
            · exact Nat.mod_lt _ M_pos
            · exact M_pos
      okLe := by rw [e1]; omega
      cfLe := by rw [e4 4 (by omega)]; omega
      pkPow := by rw [e2, e3]
      kkLe := by rw [e3]; exact hP.k0Le
      pkLe := by rw [e2, hcand]; exact hP.k0lo
      candLe := by rw [e2, hcand]; omega
      bumpRnd := by intro _; exact hrnd
      q0Lt := by rw [e4 9 (by omega)]; exact Nat.two_pow_pos 36
      r0Lt := by rw [e4 10 (by omega)]; exact Nat.two_pow_pos 50
      fALt := by rw [e4 11 (by omega)]; exact Nat.two_pow_pos 36
      fBLt := by rw [e4 12 (by omega)]; exact Nat.two_pow_pos 36
      divA := by rw [hrnd]; intro h; exact absurd rfl h
      divB := by rw [hrnd]; intro h; exact absurd rfl h }

/-- The accepting bit: on the certified side of `bound`, in the direction the
instance's rounding demands. -/
def acceptBit (c : Params) (a : Nat) : Nat :=
  if c.up = 1 then (if a ≤ c.bound then 1 else 0)
  else (if c.bound ≤ a then 1 else 0)

/-- The epilogue's effect. -/
def ceFin (c : Params) (u : RegState) : RegState :=
  (u.set 64 (acceptBit c (u 0))).set 65 ((u 1 * acceptBit c (u 0)) % M)

theorem ceEpilogue_denote (c : Params) (hb : c.bound < M) (u : RegState) :
    denoteInstrs 0 u (ceEpilogue c) = some (ceFin c u) := by
  have eb : c.bound % M = c.bound := Nat.mod_eq_of_lt hb
  by_cases hu : c.up = 1 <;>
    simp [ceEpilogue, ceFin, acceptBit, denoteInstrs, denoteInstr,
      denoteOperand, denoteOp, hu, eb, RegState.set]

theorem ceFin_out (c : Params) (u : RegState) :
    ceFin c u 65 = (u 1 * acceptBit c (u 0)) % M := rfl

/-- Every prefix of the loop carries the invariant, and reads off as the
corresponding prefix of the `ceRound` fold. -/
theorem ceFold_spec (c : Params) (hP : c.Sane) :
    ∀ N, N ≤ c.len * c.R →
      valsOf ((List.range N).foldl (fun w i => ceStep c i w) (ceInitState c)) =
          (List.range N).foldl (fun v i => ceRound c i v) (initVals c) ∧
        Inv c N ((List.range N).foldl (fun w i => ceStep c i w)
          (ceInitState c)) := by
  intro N
  induction N with
  | zero =>
      intro _
      exact ⟨by simpa using valsOf_ceInitState c hP, ceInitState_inv c hP⟩
  | succ N ih =>
      intro hN
      obtain ⟨ihv, ihI⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨_, hv, hI⟩ := ceStep_spec c hP N (by omega) _ ihI
      exact ⟨by rw [hv, ihv], hI⟩

/-- **The program denotes the flat fold.** -/
theorem ceProgram_denote (c : Params) (hP : c.Sane) :
    (ceProgram c).denote =
      some (if ((List.range (c.len * c.R)).foldl
                  (fun v k => ceRound c k v) (initVals c)).ok = 1 ∧
              (if c.up = 1
                then ((List.range (c.len * c.R)).foldl
                        (fun v k => ceRound c k v) (initVals c)).acc ≤ c.bound
                else c.bound ≤ ((List.range (c.len * c.R)).foldl
                        (fun v k => ceRound c k v) (initVals c)).acc)
            then 1 else 0) := by
  have hb : c.bound < M := hP.boundLt
  have hI0 := ceInitState_inv c hP
  have hden := Program.denote_eq_foldl_index (ceProgram c) (Inv c) (ceStep c)
    (ceFin c) (ceInitState c) (ceInit_denote c) hI0
    (fun index u hidx hu => (ceStep_spec c hP index hidx u hu).1)
    (fun index u hidx hu => (ceStep_spec c hP index hidx u hu).2.2)
    (fun u => ceEpilogue_denote c hb u)
  obtain ⟨hFv, hFI⟩ := ceFold_spec c hP (c.len * c.R) (Nat.le_refl _)
  have hacc : ((List.range (c.len * c.R)).foldl
        (fun w i => ceStep c i w) (ceInitState c)) 0 =
      ((List.range (c.len * c.R)).foldl
        (fun v i => ceRound c i v) (initVals c)).acc :=
    congrArg Vals.acc hFv
  have hok : ((List.range (c.len * c.R)).foldl
        (fun w i => ceStep c i w) (ceInitState c)) 1 =
      ((List.range (c.len * c.R)).foldl
        (fun v i => ceRound c i v) (initVals c)).ok :=
    congrArg Vals.ok hFv
  have hokLe := hFI.okLe
  rw [hok] at hokLe
  rw [hden]
  show some (ceFin c ((List.range (c.len * c.R)).foldl
    (fun w i => ceStep c i w) (ceInitState c)) 65) = _
  rw [ceFin_out, hacc, hok]
  rcases (show ((List.range (c.len * c.R)).foldl
      (fun v i => ceRound c i v) (initVals c)).ok = 0 ∨
    ((List.range (c.len * c.R)).foldl
      (fun v i => ceRound c i v) (initVals c)).ok = 1 by omega) with h | h <;>
    by_cases hu : c.up = 1 <;>
      simp [h, hu, acceptBit, l0, l1] <;> split <;> simp [l0, l1]

/-! ## §17 Re-blocking

The flat fold over `[0, len·R)` is `len` blocks of `R` rounds — the form the
per-candidate argument needs.  A re-association of the same applications in the
same order; no hypothesis, and no fold evaluated.
-/

theorem ceFold_blocked (c : Params) :
    (List.range (c.len * c.R)).foldl (fun v k => ceRound c k v) (initVals c) =
      (List.range c.len).foldl
        (BlockedFold.block c.R (fun v k => ceRound c k v)) (initVals c) :=
  BlockedFold.foldl_range_mul c.len c.R (fun v k => ceRound c k v) (initVals c)

end LeanCompCert.Ports.CeDyadicFold
