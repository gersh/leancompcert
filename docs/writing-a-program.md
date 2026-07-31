# How to actually write a program

> Read [what is proved](what-is-proved.md) first if you have not — in
> particular, that a *program* here is a **value you construct**, not Lean
> source that gets compiled. This guide is about constructing one.

The short answer to "do I have to write assembly?" is **no**. You write Lean
that *emits* instructions, and arithmetic expressions get compiled for you,
with a proof. But the target language is genuinely restricted, and the
restrictions change how you express things. That is what this guide is about.

## 1. The shape of a program

```lean
{ regCount  := 8          -- registers 0 … 7 exist
  arrayLen  := 1000       -- one array of 1000 cells
  loopCount := 1000000    -- body runs with idx = 0, 1, …, 999999
  init      := [...]      -- runs once, before the loop
  body      := [...]      -- runs once per index
  epilogue  := [...]      -- runs once, after the loop
  output    := 5 }        -- the answer is whatever ends up in register 5
```

That is the whole execution model: **setup, a loop with a fixed trip count, a
finish, one output register.** The trip count is fixed *before* the program
runs and cannot depend on anything computed inside it.

## 2. Three ways to write instructions

### Raw values — possible, never done

```lean
[ .scalar (.binop 1 .add (.reg 1) (.idx)) ]
```

### `expr!( … )` — arithmetic in ordinary notation, compiled with a proof

```lean
expr!(#1 * #1 + idx)        -- register 1 squared plus the loop index
expr!(#3 % 210 == 0)        -- comparisons yield 0 or 1
```

`#n` is register *n*, `idx` is the loop index, numerals are literals.
`Expr.toBody` turns the tree into instructions, **allocating scratch registers
itself**, and `Expr.toBody_correct` proves the instructions compute what the
expression means. You never do register allocation by hand for arithmetic.

### Emitter functions — what the real ports use

Ordinary Lean functions returning `List AInstr`. They run when the module
elaborates; they are generators, not the thing being proved.

```lean
def seed (reg value : Nat) : List AInstr :=
  [.scalar (.mov reg (.lit value))]

def gtTest (reg bound : Nat) : List AInstr :=
  [ .scalar (.binop 91 .gt (.reg reg) (.lit bound))
  , .scalar (.binop 92 .add (.reg 92) (.reg 91)) ]

def myInit (s : Seed) : List AInstr :=
  seed rAcc s.acc ++ seed rCursor s.cursor
```

Build a vocabulary of these for your problem and the body reads like Lean.
`R2SegSieve`'s 326-instruction body is assembled this way.

## 3. The constraint that changes everything: no control flow

There is no branch, no `while`, no early exit, no function call. Every
instruction executes every iteration. Here is how each thing you would
normally reach for is expressed instead.

### An `if` — multiply by a gate

Compute a 0/1 gate with a comparison, then blend:

```lean
/-- `dst := if gate then x else y`.  `s` is scratch. -/
def muxBody (dst gate x y s : Nat) : List AInstr :=
  [ .scalar (.binop s .sub (.lit 1) (.reg gate))   -- s := 1 − gate
  , .scalar (.binop s .mul (.reg s) (.reg y))      -- s := (1−gate)·y
  , .scalar (.binop dst .mul (.reg gate) (.reg x)) -- dst := gate·x
  , .scalar (.binop dst .add (.reg dst) (.reg s)) ]
```

> ⚠ **The ordering is load-bearing, and getting it wrong is silent.** Almost
> every conditional update has `y = dst` (i.e. "keep the old value unless the
> gate fires"). So `y` must be read **before** `dst` is written. Writing the
> `gate·x` product first reads more naturally and turns every such update into
> `(1 − gate)²`. On one port that reset a cursor every iteration and produced a
> confident answer off by four orders of magnitude, which every
> self-consistency check accepted. An independent oracle caught it; nothing
> else did.

### An assertion — accumulate a violation counter

You cannot stop early on failure, so don't. Add the failure indicator to a
counter and make that counter the program's output:

```lean
def gtTest (reg bound : Nat) : List AInstr :=
  [ .scalar (.binop 91 .gt (.reg reg) (.lit bound))
  , .scalar (.binop 92 .add (.reg 92) (.reg 91)) ]
```

The artifact's `main` returns 0 exactly when the total is zero. A nonzero
output means "some check failed"; the exit status carries that.

### Early exit — you don't

Run the whole loop. If the work is genuinely variable per item, see the next
pattern.

### A variable-length inner loop — fix a budget, then *check* it

You cannot iterate "until done". Give the inner work a fixed number of rounds,
and **verify at the end that the rounds were enough** — folding the check into
the violation counter, exactly like an assertion.

This is not a formality. On one port the per-item work was not monotone in the
loop index, so a budget sized from the first window under-served a later one by
1.3%. Because the budget was checked, that surfaced as a reported violation
rather than a wrong answer.

> **Never let a truncated computation look like a completed one.** Any place
> you bound work, bound it *and check the bound*.

## 4. Registers and arrays

Registers hold `Nat`, bounded by the word modulus; every write maintains that.
`regCount` bounds every index you use. Conventions in the existing ports:
low numbers for meaningful state, a named block for scratch, and one register
reserved as the violation counter (`92` in `ArraySegSieve`).

Arrays are one flat block of `arrayLen` cells:

```lean
.load  dest idxReg     -- dest := arr[regs idxReg]
.store idxReg srcReg   -- arr[regs idxReg] := regs srcReg
```

**An out-of-range index makes the whole program's meaning `none`**, not a
garbage read. That is a feature: it means an indexing bug cannot silently
produce a plausible number, and `denote = some n` already carries "every index
was in range".

## 5. When one word is not enough

Products and sums overflow sooner than you expect — the *addends* as readily as
the totals. Use the proved two-limb layer:

- `Verified/AddWide.lean` — `addWide_spec`, `sumWide_spec`, `subWide_exact`
- `Verified/MulWide.lean` — full 64×64 → 128

Work out where the width binds and **prove it rather than assuming it**. One
port's `64×64` product of two fixed-point values forced a scale constraint of
`S ≤ 27`; another found an intermediate sitting 0.23 bits below 2⁶³ and another
that exceeded it. Both were found by an oracle, not by inspection.

## 6. Transcendental functions

Built from the fragment, each with an exact integer bracket rather than an
error estimate:

| | gives |
| --- | --- |
| `Verified/LogFixed.lean` | `logFix_bracket` — a two-sided integer bracket on `⌊2^S log₂ n⌋` |
| `Verified/ExpFixed.lean` | `expFix_bracket`, unconditional; `P ≤ 30` in pure `u64` |
| `Verified/Dyadic.lean`, `DyadicBisect.lean` | fixed-point intervals; outward-rounded square root, stated *squared* so it pins the value without naming a real |

The `expOK` idiom is worth copying: a root can be produced by any means at all —
even an unproved recurrence — as long as the program then *checks* it with two
integer comparisons. **The advance is unproved; the comparison is not.**

## 7. Assembling and chaining

Most ports define a `Cfg` and a `Cfg.program` that stitches together shared
setup with problem-specific pieces:

```lean
def Cfg.program (c : Cfg) (residue init epilogue : List AInstr) : AProgram :=
  { regCount, arrayLen := c.arrayLen
    loopCount := c.period * (c.rootCount + c.segCount)
    init := c.coreInit ++ init
    body := c.coreBody ++ residue
    epilogue, output := outputReg }
```

For ranges too large for one artifact, run a **chain**: each artifact takes the
previous one's carry-out as its seed.

> ⚠ **A chain driver that only checks the violation count is worthless.** A
> window seeded with the *wrong* carry-in still reports zero violations. The
> driver must also require each artifact's outputs to match the next one's
> declared inputs. Verify by deliberately corrupting a carry-in and confirming
> rejection — one such test moved a carry by a single ulp and every window still
> reported success.

## 8. What you owe in proof

For each port:

1. **`…_wf`** — the program is well-formed (register indices in range, etc.).
2. **`…_compiled`** — instantiate `AProgram.evalCC_compile`. This gives you
   "the compiled C computes what this program means".
3. **The encoding check** — that the program means what the *mathematics* says.
   Nothing above covers this. Evaluate `denote` in the kernel on a small
   configuration and compare against a simple reference (trial division,
   written from the definition). **Include a configuration that fails**, or you
   cannot distinguish a correct encoding from one that always returns zero.
4. **An independent oracle** — a C implementation written from the
   specification, not transliterated from your encoding, compared bit-for-bit
   on *every* output slot under both `ccomp` and `gcc`.

If your body is large enough that `denote` will not reduce in the kernel — the
register file is a chain of updates, so reads cost O(writes so far) and ~10⁵
writes defeats the interpreter — **say so in the module docstring** and lean
harder on (4), running the oracle at production parameters. See
`Ports/CDEMAbelScan.lean` for how that is documented.

## 9. A minimal worked example

Sum `i²` for `i < N`, and check the total stays under a bound.

```lean
def sumSquares (n bound : Nat) : AProgram :=
  { regCount  := 4
    arrayLen  := 1
    loopCount := n
    init      := seed 1 0 ++ seed 2 0          -- acc := 0, violations := 0
    body      := Expr.toBody 1 3 expr!(#1 + idx * idx)
    epilogue  := gtTest 1 bound
    output    := 2 }
```

`Expr.toBody 1 3 …` compiles the expression into register 1 using scratch from
register 3 upward, with the correctness theorem already proved. The epilogue
adds 1 to register 2 if the accumulator exceeded `bound`, and register 2 is the
output — so the artifact exits 0 exactly when the bound held.

Then prove `…_wf`, instantiate `evalCC_compile`, register it with
`check-native`, and add the theorems to `scripts/AxiomAudit.lean`.

## 10. Checklist

- [ ] Every bounded amount of work is **checked** to have been enough.
- [ ] Every `mux` reads its "keep" operand before writing its destination.
- [ ] Rounding goes in whichever direction makes the claim **harder** to
      satisfy — and that direction is not uniform across a formula.
- [ ] Accumulator widths proved, not assumed.
- [ ] A **failing** configuration is tested, not only a passing one.
- [ ] An independent oracle agrees on **every** output, under both compilers.
- [ ] Large emitted tables are **generated in the loop**, not written as
      literals — 27,421 literal entries overflowed `ccomp`'s stack and were
      still climbing past 27 GB.
- [ ] `#print axioms` read, not assumed.

## Worked ports to read

| port | shows |
| --- | --- |
| `Ports/ArraySegSieve.lean` | segmented sieve, chaining, threshold epilogues |
| `Ports/R2SegSieve.lean` | per-cell factorisation, a fixed-point log phase, budget checking |
| `Ports/CDEMAbelScan.lean` | wide arithmetic throughout, the mux hazard, an honest "no kernel check" note |
| `Ports/ExpFixPort.lean` | certified-guess idiom (`expOK`) |
| `Ports/A36Bisect.lean` | the case where you do not need an artifact at all |
