# Tutorial 1 — Your first certificate

> New here? The two use-case guides —
> [a verified `native_decide`](use-case-1-verified-native-decide.md) and
> [a compiled artifact you can trust](use-case-2-verified-artifact.md) —
> say what is proved and why to trust it; this tutorial is the worked
> example both build on.

This walkthrough takes a small computation from nothing to a
machine-checked theorem plus a CompCert-verified native check. Everything
here uses only the stable public API (README, "Public API and
versioning"). A complete external-project version of the same flow lives
in `examples/consumer/`.

## What you will end up with

- a Lean theorem about your computation whose axioms are only the
  standard ones (`#print axioms` shows no `native_decide`, no
  `ofReduceBool`);
- a C program, compiled by the formally verified CompCert compiler,
  that independently checks the same value (its exit status is *not* the
  theorem — the theorem is kernel-checked; the binary is a cross-check).

## Step 1 — Write the computation as a register program

A `Verified.Reflect.Program` is a bounded fold: registers, an `init`
block, a `body` run once per loop index, an `epilogue`, and an output
register. Registers hold `u64` values; comparisons yield `0`/`1`.

Suppose we want to certify `Σ_{k=0}^{99} (3k + 1) mod 2⁶⁴`:

```lean
import LeanCompCert.Verified.Package

open LeanCompCert.Verified LeanCompCert.Verified.Reflect

def program : Program := {
  regCount := 3            -- r0 = accumulator, r1, r2 = temporaries
  loopCount := 100
  init := []               -- registers start at zero
  body := [
    .binop 1 .mul .idx (.lit 3),      -- r1 := 3k
    .binop 2 .add (.reg 1) (.lit 1),  -- r2 := 3k + 1
    .binop 0 .add (.reg 0) (.reg 2)   -- r0 += r2
  ]
  epilogue := []
  output := 0
}
```

Operands are `.reg i`, `.lit v`, or `.idx` (the loop index). The
operation set is the proved fragment: `add sub mul udiv urem band bor
bxor shl lshr` and the six comparisons `eq ne lt le gt ge`.

If you prefer expressions over three-address code, the verified
expression layer (`Verified.Frontend`) compiles `expr!(…)` terms with a
once-and-for-all correctness theorem — see its module docstring.

## Step 2 — Well-formedness (the only `decide`)

```lean
theorem program_wf : program.WF := by decide
```

This is **program-sized** (three instructions), never trace-sized: the
M1 packaging theorem makes everything else structural.

## Step 3 — Package it

```lean
def computation : Computation :=
  program.toComputation "Tutorial.sumDemo" program_wf
```

`toComputation` produces the packaged computation with *structural*
evidence that the production lowering succeeds and stays inside the
machine-checked fragment — no kernel evaluation happens here, at any
trace size.

## Step 4 — The certificate theorem

Compute the expected value independently (e.g. `python3 -c "print(sum(3*k+1
for k in range(100)))"` → `14950`), then:

```lean
def referenceSum : Nat :=
  (List.range 100).foldl (fun acc k => acc + (3 * k + 1)) 0

theorem returns_iff :
    computation.Returns ((14950 : Nat) : Int) ↔
      program.denote = some 14950 :=
  toComputation_returns program "Tutorial.sumDemo" program_wf 14950

def decision : Decision (referenceSum = 14950) := {
  computation
  acceptingValue := ((14950 : Nat) : Int)
  specification := returns_iff.trans (by decide +kernel)
}

theorem certificate : referenceSum = 14950 :=
  Decision.prove decision (returns_iff.mpr (by decide +kernel))
```

The kernel work in each `decide +kernel` is evaluating `program.denote`
(a plain Lean fold) and the reference fold — the CCIR model is never
evaluated; the bridge theorems connect them structurally. For larger
programs add `set_option maxRecDepth 800000` at the top of the file, and
**chunk very large folds** (see Tutorial 3, "Kernel-scale discipline").

Check your axioms: `#print axioms certificate` must list only `propext`
(possibly with `Classical.choice, Quot.sound`).

## Step 5 — The CompCert-checked native run

```lean
def mainC : String :=
  "\nint main(void)\n{\n" ++
  "    return l_Tutorial_sumDemo() == UINT64_C(14950) ? 0 : 1;\n}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[computation.fn] }
  pure (source ++ mainC)
```

The C symbol is `l_` + your name with dots replaced by underscores.
Write `emittedC` to a file and compile:

```console
ccomp -I<repo>/runtime/include -I"$(lean --print-prefix)/include" \
  -o demo demo.c
./demo && echo accepted
```

The acceptance suite additionally runs three verification gates over
emitted certificates — clightgen translation validation, structural
correspondence, and the Coq-kernel semantics check (Tutorial 4).

## Recap of the trust story

Your theorem is proved by Lean's kernel evaluating a Lean-level fold;
the structural theorems (`toComputation_returns` → the reflection bridge
→ the preservation proof) connect that fold to the CCIR trace and the
restricted-C model; CompCert's proven compiler carries the C to
assembly; and the native run is an independent check whose exit status
is deliberately never admitted as a theorem.
