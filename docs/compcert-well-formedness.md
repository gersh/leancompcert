# CompCert well-formedness contract

The semantic boundary for a verified computation is the existing
`Verified.Reflect.Program` (or `ArrayState.AProgram`) DSL. A computation does
not need to be translated to Coq or rewritten in another language. It must
prove one additional Lean proposition:

```lean
p.CompCertWF
```

The definition is in `LeanCompCert/Verified/ClightContract.lean`.

## What the predicate requires

For scalar programs, `Program.CompCertWF` is the conjunction of:

1. `p.WF`, the existing structural register-bound condition;
2. `programSafe p`, evaluated along the actual DSL state trace.

At every dynamically executed instruction, `programSafe` requires:

- the divisor of `udiv` and `urem` is nonzero;
- the count of `shl` and `lshr` is less than 64.

Unsigned addition, subtraction, multiplication, and bitwise operations wrap
modulo `2^64`, as both the DSL and CompCert specify. Comparisons are total.

`AProgram.CompCertWF` adds the same scalar requirements and requires every
load or store index to be less than `arrayLen`. A theorem about a concrete
array allocation still separately assumes `BaseOk arrayLen base`, because the
base address belongs to the calling environment rather than to `AProgram`.

The guards are state-sensitive. A divisor or shift count read from a register
is checked after all preceding instructions and loop iterations have updated
that register.

## Lean theorems

The module proves:

```lean
program_denote_eq_totalRun :
  programSafe p ->
  p.denote = some (result of the guarded total trace)

aProgram_denote_eq_totalRun :
  aProgramSafe p ->
  p.denote = some (result of the guarded total array trace)
```

It also restates the existing generic Lean-to-CCIR theorem under the stronger
precondition as `program_evalCC_compile`; `program_evalCC_compile_total` and
`aProgram_evalCC_compile_total` give the closed-form compiled results.

These are structural theorems. They do not infer safety from the fact that a
particular native run happened to succeed.

## Proving the obligation without unrolling a large computation

For a small closed computation, the direct form is decidable:

```lean
theorem myProgram_compCertWF : myProgram.CompCertWF := by
  decide +kernel
```

Large loop bounds should normally use `programSafe_of_static`. It checks the
instruction blocks once and does not unfold the loop. Division/remainder and
shifts pass this fast route when their right operand is a safe literal:

```lean
theorem myProgram_compCertWF : myProgram.CompCertWF := by
  refine <| And.intro myProgram_wf
    (programSafe_of_static myProgram ?_ ?_ ?_)
  all_goals decide
```

When a divisor, shift count, or array index is computed dynamically, prove
the corresponding `blockDefined`/`aBlockDefined` condition using the existing
state invariants. This changes only the proof; it does not change the program
or emitted artifact.

### `native_decide` is not required

Neither `CompCertWF`, the Lean preservation theorems, the proof-gated emitter,
nor the Coq compiler theorem depends on `native_decide`.  The production
fixed-point certificate uses the following kernel-checked pattern:

```lean
theorem program_compCertWF : program.CompCertWF := by
  refine ⟨program_wf, programSafe_of_static program ?_ ?_ ?_⟩
  all_goals decide

theorem program_denote : program.denote = some expectedValue := by
  decide +kernel
```

The static safety theorem checks the instruction blocks once, regardless of
the loop bound.  If a large denotation is too expensive for kernel reduction,
prove it from loop invariants or another Lean theorem.  Using `native_decide`
is an optional trust choice for such a value proof, not a requirement of the
Lean-to-Clight correspondence.

The generated Coq artifact's `vm_compute` is also kernel checked: it constructs
a proof term that Coq's kernel verifies.  It is not Lean's `native_decide` and
does not add Lean's native evaluator to the trusted base.

## Agreement with CompCert's guard

`scripts/coq/ClightDefinedOps.v` defines the same guard with CompCert's own
`Int64.eq`, `Int64.ltu`, and `Int64.iwordsize`. Coq proves:

```coq
u64_op_defined_repr
```

which says that, for a value in `[0, 2^64)`, the arithmetic Lean-side guard is
equivalent to CompCert's guard after `Int64.repr`. It also proves:

```coq
sem_binary_operation_u64_exact
sem_binary_operation_u64_defined
```

The first theorem gives exact value agreement between every DSL `u64` binary
operation and CompCert's actual `sem_binary_operation`; the second says that
satisfying the guard makes this operation return a value instead of `None`.

The existing `ClightFragmentSem.run_fuel_funcall2` and
`ClightMemorySem.run_mem_fuel_funcall2` theorems turn successful evaluation of
the exact emitted Clight AST into `ClightBigstep.eval_funcall`.

## The proved scalar compiler

`scripts/coq/ClightDSLCompiler.v` now defines a Coq copy of the scalar DSL and
a compiler

```coq
compile_program : dsl_program -> Clight.function
```

The compiler emits the exact `Clight` AST used in the conclusion.  Its generic
theorem is:

```coq
compile_program_correct : forall p w ge m,
  dsl_denote p = Some w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_program p)) nil E0 m (Vlong w)
```

This is the formerly missing structural induction.  It proves operand lookup,
every scalar operation (through CompCert's actual
`sem_binary_operation`/`sem_cast`), register updates, the complete unrolled
trace, return, and function entry.

`LeanCompCert.Verified.ProgramClightEmit.emitProgram` does not print a second,
independently implemented Clight AST.  It prints the `Reflect.Program` as a
Coq `dsl_program` value and defines the artifact function by
`compile_program source_program`.  The generated artifact contains both a
closed `vm_compute` denotation lemma and an instance of
`compile_program_correct`.  Consequently, the exact function named in the
artifact has the claimed CompCert Clight semantics.

The emitter is proof-gated: its Lean arguments include
`p.CompCertWF` and `p.denote = some expected`.  Existing computations do not
need to be rewritten; they only add these two proof obligations.  An unsafe or
unproved program cannot call this artifact emitter.  These arguments are
ordinary propositions; they may be discharged entirely by kernel proofs, as
the fixed-point certificate now demonstrates.

The path is now:

```text
Lean Reflect.Program p
  | Lean proves p.CompCertWF and p.denote = some n
  v
generated Coq data source_p : dsl_program
  | Coq checks dsl_denote source_p = Some (Int64.repr n)
  v
f_p := compile_program source_p
  | compile_program_correct (generic Qed theorem)
  v
CompCert ClightBigstep.eval_funcall ... (Internal f_p) ... (Vlong n)
```

For the fixed-point certificate, the standalone low-overhead emitter is
`bench/FixedPointProgramClightEmit.lean`; the main executable's
`emit-clight-fixedpoint-v` command uses the same function.  The
`scripts/clight-direct-verify.py` pipeline compiles the generic compiler, the
generated artifact, and an independent exact-body evaluator check.

## Exact trust boundary

Lean's kernel and Coq's kernel cannot literally share a theorem object.  The
small remaining cross-kernel boundary is serialization of the first-order DSL
value (constructors and numerals).  It no longer includes C expressions,
temporary layout, casts, statement sequencing, or Clight AST construction;
all of those are produced by the proved Coq compiler.  Coq also recomputes the
serialized program's answer, so a bad serialization fails or proves a theorem
about visibly different source data rather than silently inheriting Lean's
claim.

This endpoint is a theorem about the exact CompCert `Clight` program.  To claim
the same theorem about native machine code, that exact AST must additionally
be passed through CompCert's verified backend and its top-level compiler
correctness theorem.  Compiling separately pretty-printed C through an
unverified parser is not definitionally the same artifact and retains the
parser/structural-correspondence boundary.
