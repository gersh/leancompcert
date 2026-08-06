# Verified Computation in Lean 4 via Machine-Checked Compilation to CompCert C: Architecture, Proof Coverage, and Trust Model

**Abstract**  
Proof assistants such as Lean 4 excel at verifying mathematical logic but face fundamental performance limits when executing large-scale finite computations inside the kernel. The standard alternative, `native_decide`, bypasses the kernel by compiling computations to native code, but forces the proof to trust Lean's whole frontend, code generator, C compiler, and C runtime. This paper presents the architecture, formalization, and trust model of `lean-compcert`, a framework for verified computation in Lean 4. `lean-compcert` defines a restricted, first-order register machine domain-specific language ($\text{DSL}$) with formal denotational semantics (`Program.denote` and `AProgram.denote`). We prove in Lean 4 that any valid DSL program compiles to a restricted subset of C while preserving denotational semantics (`evalCC_compile`). We further connect this emission directly to CompCert’s Coq semantics via direct Clight AST emission (`Verified/ClightEmit.lean`), verified in Coq's kernel (`ClightFragmentSem.v`). We present a complete analysis of what is machine-proved versus what remains in the Trusted Computing Base (TCB), establish a zero-axiom policy for core verification modules, and provide a step-by-step guide for incorporating verified computations into Lean 4 proofs.

---

## 1. Introduction

Mathematical proofs in computational number theory, combinatorics, and real analysis frequently depend on verifying finite but massive bounds (e.g., verifying an inequality across billions of integers). In proof assistants like Lean 4, formalizing such proofs presents a fundamental trade-off:

1. **Kernel Evaluation (`decide +kernel`):** The Lean 4 kernel evaluates expressions via its internal reduction engine. While highly trustworthy (relying only on standard Lean axioms: `propext`, `Classical.choice`, and `Quot.sound`), it is designed for logical correctness rather than high throughput. Large computational sweeps quickly exhaust memory or exceed reasonable wall-clock execution limits.
2. **Unverified Native Reduction (`native_decide`):** Lean compiles expressions into unverified C code, builds a shared library, and dynamically executes it. While fast, `native_decide` introduces a massive Trusted Computing Base (TCB)—requiring trust in Lean's parser, elaborator, LCNF compiler pass, C code emitter, host C compiler (e.g., `gcc` or `clang`), host linker, and Lean C runtime library.

`lean-compcert` resolves this dilemma by providing a verified compilation pipeline. Rather than compiling arbitrary Lean functions, `lean-compcert` targets a restricted register-machine language whose denotational semantics and compilation into C are machine-proved inside Lean 4. The resulting C code is subsequently compiled using [CompCert](https://compcert.org/), a C compiler with a Coq-verified semantic-preservation proof down to assembly text.

```
+-------------------------------------------------------------------------+
|                              LEAN 4 KERNEL                              |
|                                                                         |
| High-Level Math Claim <---> Reference Function <---> Program.denote      |
|                                                           |             |
|                                                    evalCC_compile       |
|                                                     (Proved in Lean)    |
|                                                           v             |
|                                                       Emitted C         |
+-------------------------------------------------------------------------+
                                                            |
                                                   Direct AST / Clight
                                                   (Proved in Coq)
                                                            v
+-------------------------------------------------------------------------+
|                           COMPCERT & HARDWARE                           |
|                                                                         |
|                      CompCert (Coq-Verified C -> Asm)                   |
|                                   v                                     |
|                        Assembly Text (gcc / as)                         |
|                                   v                                     |
|                      Hardware Execution / Attestation                   |
+-------------------------------------------------------------------------+
```

---

## 2. Language Architecture and Denotational Semantics

### 2.1 The Register Machine Language (`Program` and `AProgram`)

To render compilation proofs tractable, `lean-compcert` restricts the source computation model to a bounded register machine with flat control flow. A program consists of three straight-line basic blocks executed sequentially: an `init` block, a `body` block executed inside a fixed-count loop, and an `epilogue` block.

```lean
structure Program where
  regCount  : Nat          -- Total register allocation bound
  loopCount : Nat          -- Exact loop trip count [0 ... loopCount - 1]
  init      : List Instr   -- Initialization straight-line sequence
  body      : List Instr   -- Repeated loop body sequence
  epilogue  : List Instr   -- Finalization straight-line sequence
  output    : Nat          -- Destination register containing final result

structure AProgram where
  regCount  : Nat
  arrayLen  : Nat          -- Length of single static array
  loopCount : Nat
  init      : List AInstr
  body      : List AInstr
  epilogue  : List AInstr
  output    : Nat
```

### 2.2 Instruction Set & Primitive Operations

The scalar instruction set `Instr` and array-extended instruction set `AInstr` are strictly first-order:

```lean
inductive Operand where
  | reg (i : Nat) 
  | lit (v : Nat) 
  | idx             -- Refers dynamically to current loop index

inductive Op where
  | add | sub | mul | udiv | urem
  | band | bor | bxor | shl | lshr
  | eq | ne | lt | le | gt | ge

inductive Instr where
  | mov (dest : Nat) (src : Operand)
  | binop (dest : Nat) (op : Op) (lhs rhs : Operand)

inductive AInstr where
  | scalar (i : Instr)
  | load  (dest : Nat) (idxReg : Nat)
  | store (idxReg : Nat) (srcReg : Nat)
```

**Key Syntactic Restrictions:**
* No unbounded recursion or dynamic `while` loops (trip counts are statically known).
* No pointers, heap allocation, or dynamic memory management.
* Single flat, bounds-checked array state $A \in \mathbb{N}^{\text{arrayLen}}$.
* All register operations operate on 64-bit unsigned integers (`u64`) with modulo $2^{64}$ arithmetic.

### 2.3 Denotational Semantics (`denote`)

The denotation `p.denote` for a `Program` or `AProgram` is defined as a purely functional evaluation in standard Lean arithmetic. The state is represented as a functional mapping $\text{RegState} : \mathbb{N} \to \mathbb{N}$ (and $\text{AState}$ for arrays).

```lean
def Program.denote (p : Program) : Option Nat :=
  match evalInstrs p.init (RegState.init p.regCount) with
  | none => none
  | some s0 =>
    match loop p.loopCount (fun i s => evalInstrs (substIdx p.body i) s) s0 with
    | none => none
    | some s1 =>
      match evalInstrs p.epilogue s1 with
      | none => none
      | some s2 => some (s2.get p.output)
```

---

## 3. Verified Translation Pipeline and Proof Coverage

### 3.1 Lean-Side Compilation & Semantic Preservation

Compilation maps a `Program` or `AProgram` into a restricted subset of C syntax ([`LeanCompCert/CCIR/Basic.lean`](file:///home/gersh/leancompcert/LeanCompCert/CCIR/Basic.lean) and [`LeanCompCert/C/AST.lean`](file:///home/gersh/leancompcert/LeanCompCert/C/AST.lean)).

The primary Lean 4 theorem, `AProgram.evalCC_compile` (in [`LeanCompCert/Verified/ArrayState.lean`](file:///home/gersh/leancompcert/LeanCompCert/Verified/ArrayState.lean)), establishes semantic preservation:

$$\forall p : \text{AProgram},\; \text{hWF} : p.\text{WF},\; n : \mathbb{N}, \quad (p.\text{denote} = \text{some } n) \implies \text{evalC}(p.\text{compile}) = \text{some } n$$

```lean
theorem AProgram.evalCC_compile (p : AProgram) (hWF : p.WF) (base : Int)
    (hBase : BaseOk p.arrayLen base) (n : Nat) (hDenote : p.denote = some n) :
    Option.bind (evalMCCSequence (p.initialMCC base) p.compile)
      (fun m => m.env ⟨p.output + 1⟩) = some ((n : Nat) : Int)
```

**Proof Structure:**
1. **Operand Lowering:** [`lowerOperand_correct`](file:///home/gersh/leancompcert/LeanCompCert/Proof/PureSemantics.lean) proves operand translation preserves 64-bit integer values.
2. **Binary Operation Preservation:** [`lowerBinary_unsigned_correct`](file:///home/gersh/leancompcert/LeanCompCert/Proof/PureSemantics.lean) proves that arithmetic and bitwise operations match C evaluation under `u64` wrap-around semantics.
3. **Trace Induction:** [`lowerSequence_correct`](file:///home/gersh/leancompcert/LeanCompCert/Proof/PureSemantics.lean) lifts instruction-level correctness to arbitrary straight-line execution traces via structural induction over list length.
4. **Loop Preservation:** [`rolledTraceM_eq_foldTraceM`](file:///home/gersh/leancompcert/LeanCompCert/Verified/ArrayState.lean) connects the single-pass emitted C `while` loop to the mathematical fold over index range $0 \dots \text{loopCount}-1$.

### 3.2 Coq-Side Clight Semantics (The Clight Bridge - M6)

To avoid relying on a custom Lean-side C semantics parser, `lean-compcert` includes direct Clight AST emission ([`LeanCompCert/Verified/ClightEmit.lean`](file:///home/gersh/leancompcert/LeanCompCert/Verified/ClightEmit.lean)).

In Coq (`scripts/coq/ClightFragmentSem.v`), CompCert's formal `ClightBigstep.exec_stmt` semantics is evaluated over the emitted Clight AST:
* A computable fragment evaluator is proved sound against CompCert's official Coq big-step operational semantics.
* For each certificate, Coq’s kernel evaluates `eval_funcall` at `Qed` time, verifying that CompCert’s formal semantics yields the expected certified constant value.

---

## 4. The Complete Trust Model & Trusted Computing Base (TCB)

To evaluate the mathematical validity of a claim certified via `lean-compcert`, one must precisely delineate what is formally proved versus what is assumed.

```
+-----------------------------------------------------------------------------------+
|                                  THE TRUST MODEL                                  |
+---------------------------------------------------+-------------------------------+
|             FORMALLY PROVED IN LEAN/COQ           |   TRUSTED COMPUTING BASE      |
+---------------------------------------------------+-------------------------------+
| 1. High-level math => Reflected algorithm.        | 1. Lean 4 Kernel              |
| 2. Program.denote => Emitted C (evalCC_compile).  | 2. Coq Kernel                 |
| 3. Emitted Clight => CompCert Clight semantics.   | 3. CompCert Proof (Coq)       |
| 4. CompCert C => Target Assembly Text.            | 4. Assembler & Linker (as/ld) |
| 5. Zero-axiom core verification library.          | 5. Physical CPU & Hardware    |
+---------------------------------------------------+-------------------------------+
```

### 4.1 What Is Formally Proved

1. **Denotational Preservation:** Proved in Lean 4 that $p.\text{denote} = \text{some } n \implies \text{EmittedC}(p) \Downarrow n$.
2. **Coq Clight Evaluation:** Proved in Coq that CompCert’s operational semantics assigns the exact certified value to the emitted Clight representation.
3. **CompCert Middle-End Preservation:** Proved in Coq (by the CompCert development team) that Clight AST transformations down to target assembly text preserve program semantics.

### 4.2 What Is Outside the Formal Proof (The TCB)

1. **Lean 4 & Coq Kernels:** The fundamental proof-checker binaries must be trusted.
2. **Assembler & Linker (`as` / `ld` / `gcc`):** CompCert outputs assembly text (`.s`). Assembling text into machine code (`.o`) and linking binaries into ELFs relies on GNU `as`/`ld`.
   * *Mitigation:* `lean-compcert` uses **freestanding artifacts** (~1.3 kB) with zero unresolved dynamic library dependencies, drastically minimizing linker surface area.
3. **Physical Silicon & Operating System:** No formal logic can prove that hardware execution matches theoretical ISA specifications without physical fault.
4. **The Encoding Gap:** The theorem proving $p.\text{compile} \Downarrow n$ does not prove that $p.\text{denote}$ matches a high-level mathematical definition unless an explicit Lean equivalence proof is provided.

### 4.3 Axiom Policy & Opt-In Execution Admission

Core modules under `LeanCompCert/` maintain a **strict zero-axiom policy**. Running `#print axioms` on any core theorem yields only standard Lean logic axioms:

```lean
#print axioms LeanCompCert.Verified.Reflect.Program.evalCC_compile
-- Outputs: 'propext', 'Classical.choice', 'Quot.sound'
```

When an execution result cannot be re-derived inside the kernel due to scale, the run is admitted through an opt-in module ([`LeanCompCert/Trusted/ArtifactRun.lean`](file:///home/gersh/leancompcert/LeanCompCert/Trusted/ArtifactRun.lean)):

```lean
abbrev EvidencedRun : Prop :=
  ∀ (p : AProgram) (n : Nat) (e : RunEvidence),
    e.challenge.program = p →
    RunEvidence.verify e n = true →
    p.denote = some n

axiom evidencedRun_sound : EvidencedRun
```

Using the `evidenced_decide` tactic mints a unique, inspectable axiom per execution site (e.g., `myProof._evidenced.run.ax`), allowing auditors to audit admitted runs with a simple `grep`.

---

## 5. Practical Usage Guide in Lean 4

`lean-compcert` supports three distinct workflow routes depending on the target scale and trust requirements.

```
                       +-----------------------------------+
                       | Which route fits your computation?|
                       +-----------------------------------+
                                         |
                +------------------------+------------------------+
                |                                                 |
       [ Fits in Kernel ]                              [ Exceeds Kernel ]
        (< 10,000 steps)                               (> 100,000 steps)
                |                                                 |
                v                                                 v
        +---------------+                               +-------------------+
        |    ROUTE A    |                               | Is re-running     |
        |  Kernel-Only  |                               | practical in CI?  |
        | (decide+kernel|                               +-------------------+
        +---------------+                                 |               |
                                                         Yes              No
                                                          |               |
                                                          v               v
                                                  +---------------+ +---------------+
                                                  |    ROUTE B    | |    ROUTE C    |
                                                  | CompCert Native| | Opt-In Axiom |
                                                  | (check-native)| | (evidenced)   |
                                                  +---------------+ +---------------+
```

### 5.1 Route A: Pure Kernel Reflection (`decide +kernel`)

For small to medium computations ($\le 10^4$ operations), evaluate the denotation directly in Lean's kernel.

```lean
import LeanCompCert.Verified.Reflect

open LeanCompCert.Verified.Reflect

-- 1. Construct the register program
def myProgram : Program := {
  regCount  := 3,
  loopCount := 100,
  init      := [Instr.mov 0 (Operand.lit 0)],
  body      := [Instr.binop 0 Op.add (Operand.reg 0) (Operand.lit 1)],
  epilogue  := [],
  output    := 0
}

-- 2. Prove correctness entirely inside the kernel
theorem myProgram_result : myProgram.denote = some 100 := by
  decide +kernel
```

### 5.2 Route B: Reproducible Verified Compiled Artifact (`check-native`)

For large computations ($10^5 - 10^{10}$ operations), prove compilation soundness in Lean and cross-check execution using CompCert binaries.

```lean
import LeanCompCert.Verified.ArrayState

open LeanCompCert.Verified.ArrayState

-- 1. Define executable program
def largeSweepProgram : AProgram := ...

-- 2. Prove program is well-formed
theorem largeSweep_wf : largeSweepProgram.WF := by
  decide

-- 3. Apply compilation soundness theorem
theorem largeSweep_compiled (base : Int) (hBase : BaseOk largeSweepProgram.arrayLen base) :
    ∃ n, Option.bind (evalMCCSequence (largeSweepProgram.initialMCC base) largeSweepProgram.compile)
      (fun m => m.env ⟨largeSweepProgram.output + 1⟩) = some ((n : Nat) : Int) := by
  exact ⟨_, AProgram.evalCC_compile largeSweepProgram largeSweep_wf base hBase _ rfl⟩
```

Register the program in `Main.lean` and execute the native verification runner:

```bash
lake exe lean-compcert check-native --force
```

### 5.3 Route C: Opt-In Execution Admission (`evidenced_decide`)

For massive computations where kernel evaluation is infeasible and CI re-execution is too expensive:

```lean
import LeanCompCertTrusted

open LeanCompCert.Trusted

-- Admit execution via named receipt
theorem heavyComputation_ok : myHeavyProgram.denote = some 42 := by
  evidenced_decide myRunEvidence
```

Auditing axioms will display the exact admitted execution:

```lean
#print axioms heavyComputation_ok
-- Output includes: heavyComputation_ok._evidenced.run.ax
```

---

## 6. Known Performance Limits & Open Challenges

### 6.1 The M8 Denotation Performance Gap

As documented in Milestone M8 of [`ROADMAP.md`](file:///home/gersh/leancompcert/ROADMAP.md), `RegState` is represented functionally as $\text{RegState} = \mathbb{N} \to \mathbb{N}$ with functional updates (`RegState.set`). Consequently:
* Reading a register requires traversing a closure chain proportional to the number of prior writes.
* Evaluated inside Lean's kernel interpreter, unrolled program denotations exhibit **$O(N^2)$ time complexity** relative to loop trip count $N$.

**Workaround & Mitigation:** For production fold certificates, developers chunk high-level reference functions directly (`List.foldl`) and prove equivalence to `Program.denote` algebraically rather than evaluating unrolled register states in the kernel.

---

## 7. Conclusion

`lean-compcert` establishes a practical, machine-checked framework for verified computation in Lean 4. By coupling a restricted register-machine DSL with Lean 4 compilation proofs and Coq-verified CompCert Clight semantics, it delivers native execution speeds while preserving Lean’s kernel trust guarantees.

---

## References

1. Xavier Leroy. *Formal verification of a realistic compiler.* Communications of the ACM, 52(7):107–115, 2009.
2. Leonardo de Moura and Sebastian Ullrich. *The Lean 4 Theorem Prover and Programming Language.* Automated Reasoning (IJCAR 2021).
3. [lean-compcert Codebase and Documentation Repository](file:///home/gersh/leancompcert).
