Below is a build-oriented specification for an initial Lean-to-CompCert backend. The first release targets CompCert-compatible C rather than generating CompCert’s internal Clight AST directly. This keeps the project independently usable while leaving a clear path toward verified LCNF-to-Clight compilation.

Lean–CompCert Backend Specification

Working name: lean-compcert
Status: Proposed
Initial target: Lean 4.30 or later and CompCert 3.17
Primary objective: Compile Lean programs into CompCert-compatible C and use CompCert to produce native executables.

1. Executive summary

lean-compcert is an alternative Lean 4 native-code backend that lowers Lean’s compiler intermediate representation into a restricted C dialect accepted by CompCert.

The initial compilation pipeline is:

Lean source
    ↓
Elaboration and kernel checking
    ↓
Lean compiler frontend
    ↓
LCNF
    ↓
lean-compcert lowering
    ↓
CompCert-compatible C
    ↓
CompCert ccomp
    ↓
Assembly and native executable

Lean 4’s newer compiler pipeline is based on LCNF, and the LCNF backend was completed in Lean 4.30 with explicit borrow annotations. (⁠Lean Language)

CompCert accepts a large, but not unlimited, subset of ISO C and produces code for ARM, PowerPC, RISC-V, and x86 targets. Its verified guarantee covers semantic preservation from an accepted CompCert C program to the generated assembly. (⁠CompCert)

The first release does not claim end-to-end verified compilation from Lean source. Its assurance boundary is:

Lean source
    │
    │ Existing Lean frontend and lean-compcert backend
    │ Not initially formally verified
    ▼
CompCert C
    │
    │ CompCert semantic-preservation theorem
    ▼
Assembly

A later project phase may replace textual C emission with direct generation of CompCert Clight syntax and establish a semantic-preservation proof from a formally specified Lean subset.

⸻

2. Goals

2.1 Primary goals

The backend shall:

1. Compile a useful subset of executable Lean 4 programs with CompCert.
2. consume Lean’s LCNF representation after standard frontend transformations;
3. generate deterministic, readable, CompCert-compatible C;
4. use the existing Lean object representation and runtime where practical;
5. isolate runtime features that are incompatible with CompCert;
6. reject unsupported Lean features with precise diagnostics;
7. integrate with Lake as an alternative native backend;
8. support differential testing against Lean’s standard C backend;
9. preserve ordinary Lean calling conventions at supported FFI boundaries;
10. establish an architecture suitable for later formal verification.

2.2 Secondary goals

The backend should:

* support reproducible builds;
* support separate compilation of Lean modules;
* emit source maps or symbol mappings from generated C to Lean declarations;
* minimize compiler-specific C extensions;
* permit mixed builds containing CompCert-compiled and conventionally compiled modules;
* expose generated C and intermediate lowering stages for inspection;
* support a “strict verified-C profile” with tighter restrictions than ordinary CompCert C.

2.3 Non-goals for the first release

Version 1 will not attempt to:

* verify Lean elaboration;
* verify Lean’s kernel implementation;
* verify all LCNF optimization passes;
* prove the LCNF-to-C translation correct;
* compile the entire Lean compiler with CompCert;
* support arbitrary C or C++ FFI libraries;
* support all platform-specific portions of Lean’s runtime;
* support JavaScript or WebAssembly output;
* reproduce every optimization performed by Clang or LLVM;
* support unrestricted concurrency;
* support arbitrary unsafe declarations;
* establish that a theorem proved in Lean remains true because its executable code was compiled by CompCert.

Proof checking and executable-code generation are related but distinct trust boundaries.

⸻

3. User-facing behavior

3.1 Lake configuration

The intended package configuration is:

package verifiedExample where
  nativeBackend := .compcert
lean_compcert where
  ccomp := "/opt/CompCert/ccomp"
  profile := "portable"
  runtime := "hybrid"

If extending Lake.Backend upstream is not initially practical, the prototype shall use a post-build driver:

lake lean-compcert build

or:

lake env lean-compcert \
  --input .lake/build/ir/MyModule \
  --output .lake/build/compcert

Lake currently exposes standard C, LLVM, and default backend selections. The project may therefore begin as an external Lake facet or executable before proposing an upstream .compcert backend value. (⁠Lean Language)

3.2 Direct command-line interface

lean-compcert build Main.lean
lean-compcert emit-c Main.lean
lean-compcert compile-ir Main
lean-compcert check-runtime
lean-compcert doctor

Representative options:

--ccomp PATH
--target TARGET
--profile portable|hosted|strict
--runtime hybrid|compcert|external
--emit-c DIR
--emit-lowered-ir DIR
--keep-temporaries
--debug-symbols
--opt-level 0|1|2
--differential-check
--reject-unsafe
--report FILE

3.3 Failure diagnostics

Unsupported constructs must produce structured diagnostics:

error: declaration `Worker.start` requires unsupported runtime feature `thread`
  Lean declaration:
    Worker.start
  Lowered primitive:
    lean_spawn_task
  Current profile:
    strict
  Supported alternatives:
    - compile this module with the standard Lean backend;
    - use the hybrid runtime profile;
    - refactor the function to avoid task creation.

The backend must not silently replace unsupported semantics with approximate behavior.

⸻

4. Architecture

4.1 Components

The repository shall contain the following logical components:

LeanCompCert/
  Driver/
  LCNF/
  Lower/
  C/
  Runtime/
  ABI/
  Diagnostics/
  Testing/
  Lake/
runtime/
  include/
  portable/
  adapters/
  platform/
tools/
  ccomp-driver/
  differential-runner/
  compatibility-scanner/
tests/
  compile/
  runtime/
  negative/
  differential/
  ffi/

Component responsibilities

Driver

* load compiled Lean modules;
* invoke the necessary Lean compiler passes;
* obtain normalized LCNF;
* construct whole-module compilation metadata;
* invoke lowering, C emission, CompCert, and linking.

LCNF

* provide a stable internal view of the Lean LCNF structures used by the backend;
* shield most backend code from Lean compiler API changes;
* perform backend-specific validation;
* assign stable identifiers to functions, blocks, variables, and declarations.

Lower

* normalize LCNF into a smaller backend IR;
* make control flow explicit;
* lower closures, constructors, projections, primitives, and calls;
* insert runtime operations;
* resolve tail calls;
* classify unsupported operations.

C

* model a restricted CompCert-compatible C AST;
* validate that generated constructs belong to the supported C subset;
* emit deterministic C source;
* emit declarations, headers, symbol maps, and compilation manifests.

Runtime

* provide CompCert-compatible implementations or adapters for Lean runtime services;
* classify runtime functions by trust and compiler boundary;
* provide a reduced portable runtime for strict builds.

ABI

* define object layouts, calling conventions, symbol naming, initialization, and module boundaries;
* generate static assertions where accepted;
* prevent ABI drift between generated modules and runtime components.

Diagnostics

* map failures to Lean declarations and source positions where possible;
* generate human-readable and machine-readable build reports.

Testing

* generate test programs;
* compile with both standard Lean and CompCert backends;
* compare observable behavior;
* run runtime invariant and ABI tests.

⸻

5. Input boundary

5.1 Backend input

The backend shall consume LCNF after the following conceptual transformations have occurred:

* erasure of proof-only content;
* specialization as selected by the Lean frontend;
* lambda lifting or closure preparation;
* pattern-match lowering;
* primitive resolution;
* compiler normalization required by the active Lean version.

The backend shall not parse Lean source itself.

5.2 Compiler API adapter

Because Lean compiler internals may change between releases, the project shall isolate all direct references to Lean’s compiler APIs behind:

namespace LeanCompCert.CompilerAdapter
def loadModule ...
def compileToLCNF ...
def declarationSourceInfo ...
def compilerVersion ...
def runtimeVersion ...
end LeanCompCert.CompilerAdapter

Each supported Lean version shall have either:

* a separate adapter module; or
* a version-gated implementation.

The backend must reject unknown Lean compiler versions unless the user explicitly selects an experimental compatibility mode.

⸻

6. Backend intermediate representation

6.1 Purpose

A backend-specific IR, called CCIR, shall sit between LCNF and C.

LCNF → CCIR → CompCert C AST → C text

CCIR reduces dependence on both Lean’s internal representation and C syntax.

6.2 CCIR properties

CCIR shall be:

* first-order;
* explicitly typed at machine level;
* statement-oriented;
* control-flow explicit;
* free of nested expressions with observable effects;
* explicit about allocation and reference-count operations;
* explicit about exceptional or non-returning operations;
* explicit about external calls;
* easy to interpret for testing;
* suitable for a future operational semantics.

6.3 Representative CCIR types

inductive CCType
  | void
  | u8
  | u16
  | u32
  | u64
  | usize
  | i8
  | i16
  | i32
  | i64
  | isize
  | f32
  | f64
  | obj
  | ptr (element : CCType)
  | fnPtr (args : Array CCType) (result : CCType)
inductive Operand
  | local (id : LocalId)
  | global (id : GlobalId)
  | uintLit (type : CCType) (value : Nat)
  | intLit (type : CCType) (value : Int)
  | null (type : CCType)
inductive Statement
  | assign
  | unary
  | binary
  | load
  | store
  | call
  | runtimeCall
  | retain
  | release
  | allocCtor
  | getTag
  | project
  | branch
  | switch
  | goto
  | return
  | unreachable

6.4 ANF requirement

All effectful and potentially trapping operations shall occur in separate statements.

Forbidden:

x = f(g(), h());

Required:

t1 = g();
t2 = h();
x = f(t1, t2);

This simplifies evaluation-order reasoning and prevents reliance on unspecified C operand-evaluation order.

⸻

7. Lean value representation

7.1 Compatibility strategy

Version 1 should retain Lean’s existing native object representation wherever it can be documented and reproduced safely.

The supported representation must cover:

* scalar machine integers;
* boxed natural numbers and integers;
* constructor objects;
* arrays;
* strings;
* closures;
* thunks where required;
* reference-counted heap objects;
* scalar constructors encoded directly in object words, if used by the selected Lean runtime ABI.

7.2 ABI manifest

The build must produce or consume a versioned ABI manifest:

{
  "leanVersion": "4.30.0",
  "pointerBits": 64,
  "endianness": "little",
  "objectAlignment": 8,
  "scalarTagBits": 1,
  "closureLayoutVersion": 1,
  "runtimeAbiHash": "..."
}

The backend shall fail compilation when the active runtime does not match the expected manifest.

7.3 Representation invariants

The implementation must document invariants including:

1. every object pointer is correctly aligned;
2. immediate scalar values are distinguishable from pointers;
3. constructor tags fit within the runtime’s tag representation;
4. object field accesses stay within allocated layouts;
5. closures carry the expected function pointer and environment fields;
6. reference-count operations apply only to representations that require them;
7. unboxed values are never passed where boxed values are expected;
8. no generated code fabricates a pointer from an arbitrary integer;
9. casts preserve representation and alignment assumptions;
10. null values occur only where the ABI permits null.

⸻

8. Lowering rules

8.1 Functions

Each compiled Lean function shall become one C function with a stable mangled name.

Example:

def Example.addOne (n : UInt64) : UInt64 :=
  n + 1

Conceptual output:

uint64_t l_Example_addOne(uint64_t n) {
    return n + UINT64_C(1);
}

8.2 Constructors

Constructor creation shall lower to either:

* an immediate scalar representation; or
* a runtime allocation followed by ordered field stores.

Conceptual CCIR:

p = alloc_ctor(tag = 2, fields = 3)
store_field p 0 x
store_field p 1 y
store_field p 2 z
return p

Generated C shall not rely on struct-layout aliasing unless the ABI explicitly defines that layout.

8.3 Pattern matching

Pattern matching shall lower to:

1. constructor-tag extraction;
2. a C switch, or equivalent branches;
3. checked field projections within the matching case.

There shall be no C default case when all source constructors are represented explicitly unless the default invokes a defined unreachable/error routine.

8.4 Closures

Closure conversion shall use the runtime ABI’s closure representation.

Each closure call shall be lowered through either:

* a statically known function call; or
* a runtime-compatible indirect-call helper selected by arity.

Indirect calls must use function-pointer types compatible with the called function. The backend must not rely on incompatible function-pointer casts.

8.5 Tail calls

Version 1 shall preserve semantic tail recursion without requiring a compiler-specific tail-call attribute.

Strategies, in order of preference:

1. translate direct self-tail recursion into a C loop;
2. translate mutually recursive tail calls into a dispatcher loop when practical;
3. use ordinary calls where stack use is acceptable;
4. reject programs requiring guaranteed bounded-stack tail calls when no transformation applies.

The backend shall not assume CompCert performs tail-call optimization unless guaranteed for the relevant source form and target.

8.6 Primitive arithmetic

Fixed-width integer operations shall use explicitly sized unsigned types wherever modular arithmetic is intended.

Signed overflow must never be used to implement Lean semantics.

For example:

uint64_t r = x + y;

may implement modular UInt64 addition.

Operations on signed integers must avoid undefined signed overflow by using:

* unsigned arithmetic and representation-preserving conversion;
* checked helper functions;
* wider intermediate types when justified;
* runtime big-integer operations.

8.7 Natural numbers and integers

Small-value arithmetic may use immediate runtime representations.

Large values shall use runtime functions.

The backend must not duplicate big-number algorithms in generated code during the first release.

8.8 Floating point

The portable profile may support Float only when:

* the target CompCert configuration supports the required floating-point operations;
* the runtime and generated C agree on representation;
* the backend documents that cross-compiler differential results may differ for NaNs, payloads, exceptional states, or unspecified library functions.

A strict deterministic profile may initially reject floating-point operations.

8.9 Exceptions and panics

Lean-level panic, unreachable, and fatal-error paths shall lower to explicit non-returning runtime functions.

Generated C must not communicate exceptions through undefined behavior.

8.10 IO

IO α shall use the existing compiled Lean representation and calling convention where possible.

Version 1 must support at least:

* IO.pure;
* sequencing;
* standard output;
* standard error;
* process exit;
* command-line arguments;
* basic file reads and writes, in the hosted profile.

Concurrency, asynchronous tasks, timers, sockets, and platform event loops may be deferred.

⸻

9. C subset and coding restrictions

9.1 Generated-language profile

The generated C shall conform to a project-defined subset called Lean CompCert C Profile 1.

Profile 1 shall prohibit generated use of:

* variable-length arrays;
* unsequenced side effects;
* signed integer overflow;
* pointer arithmetic outside allocated objects;
* incompatible function-pointer calls;
* type-punning through pointer casts;
* dependence on struct padding contents;
* dependence on unspecified argument-evaluation order;
* statement expressions;
* nested functions;
* computed goto;
* inline assembly;
* compiler-specific vector extensions;
* thread-local storage;
* C++ constructs;
* exceptions;
* arbitrary pragmas;
* atomics, unless separately supported and tested;
* undefined behavior as an optimization device.

CompCert accepts most ISO C with defined exceptions and selected extensions, but the project’s emitted subset should be substantially narrower than CompCert’s complete accepted language. (⁠CompCert)

9.2 Generated C AST

The emitter shall not concatenate arbitrary source strings.

It shall emit from a typed internal C AST:

inductive CType
inductive CExpr
inductive CStmt
structure CFunction
structure CGlobal
structure CTranslationUnit

A validation pass shall run before pretty-printing.

9.3 C validation

Validation errors shall include:

* generated node;
* originating CCIR instruction;
* originating Lean declaration;
* violated profile rule.

9.4 External syntax validation

As a test-stage check, generated files should be accepted by:

ccomp -c generated.c

Where available, the project may also run CompCert’s Clight export tooling to confirm that generated C can be translated into CompCert’s formal syntax. CompCert includes an experimental clightgen tool for translating C into Clight or Csyntax represented in Coq. (⁠GitHub)

⸻

10. Runtime strategy

10.1 Runtime modes

The backend shall provide three runtime modes.

Hybrid mode

Generated application modules are compiled with CompCert. The standard Lean runtime is compiled with its supported conventional compiler.

Lean-generated modules: CompCert
Lean runtime: Clang or GCC
System libraries: platform toolchain

This is the easiest compatibility milestone but does not put the runtime under CompCert’s guarantee.

CompCert mode

Generated modules and all compatible runtime modules are compiled with CompCert.

Incompatible platform adapters may remain conventionally compiled.

Strict mode

Generated modules use a reduced runtime whose CompCert-compatible source is maintained by the project.

Unsupported runtime features are rejected.

10.2 Runtime inventory

Every referenced runtime symbol shall be classified:

COMPATIBLE
ADAPTED
EXTERNAL_TRUSTED
UNSUPPORTED

The inventory shall be machine-readable:

lean_alloc_ctor:
  status: compatible
  source: runtime/portable/alloc.c
lean_dec_ref:
  status: compatible
  source: runtime/portable/refcount.c
lean_spawn_task:
  status: unsupported
  reason: requires threads and synchronization
lean_get_stdin:
  status: external_trusted
  source: platform POSIX adapter

10.3 Runtime compatibility scanner

The project shall provide:

lean-compcert check-runtime

This command shall:

1. enumerate runtime source files;
2. attempt CompCert preprocessing and compilation;
3. classify failures;
4. detect unsupported headers and extensions;
5. generate a compatibility report;
6. record the exact CompCert target and version.

10.4 External libraries

System and third-party libraries remain outside CompCert’s correctness theorem unless separately compiled and verified.

The final build report shall list:

CompCert-compiled:
  Main.c
  Example_Arithmetic.c
  lean_runtime_refcount.c
Conventionally compiled:
  lean_platform_posix.c
  libc
  libm
Dynamically linked:
  libc.so

⸻

11. FFI policy

11.1 Supported FFI

Version 1 may support C FFI declarations satisfying all of the following:

* ABI-compatible scalar, pointer, or documented runtime-object parameters;
* no C++ exceptions;
* no variadic functions unless handled by an approved wrapper;
* no callback with an incompatible function-pointer type;
* no ownership ambiguity;
* no untracked long jumps;
* no thread entry into Lean without a supported runtime adapter.

11.2 FFI descriptors

Each external function should have a generated or manually supplied descriptor:

structure ForeignSpec where
  symbol : String
  args : Array ForeignType
  result : ForeignType
  ownership : OwnershipSpec
  effects : EffectSpec
  trusted : Bool

11.3 Unsafe declarations

Profiles shall behave as follows:

* hosted: allow approved unsafe declarations and FFI;
* portable: allow only backend-recognized unsafe primitives;
* strict: reject user unsafe declarations unless explicitly allowlisted.

⸻

12. CompCert driver integration

12.1 Driver executable

A dedicated driver shall translate project options into ccomp invocations.

lean-ccomp-driver \
  --target x86_64-linux \
  --input Module.c \
  --output Module.o \
  --manifest Module.json

CompCert’s normal command-line compiler is ccomp. (⁠CompCert)

12.2 No blind compiler substitution

The project must not simply set LEAN_CC=ccomp and assume compatibility with all flags produced for Clang or GCC.

The driver shall:

* accept a controlled argument set;
* reject unknown options;
* translate supported optimization flags;
* manage include paths;
* generate dependency files itself when necessary;
* invoke the platform linker through an explicit, documented path;
* record exact invocations in the build manifest.

12.3 Linking

Linking shall be treated as a separate trust stage.

The build report must distinguish:

* verified CompCert compilation;
* assembly;
* assembler execution;
* linker execution;
* startup objects;
* system libraries.

No claim of end-to-end verification may omit these boundaries.

⸻

13. Module initialization and separate compilation

13.1 Separate compilation

Each Lean module shall produce:

Module.c
Module.h
Module.o
Module.compmanifest.json
Module.symmap.json

13.2 Symbol naming

Symbols shall be:

* deterministic;
* collision-resistant;
* valid C identifiers;
* stable within a defined backend ABI version.

Example:

Lean declaration: Data.Tree.map
C symbol:         l_Data_Tree_map

Characters not valid in C identifiers shall be escaped using a specified encoding.

13.3 Initialization

Module initialization shall preserve Lean’s dependency ordering.

The backend shall generate:

lean_object *initialize_Data_Tree(
    uint8_t builtin,
    lean_object *world);

or an ABI-equivalent form matching the selected runtime.

Initialization must be idempotent if the standard Lean ABI requires idempotence.

⸻

14. Correctness strategy

14.1 Version 1 assurance claim

Version 1 may claim only:

For generated C accepted by CompCert, the C-to-assembly portion of compilation receives CompCert’s semantic-preservation guarantee, subject to CompCert’s assumptions and the behavior of external functions.

It must not claim:

Lean source semantics are formally preserved into assembly.

14.2 Executable CCIR semantics

CCIR shall receive an interpreter early in development.

def CCIR.eval :
  Program → EntryPoint → Array Value → IO EvalResult

This enables three-way comparisons:

Lean evaluator result
CCIR interpreter result
CompCert executable result

14.3 Future semantic theorem

The long-term proof target is:

If:
  LCNF program P evaluates with observable behavior B,
and:
  lower(P) = Q,
and:
  emit(Q) = C,
then:
  C has observable behavior corresponding to B.

This should eventually be decomposed into:

1. LCNF-to-CCIR simulation;
2. CCIR-to-Clight simulation;
3. ABI representation correspondence;
4. runtime primitive specifications;
5. use of CompCert’s Clight-to-assembly correctness theorem.

CompCert states its high-level correctness theorem as preservation of observable behavior from source to generated code when compilation succeeds. (⁠CompCert)

14.4 Direct Clight backend

After the C backend stabilizes, the project may add:

LCNF → CCIR → Clight AST

rather than:

LCNF → CCIR → C text → CompCert parser → Clight

Advantages include:

* no reliance on C parsing;
* exact construction of formal CompCert syntax;
* simpler proof statement;
* elimination of ambiguity in C pretty-printing;
* direct access to CompCert’s formal semantics.

This is a second-generation backend and not required for the first usable release.

⸻

15. Testing requirements

15.1 Unit tests

Unit tests shall cover:

* name mangling;
* type lowering;
* arithmetic lowering;
* constructor allocation;
* projection;
* closure construction;
* direct calls;
* indirect calls;
* recursion;
* tail recursion;
* reference-count insertion;
* module initialization;
* FFI descriptors;
* C AST validation;
* diagnostics.

15.2 Golden C tests

Selected Lean inputs shall have reviewed generated-C snapshots.

Golden tests must normalize:

* temporary identifiers;
* absolute paths;
* compiler-version strings when appropriate.

15.3 Differential tests

Each differential test shall:

1. compile the Lean program with the standard Lean C backend;
2. compile it with lean-compcert;
3. run both with identical inputs;
4. compare:
    * standard output;
    * standard error;
    * exit status;
    * generated data files where applicable.

15.4 Property-based tests

Automatically generated tests should cover:

* UInt8, UInt16, UInt32, and UInt64 arithmetic;
* comparisons;
* shifts;
* constructor/tag round trips;
* arrays;
* lists;
* trees;
* recursive traversals;
* closure capture;
* partial application;
* reference-count stress.

15.5 Memory tests

Where compatible tooling is available, runtime tests should check:

* leaks;
* double frees;
* use after free;
* invalid field access;
* reference-count underflow;
* incorrect scalar/pointer classification.

Because external memory-checking tools are outside the verified compilation path, their results are testing evidence, not formal proof.

15.6 Negative tests

Compilation must fail predictably for:

* unsupported concurrency;
* unsupported intrinsics;
* incompatible FFI declarations;
* unsupported inline assembly;
* ABI mismatch;
* unknown runtime symbol;
* strict-profile unsafe code;
* unsupported target;
* CompCert-rejected generated constructs.

15.7 Miscompilation corpus

The project should maintain small adversarial tests involving:

* evaluation order;
* aliasing;
* integer boundaries;
* signed and unsigned conversions;
* shifts by boundary amounts;
* deep recursion;
* closure arity;
* constructor tags;
* zero-sized or empty structures;
* reference-count ownership transfer.

⸻

16. Performance requirements

Version 1 prioritizes correctness and compatibility over peak performance.

Nevertheless, the backend shall measure:

* compile time;
* generated C size;
* object-code size;
* runtime against Lean’s standard C backend;
* allocation count;
* reference-count operation count;
* maximum stack depth for transformed tail recursion.

Initial acceptance thresholds:

* compilation succeeds for at least 90% of the designated portable test suite;
* generated executable runtime is no more than 5× the standard backend on geometric-mean benchmark time;
* object-code size is no more than 5× on the same suite;
* direct self-tail-recursive tests execute in bounded stack space;
* no unexplained differential-test failures.

These are project targets, not properties guaranteed by CompCert.

⸻

17. Build manifest and provenance

Every build shall produce a manifest containing:

{
  "leanVersion": "4.30.0",
  "leanGitRevision": "...",
  "backendVersion": "0.1.0",
  "backendGitRevision": "...",
  "compcertVersion": "3.17",
  "compcertTarget": "x86_64-linux",
  "runtimeMode": "hybrid",
  "runtimeAbiHash": "...",
  "profile": "portable",
  "modules": [],
  "externalObjects": [],
  "systemLibraries": [],
  "unsupportedFeatures": [],
  "compilerCommands": []
}

The manifest shall make it possible to determine exactly which components were and were not compiled by CompCert.

⸻

18. Security and trust model

18.1 Trusted components in version 1

The trusted computing base includes:

* Lean elaborator and compiler frontend;
* Lean kernel implementation for proof checking;
* LCNF passes used before the backend;
* the lean-compcert lowering implementation;
* C emission and printing;
* the Lean runtime or reduced runtime;
* external FFI implementations;
* CompCert assumptions and extracted compiler executable;
* assembler;
* linker;
* target hardware and operating system.

18.2 Reduced trust from CompCert

The project reduces dependence on unverified optimizing C compilers for generated Lean application code.

It does not eliminate the other components listed above.

18.3 Reproducibility

Strict builds should support:

* pinned Lean and CompCert versions;
* deterministic generated C;
* deterministic manifests;
* containerized or Nix-based development environments;
* source hashes for runtime files;
* optional comparison of independently produced object files.

⸻

19. Development milestones

Milestone 0: Compatibility reconnaissance

Deliverables:

* runtime-source inventory;
* automated attempts to compile Lean-generated C with CompCert;
* catalog of rejected C constructs;
* catalog of unsupported compiler flags;
* minimal “hello world” result, if possible;
* written ABI notes.

Exit criterion:

A report identifies whether existing Lean-emitted C can be adapted directly or requires a new emitter.

Milestone 1: Pure first-order subset

Supported:

* fixed-width integers;
* booleans;
* first-order functions;
* direct calls;
* conditionals;
* loops;
* self-recursion without heap allocation.

Deliverables:

* LCNF reader;
* CCIR;
* C AST;
* CompCert driver;
* differential test suite.

Exit criterion:

At least 100 pure arithmetic and control-flow tests pass under both backends.

Milestone 2: Inductive values and allocation

Supported:

* constructors;
* pattern matching;
* products;
* options;
* lists;
* trees;
* basic natural numbers.

Deliverables:

* runtime allocation integration;
* constructor ABI;
* tag and projection lowering;
* reference-count operations.

Exit criterion:

Allocation-heavy recursive programs pass differential and memory tests.

Milestone 3: Closures

Supported:

* higher-order functions;
* lambda capture;
* partial application;
* closure invocation.

Exit criterion:

Map, fold, composition, captured environments, and mixed-arity closure tests pass.

Milestone 4: Basic IO

Supported:

* console output;
* command-line arguments;
* file input and output;
* process exit.

Exit criterion:

A nontrivial command-line Lean application builds and runs through CompCert.

Milestone 5: Lake integration

Deliverables:

* Lake facet or backend integration;
* incremental builds;
* module dependency handling;
* package-level configuration;
* build manifest.

Exit criterion:

A normal multi-module Lake package builds with one documented command.

Milestone 6: CompCert-compatible runtime subset

Deliverables:

* portable allocation and reference-count runtime;
* CompCert-compiled runtime modules;
* compatibility matrix;
* strict profile.

Exit criterion:

A useful standalone subset builds without conventionally compiled Lean runtime modules, apart from documented system adapters.

Milestone 7: Formal semantics

Deliverables:

* formal CCIR syntax;
* operational semantics;
* executable interpreter;
* representation relation;
* statement of LCNF-to-CCIR correctness theorem.

Exit criterion:

Correctness is proved for a small first-order subset.

Milestone 8: Direct Clight emission

Deliverables:

* Clight AST generator;
* no textual C parse in the verified path;
* proof connection to CompCert source semantics.

Exit criterion:

One nontrivial Lean subset program has a machine-checked LCNF/CCIR-to-Clight simulation proof and is compiled by CompCert.

⸻

20. Initial repository plan

lean-compcert/
├── LeanCompCert.lean
├── LeanCompCert/
│   ├── Main.lean
│   ├── Config.lean
│   ├── Driver.lean
│   ├── CompilerAdapter.lean
│   ├── LCNF/
│   │   ├── View.lean
│   │   ├── Validate.lean
│   │   └── Pretty.lean
│   ├── CCIR/
│   │   ├── Basic.lean
│   │   ├── Type.lean
│   │   ├── Validate.lean
│   │   ├── Interpreter.lean
│   │   └── Pretty.lean
│   ├── Lower/
│   │   ├── Function.lean
│   │   ├── Constructor.lean
│   │   ├── Closure.lean
│   │   ├── Primitive.lean
│   │   └── Module.lean
│   ├── C/
│   │   ├── AST.lean
│   │   ├── Validate.lean
│   │   ├── Emit.lean
│   │   └── Profile.lean
│   ├── ABI/
│   │   ├── Manifest.lean
│   │   ├── Layout.lean
│   │   └── Symbols.lean
│   ├── Runtime/
│   │   ├── Inventory.lean
│   │   └── Symbols.lean
│   └── Lake/
│       └── Facet.lean
├── runtime/
│   ├── include/
│   ├── portable/
│   ├── adapters/
│   └── inventory.yaml
├── scripts/
├── tests/
├── lakefile.lean
├── lean-toolchain
└── README.md

⸻

21. First implementation task

The first coding task should not be the full backend.

It should be a reconnaissance tool:

lean-compcert-probe Main.lean

The tool shall:

1. ask Lean to emit the ordinary generated C;
2. run CompCert preprocessing and compilation on each generated file;
3. capture all failures;
4. classify failures into:
    * command-line incompatibility;
    * unsupported C syntax;
    * unsupported attribute;
    * unsupported header;
    * runtime dependency;
    * assembler or linker issue;
5. produce a minimized report;
6. optionally attempt mechanical rewrites;
7. compile and run the result when successful;
8. compare output with the ordinary Lean build.

This determines how much of Version 1 can reuse Lean’s existing C emission and how much requires a dedicated LCNF-to-C emitter.

⸻

22. Version 0.1 acceptance test

Version 0.1 is complete when the following program, plus equivalent tests involving lists and closures, compiles and runs with CompCert:

def sum : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + sum xs
def transform (k : UInt64) : List UInt64 → List UInt64 :=
  List.map fun x => x * k + 1
def main : IO Unit := do
  let xs := transform 3 [1, 2, 3, 4, 5]
  IO.println (sum xs)

The build must:

* use CompCert for every generated application module;
* produce the expected result;
* match the standard Lean backend’s output and exit status;
* produce a build manifest;
* list every non-CompCert runtime or system component;
* contain no unsupported generated-C profile construct;
* pass reference-count and allocation stress tests;
* be reproducible from pinned source revisions.

⸻

23. Final project success criteria

The project is successful at its initial engineering objective when it can compile a substantial class of ordinary Lean command-line applications using CompCert for all generated application code.

The project reaches its stronger research objective only when there is a machine-checked semantic bridge:

Lean executable semantics
        ↓ proof
LCNF or formally defined source subset
        ↓ proof
CCIR
        ↓ proof
Clight
        ↓ existing CompCert proof
Assembly semantics

Until that bridge exists, the backend should accurately describe itself as:

A Lean native backend that emits CompCert-compatible code and obtains CompCert’s verified C-to-assembly compilation guarantee.

It should not describe itself as:

A formally verified compiler from Lean to machine code.

The best immediate starting point is Milestone 0, because it will establish whether a new LCNF emitter is actually necessary or whether Lean’s existing C output can first be normalized into the restricted profile.
