# The program ledger

*Which compiled programs exist, what is inside each one, and which have actually
been run.*

The rest of this package answers "is this receipt bound to this computation?".
It did not answer the two questions a reviewer asks first — what does this
binary compute, and has it run — and there was no single place to look. The
ledger is that place.

Two verbs, over a registry that is ordinary Lean data:

```
lake exe lean-compcert ledger [--json] [check-native options]
lake exe lean-compcert describe NAME [--full] [--source]
```

Nothing in the machinery names a certificate, a campaign or a project. The
registry in `LeanCompCert/Main.lean` is *this* repository's; `claude_math` and
`gpu_prover` write their own list of the same type and get the same two verbs.

---

## 1. The three states, and why they are three columns

A green row in a build log usually means "it worked". Here it can mean three
independent things.

| state | what it means | evidence the ledger reads |
| --- | --- | --- |
| **compiled** | `ccomp` accepted this exact C text | a run record saying so |
| **run** | the binary executed and its self-check agreed | a *current* stamp, and a run record whose outcome is `agrees` |
| **chain proved** | a proved Lean arrow runs from this program's computation to a mathematical proposition | a `ChainProof`, which does not typecheck unless the arrow exists |

They are independent **in both directions**, and this repository contains an
example of each.

* `rolled-10m` is compiled and run, and nothing in Lean says what the number it
  reports means. A green run there bears on no mathematics whatsoever.
* `algorithm-sumrange` in a fresh checkout is chain proved and neither compiled
  nor run.

Collapsing them is a real failure mode, not a hypothetical one. Downstream, an
artifact that computed ψ was registered alongside a Lean certificate that
checked a fixed-point upper bound against a slope: two correct halves, no arrow
between them, and a green run that bore on nothing. The consumer registry now
carries a machine-readable `evaluates_atom_predicate` boolean for exactly that
reason. `ChainProof` is the producer-side form of the same discipline.

### Why "chain proved" cannot be claimed falsely

```lean
structure ChainProof (artifact : Artifact) where
  proposition : String        -- prose, for the reader
  provedBy : String           -- the Lean declaration
  acceptingValue : Int
  prop : Prop
  sound : artifact.computation.Returns acceptingValue → prop
```

`sound`'s domain mentions `artifact.computation`. A `ChainProof` therefore
cannot be built from a decision about some *other* program — which is exactly
the mistake above. Two constructors are supplied:

* `ChainProof.ofDecision` from a `Verified.Decision` (the equivalence-shaped
  packaging), with a `same : d.computation = artifact.computation` obligation;
* `ChainProof.ofClaim` from a `Verified.Algorithm.ProgramClaim`, which is what
  `CertifiedAlgorithm.claim` produces from an `Algorithm.Ensures` **and** a
  `ProgramRefinement`.

And the column is not a label:

```lean
theorem ChainProof.prop_of_receipt (c : ChainProof artifact)
    (bound : receiptBinds crypto artifact kind params nonce c.acceptingValue receipt = true)
    (admitted : RunAdmission crypto artifact receipt) : c.prop
```

For a `.chained` entry, a bound receipt plus an admitted run yields the
proposition the ledger prints. For any other entry there is no such theorem.
`RunAdmission` is still the empirical premise and is still not proved anywhere
in this package — **the ledger records runs; it never lets one become a
theorem.**

### The safe direction is free

Registering `.chained` requires a proof. Registering `.unbindable` requires
nothing but a sentence. Under-claiming is therefore always available, and the
`true` in the chain column is the only direction that costs anything.

---

## 2. A fourth fact: **bindable**

Separate from all three, and easy to miss: can a receipt for this program be
checked in the Lean kernel at all?

`receiptBinds` re-emits `Artifact.source?` and compares its digest. That needs
an `Artifact` — a `Computation`, a route, and a `main`. Eight of this
repository's fifteen registered programs do not have one, for two structural
reasons:

* **rolled scalar emission** (`rolled-10m`, `proth`) — an `Artifact` needs a
  `Computation`, and `Program.toComputation` at 10⁷ trips unrolls 10⁷ × 21
  statements, which is the size the rolled route exists to avoid;
* **array emission** (`mobius-array`, `mobius-seg`, `cdem-abel`,
  `dirichlet-ladder`, `rs62-ladder-sl`, `rs62-ladder-su`) — `Attest.emitFor`
  knows `Lower.compileProgram` and `Reflect.emitRolled` and nothing else. There
  is no array route in `EmissionRoute`.

`lean-compcert attest` will happily write receipts for all eight, and
`verify-receipt` will accept them, because both are `IO` tools that compare a
digest against freshly emitted text. **Nothing in Lean can consume those
receipts.** The ledger says so in its own column rather than leaving a reader to
discover it.

These eight are filed under route labels — `rolled-loop` and
`array-rolled-loop` — that no `Artifact` in the package claims, so
`receiptBinds`'s route clause refuses them rather than comparing an array
program's run against a scalar program's C. Before this change they were filed
under `straight-line`, the route whose proved chain covers exactly the case they
are not.

---

## 3. Staleness

> A program whose C has changed since its last run must read as **stale**, not
> as run.

Three files per program, all under the native-check directory:

| file | written | contents |
| --- | --- | --- |
| `<name>.stamp` | only on a **passing** run | `hash` of the generated C, `hash` of the toolchain key, `pass` |
| `<name>.run` | on **every** attempt | when, the C's SHA-256 and size, the `ccomp` version and identity digest, the link description, the machine, the exit code, the outcome, the constant tested, the receipt path |
| `<receipts>/<name>.receipt` | with `--attest` | the signed record |

The ledger re-emits every program's C in memory and re-digests it on every
invocation, so "the C has not changed" is a fact it establishes rather than a
claim it repeats. Then:

* both stamp halves match → **RUN**;
* the C half differs → `STALE — the generated C has CHANGED since the last
  passing run; the run was of a different binary`;
* the toolchain half differs → `STALE — the generated C is unchanged but the
  toolchain key is not: a different CompCert, target, startup stub, or machine`;
* no stamp and no record → `NOT RUN — never built here`;
* no stamp, and a record about **other** C → `STALE`, not a verdict about a
  binary this checkout has never produced;
* no stamp, a record about *this* C, and the binary ran and did not agree →
  `FAILED (disagrees)` or `FAILED (abnormal)`, which are **different** and are
  never merged;
* no stamp, a record about *this* C, and nothing executed (`ccomp` rejected it,
  or the link failed) → `NOT RUN`, because "failed" would claim something about
  a binary that was never produced;
* the toolchain cannot be resolved here (no `ccomp`, no startup stub) → every
  row reads `STALE`, because no stamp can be shown to belong to this
  environment.

The run record is why the last two are possible. The stamp is a cache key: it
exists only when the run agreed, so a tree in which every artifact was killed by
the out-of-memory killer is indistinguishable, by stamps alone, from one where
nothing was ever tried.

`ccomp` *rejecting* a program reads `REJECTED`, not `NOT COMPILED`: a hard
compile failure and a build that was never attempted are different facts. A run
record that does not parse, or that is about another program, reads
`UNREADABLE`, not `NO RECORD` — "this program has not been built here" would be
an affirmative false claim rather than a refusal.

Receipts get the same treatment. A receipt reads `STALE` when its `programHash`
is not the digest of the C this build emits, when its verdict is not `agrees`,
when it is filed under another route, when it records a different value than the
program certifies, when the program certifies no value at all, or — if the
caller passed `--nonce`/`--params` — when it answers a different challenge or a
different input block. One that does not parse reads `UNREADABLE`. Absence reads
`NO RECEIPT`, never blank.

The nonce and the params digest are checked only when supplied, because without
them the ledger has nothing to compare against; the same position
`NativeCheck.receiptStillCurrent` takes. And the ledger never verifies the
*signature*: `CURRENT` has never meant "cryptographically checked" — that is
`verify-receipt` out of band, and `receiptBinds` in the kernel.

---

## 4. Exit status: what counts as a defect

`ledger` exits `0` when every row is structurally clean and `1` otherwise. A
defect is **not** "has not run" — a program that has never been run is a
perfectly clean row. A defect is an internal inconsistency:

1. the entry's `Artifact` does not re-emit the C that is compiled, so a receipt
   would bind to text `ccomp` never saw (or the `Artifact` emits and the
   registered `emitted` does not, so the row describes C nobody compiles);
2. the proved chain consumes a different value than the binary self-checks —
   two internally consistent halves about different numbers;
3. the entry declares a chain but no `certifiedValue`, so nothing says the
   binary tested it;
4. the route label disagrees with the `Artifact`'s route;
5. an entry with **no** `Artifact` is filed under `straight-line` — the default,
   and the one route whose proved chain covers a straight-line emission it is
   not.  This is the check that keeps the array and rolled programs out of the
   label they used to carry;
6. a gap with no explanation, or a proved chain whose proposition or provenance
   is blank.  A blank is an omission, not a refusal;
7. the declared entry point does not occur in the emitted C.

Each is exercised in `LeanCompCertTests.testProgramLedger` on a registration
that is wrong in exactly that one way.

Note what defect 2 does **not** do: it compares two pieces of *registration
data*, `certifiedValue` against the chain's `acceptingValue`. It does not read
the constant out of the emitted `main`. Only `Attest.selfCheckMain` closes that,
by building the `main` from the same number — and fourteen of the fifteen
registered `mainC` definitions predate it and spell the literal twice.

---

## 5. What `describe` prints

```
$ lake exe lean-compcert describe fixedpoint
```

* the summary, and the **shape**: family, registers, trip count, instructions per
  block, instructions executed, output register, CCIR instruction count,
  restricted-C statement count, CCIR function name;
* the **parameters** it was instantiated at — two rows with the same name and
  different parameters are different programs;
* the **emitted C**: route, entry point, SHA-256, size in bytes, and the
  constant its `main` self-checks against;
* the **denotation theorem**, if one exists, *and whether it is instantiated at
  these parameters*. This last field is the one that matters: a theorem stated
  for every parameter and never instantiated at the ones the binary was compiled
  at tells a reviewer nothing about this binary, and a ledger printing only its
  name would read as though it did. Four registered programs are in exactly that
  position;
* the three states, plus bindable;
* what a successful run bears on — the proposition, the declaration it was
  proved from, and the accepting value; or an explicit statement that it bears on
  nothing;
* the **last attempt**: when, the outcome and exit code, the C's digest and size,
  the `ccomp` version *and* identity digest, the link description, the machine,
  the constant tested, and the receipt path;
* the **instruction listing** — every instruction, one per line, in emitter
  order. `--full` removes the 60-line cap; `--source` dumps the C.

The renderers are total matches over the instruction inductives, so adding a
constructor breaks the build rather than silently printing a program that is
missing an operation.

---

## 6. Registering a program (what a consumer does)

Two steps, in the consumer's own repository.

### Step 1 — write a `ProgramEntry`

```lean
open LeanCompCert

def myArtifact : Attest.Artifact := {
  computation := MyPort.computation
  route := .provedStraightLine
  -- Build the `main` from the accepting value.  Do NOT spell the constant out
  -- a second time: if the `main` tests one number and the chain consumes
  -- another, both sides agree with each other while the artifact tested
  -- something else.
  mainC := Attest.selfCheckMain "l_MyPort_entry" MyPort.expected }

def myEntry : Attest.ProgramEntry := {
  name := "my-port"
  summary := "what this binary computes, in one line"
  emitted := Attest.emitFor myArtifact.computation myArtifact.route myArtifact.mainC
  certifiedValue := some (MyPort.expected : Nat)
  entryPoint := "l_MyPort_entry"
  shape := (Attest.ProgramShape.ofProgram MyPort.program).withComputation
    MyPort.computation
  parameters := [("bound", toString MyPort.bound)]
  denotation := some {
    theoremName := "MyPort.program_denote"
    statement := "…in plain mathematics…"
    atTheseParameters := true }
  listing := Thunk.mk fun _ => Attest.listingOfProgram MyPort.program
  leanSide := .chained myArtifact
    (Attest.ChainProof.ofDecision myArtifact MyPort.decision rfl
      "…the proposition, in plain mathematics…" "MyPort.decision") }
```

If there is no proved arrow, write `.artifactOnly myArtifact "why not"`. If
nothing in Lean reproduces the C, write `.unbindable "why not"`. Both are
one-liners and neither carries a proof obligation — under-claiming is free.

### Step 2 — derive the cross-check units from the same list

```lean
def registry : List Attest.ProgramEntry := [myEntry, …]

def nativeCerts : List NativeCheck.Cert := registry.map NativeCheck.Cert.ofEntry

def main (args : List String) : IO UInt32 :=
  match args with
  | "check-native" :: rest => NativeCheck.run nativeCerts rest
  | "attest" :: rest => NativeCheck.run nativeCerts ("--attest" :: rest)
  | "ledger" :: rest => Attest.Ledger.ledgerVerb registry rest
  | "describe" :: rest => Attest.Ledger.describeVerb registry rest
  | _ => …
```

One list, so a program cannot be described by one verb and compiled by another.

### Publishing a receipt

```
lake exe lean-compcert attest-keygen
lake exe lean-compcert attest --campaign my-campaign --receipts evidence/receipts
lake exe lean-compcert ledger          # the receipt column now reads CURRENT
lake exe lean-compcert verify-receipt evidence/receipts/my-port.receipt --cert my-port --lean myReceipt
```

`--lean` prints the `RunReceipt` term to paste into a Lean file. The
authoritative check is then `Attest.receiptBinds` in the kernel, by
`decide +kernel`; `verify-receipt` is a convenience that can only fail earlier,
never make a bad receipt pass.

⚠ A locally signed receipt is **tamper-evident, not attested** — the key sits on
the machine that ran the binary. Read `LeanCompCert/Trusted/LocalReceipt.lean`
before relying on one. An enclave-grade receipt uses
`AttestationKind.enclaveQuote` and a different discharger, and `#print axioms`
names which one a theorem used.

---

## 7. What the ledger says about this repository today

15 registered programs: 15 compiled, 15 run, 6 chain proved, 7 bindable.

The nine that are not chain proved are not an oversight to be papered over; each
row carries the specific reason, and they fall into four kinds:

* **the proposition is about the program itself** — `verified-decide`'s only
  `Decision` decides that the computation returns 42. There is no reference
  function above it;
* **no theorem at all** — `rolled-10m`, `cdem-abel`. `Ports/CDEMAbelScan.lean`
  carries a reference fold in `namespace Ref` and no `example` or theorem tying
  `denote` to it;
* **a theorem at other parameters** — `mobius-array` (spot-checked at L = 8, 16,
  24; the artifact runs at L = 100000), `mobius-seg` (24 cells vs 32768),
  `dirichlet-ladder` (every `example` at `testCfg`, the artifact at
  `sourceCfg`);
* **a theorem never instantiated, or about the wrong thing** — `proth` has a
  real structural denotation theorem, `Ports.TGProth.prothProgram_denote`, which
  this certificate never instantiates; `rs62-ladder-{sl,su}` have
  `ladderProgram_denote`, which relates the array lift to the scalar program and
  neither to a reference function, and the obligation that would fix that,
  `Ports.RS62LadderProgram.LadderEncoding`, is *stated and not discharged*.

Making those rows true is ordinary work with a visible target. That is the
point of writing the column down.
