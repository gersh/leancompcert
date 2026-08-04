import LeanCompCert.Attest.Admission
import LeanCompCert.Attest.Tool
import LeanCompCert.CCIR.Pretty
import LeanCompCert.Verified.ArrayState
import LeanCompCert.Verified.Algorithm.Spec

/-!
# The program ledger: which compiled programs exist, what is in them, and
which have actually been run

The rest of this package answers "is this receipt bound to this computation?".
It does not answer the two questions a reviewer asks first:

* **what is in the compiled program** — what does this binary compute, at what
  parameters, and what does Lean prove about it;
* **has it been run** — and if the C has changed since, does the old evidence
  still say anything.

This module is the data model for both.  It is deliberately *generic*: nothing
here names a certificate, a campaign or a downstream project.  A consumer
(`claude_math`, `gpu_prover`, anyone) writes a `List ProgramEntry` of its own
and gets the same two verbs.

## The three states, and why they are three columns and not one

A green row in a build log usually means "it worked".  Here it can mean three
independent things, and collapsing them is the failure mode this module exists
to prevent.

| state | what it means | evidence |
| --- | --- | --- |
| **compiled** | `ccomp` accepted this exact C text | a `RunRecord` saying so |
| **run** | the binary executed and its self-check agreed | a current stamp, and a `RunRecord` whose verdict is `agrees` |
| **chain proved** | a *proved* Lean arrow runs from this program's computation to a mathematical proposition | a `ChainProof`, which does not typecheck unless the arrow exists |

They are independent in both directions.  A program can be compiled and run
while proving nothing about any mathematics — the binary computes a number and
no Lean statement says what the number means.  A program can be chain proved
and never compiled.  The ledger prints all three, always, and
`ProgramEntry.chainProved` is `true` only for the third.

The precedent is not hypothetical.  Downstream, an artifact that computed ψ was
registered alongside a Lean certificate that checked a fixed-point upper bound
against a slope: two correct halves, no arrow between them, and a green run that
bore on nothing.  `ChainProof` is typed so that mistake cannot be *registered*:
its `sound` field is a function out of `artifact.body.Returns`, so it is
about the body this artifact compiles and no other.

## Fail closed

Absence of evidence renders as an explicit refusal, never as a blank and never
as a pass:

* an entry with no `Artifact` reads `UNBINDABLE`, because no receipt for it can
  ever be checked by `receiptBinds`;
* an entry with no run record reads `NOT RUN`;
* an entry whose C has changed since the run reads `STALE`, **not** `RUN`;
* an entry with no `ChainProof` reads `NOT PROVED`, and carries the registrar's
  one-line reason;
* registering `.chained` requires a proof; registering `.unbindable` requires
  none.  Under-claiming is always available and always safe, so the `true` in
  the chain column is the only direction that costs anything.
-/

namespace LeanCompCert.Attest

open LeanCompCert.Verified

/-! ## Emission routes that have no `Artifact` -/

/-- The label under which `Verified.ArrayState.AProgram.emitRolled`'s output is
filed.

`EmissionRoute` has two constructors and neither is this one: `emitFor` knows
`Lower.compileProgram` and `Reflect.emitRolled`, and nothing in it reproduces
the array emitter.  A program emitted that way therefore has **no `Artifact`**,
so no receipt for it can ever be bound in Lean.

Giving it a distinct label is what keeps that fail-closed.  `receiptBinds`
compares `r.routeLabel` against `artifact.route.label`; a receipt filed under
this label matches neither existing route, so the check returns `false` rather
than comparing an array program's run against a scalar program's C.  Filing
these under `"straight-line"` — which is what the default did — would have made
a receipt for an array program look presentable under a route whose proved
chain does not cover it. -/
def arrayRolledLabel : String := "array-rolled-loop"

/-! ## What is in the compiled program -/

/-- Static shape of a registered program.

Every field is `Option` because the families differ: a scalar bounded fold has
a register count and a trip count, an array fold additionally has a static
array length, and a hand-built `Computation` has neither but does have a
lowered instruction list.  `none` renders as `-`, never as `0`. -/
structure ProgramShape where
  /-- Which family the program belongs to, in words. -/
  family : String
  /-- Registers the program's state machine uses. -/
  regCount : Option Nat := none
  /-- Static length of the program's array, for the array fragment. -/
  arrayLen : Option Nat := none
  /-- Trip count of the single outer loop. -/
  loopCount : Option Nat := none
  /-- Instructions in the initialisation block. -/
  initInstrs : Option Nat := none
  /-- Instructions in the loop body, executed once per trip. -/
  bodyInstrs : Option Nat := none
  /-- Instructions in the epilogue. -/
  epilogueInstrs : Option Nat := none
  /-- The register the program's result is read from. -/
  outputReg : Option Nat := none
  /-- `init + loopCount * body + epilogue`: how many instructions the program
  executes.  This is the number the emission route decides whether to write out
  (straight line) or to roll into a `while` (rolled). -/
  dynamicInstrs : Option Nat := none
  /-- Straight-line CCIR instructions of the packaged `Computation`. -/
  ccirInstrs : Option Nat := none
  /-- Restricted-C statements the proved C model is about. -/
  cStatements : Option Nat := none
  /-- The CCIR function's name, before ABI mangling. -/
  ccirFunction : Option String := none

/-- The shape of a scalar bounded-fold program. -/
def ProgramShape.ofProgram (p : Reflect.Program) : ProgramShape := {
  family := "scalar bounded fold (Verified.Reflect.Program)"
  regCount := some p.regCount
  loopCount := some p.loopCount
  initInstrs := some p.init.length
  bodyInstrs := some p.body.length
  epilogueInstrs := some p.epilogue.length
  outputReg := some p.output
  dynamicInstrs :=
    some (p.init.length + p.loopCount * p.body.length + p.epilogue.length)
}

/-- The shape of an array bounded-fold program. -/
def ProgramShape.ofAProgram (p : ArrayState.AProgram) : ProgramShape := {
  family := "array bounded fold (Verified.ArrayState.AProgram)"
  regCount := some p.regCount
  arrayLen := some p.arrayLen
  loopCount := some p.loopCount
  initInstrs := some p.init.length
  bodyInstrs := some p.body.length
  epilogueInstrs := some p.epilogue.length
  outputReg := some p.output
  dynamicInstrs :=
    some (p.init.length + p.loopCount * p.body.length + p.epilogue.length)
}

/-- The shape of a `Computation` with no program above it: the lowered
instruction list is all there is. -/
def ProgramShape.ofComputation (c : Computation) : ProgramShape := {
  family := "hand-built straight line (Verified.Computation)"
  ccirInstrs := some c.instructions.length
  cStatements := some c.statements.length
  ccirFunction := some c.fn.name.name
  outputReg := some c.output.value
}

/-- Add the packaged `Computation`'s numbers to a program's shape.  These are
the counts the *proved* chain is about: `Computation.result_preserved` relates
`cStatements` to `ccirInstrs`. -/
def ProgramShape.withComputation (s : ProgramShape) (c : Computation) :
    ProgramShape :=
  { s with
    ccirInstrs := some c.instructions.length
    cStatements := some c.statements.length
    ccirFunction := some c.fn.name.name }

/-! ## Faithful listings

Not a summary and not a paraphrase: every instruction, one per line, in the
order the emitter walks them.  The renderers below are total matches over the
instruction inductives, so adding a constructor breaks this file rather than
silently printing a program that is missing an operation. -/

def renderOperand : Reflect.Operand → String
  | .reg index => s!"r{index}"
  | .lit value => toString value
  | .idx => "idx"

def renderOp : Reflect.Op → String
  | .add => "+"    | .sub => "-"     | .mul => "*"
  | .udiv => "/u"  | .urem => "%u"
  | .band => "&"   | .bor => "|"     | .bxor => "^"
  | .shl => "<<"   | .lshr => ">>u"
  | .eq => "=="    | .ne => "!="
  | .lt => "<u"    | .le => "<=u"    | .gt => ">u"   | .ge => ">=u"

def renderInstr : Reflect.Instr → String
  | .mov dest src => s!"r{dest} := {renderOperand src}"
  | .binop dest op lhs rhs =>
      s!"r{dest} := {renderOperand lhs} {renderOp op} {renderOperand rhs}"

def renderAInstr : ArrayState.AInstr → String
  | .scalar i => renderInstr i
  | .load dest idxReg => s!"r{dest} := arr[r{idxReg}]   (traps if r{idxReg} ≥ arrayLen)"
  | .store idxReg srcReg =>
      s!"arr[r{idxReg}] := r{srcReg}   (traps if r{idxReg} ≥ arrayLen)"

private def blockLines (label : String) (rendered : List String) :
    List String :=
  [s!"{label} ({rendered.length} instructions):"] ++ rendered.map ("  " ++ ·)

/-- Every instruction of a scalar program, in the order the emitter walks
them. -/
def listingOfProgram (p : Reflect.Program) : String :=
  String.intercalate "\n" (
    [s!"regCount = {p.regCount}, loopCount = {p.loopCount}, output = r{p.output}"]
    ++ blockLines "init" (p.init.map renderInstr)
    ++ blockLines s!"body, once per trip with idx = 0 … {p.loopCount} - 1"
        (p.body.map renderInstr)
    ++ blockLines "epilogue" (p.epilogue.map renderInstr))

/-- Every instruction of an array program. -/
def listingOfAProgram (p : ArrayState.AProgram) : String :=
  String.intercalate "\n" (
    [s!"regCount = {p.regCount}, arrayLen = {p.arrayLen}, \
       loopCount = {p.loopCount}, output = r{p.output}"]
    ++ blockLines "init" (p.init.map renderAInstr)
    ++ blockLines s!"body, once per trip with idx = 0 … {p.loopCount} - 1"
        (p.body.map renderAInstr)
    ++ blockLines "epilogue" (p.epilogue.map renderAInstr))

/-- The straight-line CCIR a `Computation` carries, through the package's own
pretty printer — the same one `lean-compcert demo` prints. -/
def listingOfComputation (c : Computation) : String :=
  CCIR.Program.pretty { functions := #[c.fn] }

/-! ## The proved arrow -/

/-- **A proved Lean chain from this artifact's run to a mathematical
proposition.**

`sound` is the whole content: a function *out of* `artifact.body.Returns
acceptingValue`.  Because the domain mentions `artifact.body`, a
`ChainProof` cannot be built from a decision about some other program — which
is exactly the mistake this type exists to make unregistrable.

`proposition` and `provedBy` are prose for the reader; `prop` and `sound` are
what Lean checked.  A registration that gets the prose wrong is a
documentation bug; a registration that gets the arrow wrong does not compile.

⚠ `acceptingValue` must be the constant the emitted `main` compares against.
If the binary self-checks one number and this arrow consumes another, both
sides are internally consistent while the artifact tested something else.

Two things guard that, and it is worth being precise about which does what.
`Attest.selfCheckMain` closes it **by construction**: build the `main` from the
same number and the constant inside the hashed text cannot differ from the one
the arrow consumes.  `Ledger.defectsOf` closes the weaker half — it compares
this field against the entry's `certifiedValue` and fails the row when they
differ.  It compares two pieces of *registration data*; it does not read the
constant out of the emitted C.  A `mainC` written by hand can still disagree
with both, which is why `selfCheckMain` exists and why the ledger cannot make
hand-written `main`s safe. -/
structure ChainProof (artifact : Artifact) where
  /-- The mathematical proposition, in words, as it should appear to a
  reviewer. -/
  proposition : String
  /-- The Lean declaration the arrow was taken from. -/
  provedBy : String
  /-- The value a successful run must report. -/
  acceptingValue : Int
  /-- The proposition itself. -/
  prop : Prop
  /-- **The arrow.**  A run of *this artifact's body* reporting
  `acceptingValue` proves `prop`. -/
  sound : artifact.body.Returns acceptingValue → prop

/-- Build a `ChainProof` from a `Decision` — the equivalence-shaped packaging
(`Verified.Decision`).  `same` is the clause that pins the decision to this
artifact; it is `rfl` whenever the registry names the same `Computation` the
artifact was built from. -/
def ChainProof.ofDecision {p : Prop} (artifact : Artifact) (d : Decision p)
    (same : artifact.body.sourceResult = d.computation.sourceResult)
    (proposition provedBy : String) : ChainProof artifact := {
  proposition
  provedBy
  acceptingValue := d.acceptingValue
  prop := p
  sound := fun h => d.prove (by
    show d.computation.sourceResult = some d.acceptingValue
    rw [← same]
    exact h)
}

/-- Build a `ChainProof` from a `ProgramClaim` — the forward-only packaging
(`Verified.Algorithm.ProgramClaim`), which is what
`CertifiedAlgorithm.claim` produces from an `Algorithm.Ensures` and a
`ProgramRefinement`.  This is the strongest shape in the package: the
refinement is proved structurally, for every input, rather than by evaluating
the loop. -/
def ChainProof.ofClaim {p : Prop} (artifact : Artifact) (name : String)
    (c : Verified.Algorithm.ProgramClaim p)
    (same : artifact.body.sourceResult = (c.computation name).sourceResult)
    (proposition provedBy : String) : ChainProof artifact := {
  proposition
  provedBy
  acceptingValue := ((c.acceptingValue : Nat) : Int)
  prop := p
  sound := fun h => c.prove name (by
    show (c.computation name).sourceResult = some ((c.acceptingValue : Nat) : Int)
    rw [← same]
    exact h)
}

/-- **The chain column is not decoration.**

For an entry registered as `.chained`, a bound receipt plus an admitted run
yields the proposition the ledger prints.  For an entry registered any other
way there is no such theorem, which is the whole difference between the two
renderings.

`RunAdmission` is still the empirical premise and is still not proved here; see
`LeanCompCert/Attest/Admission.lean`. -/
theorem ChainProof.prop_of_receipt {crypto : ReceiptCrypto} {artifact : Artifact}
    {kind : AttestationKind} {params nonce : String} {receipt : RunReceipt}
    (c : ChainProof artifact)
    (bound :
      receiptBinds crypto artifact kind params nonce c.acceptingValue receipt
        = true)
    (covered : artifact.coveredByProvedChain = true)
    (admitted : RunAdmission crypto artifact receipt) : c.prop :=
  c.sound (returns_of_receipt bound covered admitted)

/-- The same, with the coverage condition read off `receiptBindsProved` rather
than supplied separately — available on both routes; see `ArtifactBody`. -/
theorem ChainProof.prop_of_receipt_proved {crypto : ReceiptCrypto}
    {artifact : Artifact} {kind : AttestationKind} {params nonce : String}
    {receipt : RunReceipt} (c : ChainProof artifact)
    (bound :
      receiptBindsProved crypto artifact kind params nonce c.acceptingValue
        receipt = true)
    (admitted : RunAdmission crypto artifact receipt) :
    artifact.coveredByProvedChain = true ∧ c.prop :=
  ⟨(receiptBindsProved_sound bound).1,
    c.sound (returns_of_receipt_proved bound admitted)⟩

/-! ## What Lean knows about a registered program -/

/-- **The Lean side of a registered program**, as a three-way choice that a
reader cannot misread.

The order is strictly increasing in what has been proved, and the *default* for
a new registration is the weakest one. -/
inductive LeanSide where
  /-- **No `Artifact`.**  Nothing in Lean reproduces this program's C text, so
  `receiptBinds` can never be applied to it: a receipt for this program is a
  signed file and nothing more.  `why` says what is missing. -/
  | unbindable (why : String)
  /-- **An `Artifact`, and no arrow.**  `receiptBinds` can check a receipt
  against this program's emitted C, but nothing in Lean says what the value it
  reports means.  `why` says what is missing. -/
  | artifactOnly (artifact : Artifact) (why : String)
  /-- **An `Artifact` and a proved arrow.**  This — and only this — is
  "chain proved". -/
  | chained (artifact : Artifact) (chain : ChainProof artifact)

/-- The artifact, when there is one. -/
def LeanSide.artifact? : LeanSide → Option Artifact
  | .unbindable _ => none
  | .artifactOnly a _ => some a
  | .chained a _ => some a

/-- Can a receipt for this program be checked in the Lean kernel at all? -/
def LeanSide.bindable : LeanSide → Bool
  | .unbindable _ => false
  | .artifactOnly _ _ => true
  | .chained _ _ => true

/-- Is a proved chain in place?  `true` exactly for `.chained`, whose
construction requires the arrow. -/
def LeanSide.chainProved : LeanSide → Bool
  | .chained _ _ => true
  | _ => false

/-- The value a successful run must report for the chain to fire. -/
def LeanSide.acceptingValue? : LeanSide → Option Int
  | .chained _ c => some c.acceptingValue
  | _ => none

/-- The proposition a successful run bears on, in words; `none` when there is
none. -/
def LeanSide.proposition? : LeanSide → Option String
  | .chained _ c => some c.proposition
  | _ => none

/-- The Lean declaration the arrow came from. -/
def LeanSide.provedBy? : LeanSide → Option String
  | .chained _ c => some c.provedBy
  | _ => none

/-- Why nothing stronger is claimed.  `none` for `.chained`. -/
def LeanSide.gap? : LeanSide → Option String
  | .unbindable why => some why
  | .artifactOnly _ why => some why
  | .chained _ _ => none

/-! ## The denotation theorem -/

/-- A theorem relating the program's `denote` to a reference function.

`atTheseParameters` is the field that matters.  A denotation theorem stated for
every parameter and never instantiated at the ones this program was compiled at
tells a reviewer nothing about *this* binary, and a ledger that printed only
the theorem's name would read as though it did. -/
structure DenotationNote where
  /-- The Lean declaration. -/
  theoremName : String
  /-- What it says, in plain mathematics. -/
  statement : String
  /-- Is it instantiated at the parameters this program was compiled at? -/
  atTheseParameters : Bool
  /-- When it is not, what is missing. -/
  gap : String := ""

/-! ## A registered program -/

/-- **One registered program.**

`emitted` is the authority for what gets compiled: it is the same field
`NativeCheck.Cert` carries, so registering a program in the ledger and
registering it for the native cross-check are one act rather than two lists to
keep in step.

`leanSide` is the authority for what is proved.  The ledger cross-checks the
two — an `Artifact` whose `source?` differs from `emitted` is a defect, because
the receipt would then bind to text other than the text that was compiled — and
reports the disagreement rather than picking a winner. -/
structure ProgramEntry where
  /-- Stable name.  Also the basename of the cache, stamp, run record and
  receipt files, so keep it to `[A-Za-z0-9._-]`. -/
  name : String
  /-- One line: what this program computes. -/
  summary : String
  /-- **The exact bytes handed to `ccomp`.**  An entry whose C fails to emit
  reads as a failure, never as an absent row. -/
  emitted : Except (Array String) String
  /-- Which emitter produced `emitted`, by label.  Must match the
  `Artifact.route.label` of `leanSide`'s artifact when there is one;
  `arrayRolledLabel` for the array emitter, which has no route. -/
  routeLabel : String := EmissionRoute.provedStraightLine.label
  /-- The constant the emitted `main` compares against. -/
  certifiedValue : Option Int := none
  /-- The C symbol `main` calls. -/
  entryPoint : String
  /-- Static shape; see `ProgramShape`. -/
  shape : ProgramShape
  /-- The parameters the program was instantiated at, in registration order.
  These are what make the row reproducible: two rows with the same name and
  different parameters are different programs. -/
  parameters : List (String × String) := []
  /-- The denotation theorem, when one exists. -/
  denotation : Option DenotationNote := none
  /-- What Lean knows; see `LeanSide`. -/
  leanSide : LeanSide
  /-- A faithful instruction listing, deferred because some are large. -/
  listing : Thunk String := Thunk.pure ""

def ProgramEntry.artifact? (e : ProgramEntry) : Option Artifact :=
  e.leanSide.artifact?

def ProgramEntry.bindable (e : ProgramEntry) : Bool := e.leanSide.bindable

def ProgramEntry.chainProved (e : ProgramEntry) : Bool :=
  e.leanSide.chainProved

/-- The emitted C, or `none` when emission failed. -/
def ProgramEntry.source? (e : ProgramEntry) : Option String :=
  e.emitted.toOption

/-! ## The run record

What `check-native` writes next to its stamp.  The stamp is a cache key and
says only "this passed"; the record is the evidence a reader wants — when, on
what compiler, with what result.

Line-oriented for the same reason receipts are: every field is a digest, a
bounded label or a decimal, none of which can contain a newline, so the format
needs no escaping.  Parsing is fail-closed: a record with the wrong line count
or an unknown outcome label is refused rather than patched up. -/

/-- What happened on the last attempt.

`compiled` and `agrees` are separate outcomes on purpose.  `ccomp` accepting
the C and the binary agreeing with the certified constant are different facts,
and the second can fail while the first holds. -/
inductive RunOutcome where
  /-- The C could not be emitted at all. -/
  | emitFailed
  /-- `ccomp` rejected the generated C. -/
  | compileFailed
  /-- `ccomp` accepted it; the link failed. -/
  | linkFailed
  /-- It ran and the computed value equals the certified constant. -/
  | agrees
  /-- It ran and the computed value differs.  A genuine disagreement. -/
  | disagrees
  /-- It was killed — signal, out of memory.  Evidence of nothing about the
  computed value, and never reported as a disagreement. -/
  | abnormal
  deriving DecidableEq, Repr, Inhabited

def RunOutcome.label : RunOutcome → String
  | .emitFailed => "emit-failed"
  | .compileFailed => "compile-failed"
  | .linkFailed => "link-failed"
  | .agrees => "agrees"
  | .disagrees => "disagrees"
  | .abnormal => "abnormal"

def RunOutcome.ofLabel : String → Option RunOutcome
  | "emit-failed" => some .emitFailed
  | "compile-failed" => some .compileFailed
  | "link-failed" => some .linkFailed
  | "agrees" => some .agrees
  | "disagrees" => some .disagrees
  | "abnormal" => some .abnormal
  | _ => none

/-- Did `ccomp` accept the C on this attempt? -/
def RunOutcome.compiled : RunOutcome → Bool
  | .emitFailed => false
  | .compileFailed => false
  | .linkFailed => true
  | .agrees => true
  | .disagrees => true
  | .abnormal => true

/-- **Did the binary execute at all?**

Deliberately *not* "did it agree": a disagreement and an out-of-memory kill are
both executions, and both are `true` here.  Whether the run was a *pass* is
`outcome = .agrees` and nothing else.  In a module whose premise is that RUN is
not the same as green, a predicate named for the weaker fact has to say so. -/
def RunOutcome.executed : RunOutcome → Bool
  | .agrees => true
  | .disagrees => true
  | .abnormal => true
  | _ => false

/-- Format version of the run-record schema. -/
def runRecordSchema : String := "leancompcert-run/1"

/-- **What happened the last time this program was built and run here.** -/
structure RunRecord where
  /-- Must equal `runRecordSchema`. -/
  schema : String
  /-- The `ProgramEntry.name` this record is about. -/
  name : String
  /-- RFC 3339 UTC, when the attempt finished. -/
  recordedAt : String
  /-- SHA-256 of the exact C text that was compiled. -/
  sourceDigest : String
  /-- Its size in bytes. -/
  sourceBytes : Nat
  /-- `ccomp -version`, first line. -/
  ccompVersion : String
  /-- SHA-256 of the `ccomp` binary together with its `compcert.ini` — the
  identity `ccomp -version` does not give, because it names no architecture. -/
  ccompDigest : String
  /-- Freestanding or hosted, plus the stub, assembler and linker identities. -/
  linkDescription : String
  /-- The machine, in the sense of `NativeCheck.machineIdentity`. -/
  machine : String
  /-- The artifact's exit status, verbatim. -/
  exitCode : Nat
  /-- The classification of that status. -/
  outcome : RunOutcome
  /-- The constant the binary self-checked against, rendered; `unstated` when
  the entry declares none. -/
  certifiedValue : String
  /-- Where the receipt was written; `"-"` when none was.  A literal rather
  than an empty line, so that the record's field count is fixed and a
  truncated file is refused rather than reinterpreted. -/
  receiptPath : String
  deriving DecidableEq, Repr

/-- A field as it goes on the wire.

The format is thirteen **non-empty** lines and `parse` enforces that, so a
field that is empty or all whitespace would produce a record its own reader
refuses — and an unreadable record is indistinguishable from a missing one.
`ccomp -version` emitting a leading blank line is enough to reach that.  An
empty field is therefore written `-`, which round-trips. -/
private def wireField (text : String) : String :=
  if text.trimAscii.isEmpty then "-" else text

/-- Thirteen non-empty lines, in this order, with a trailing newline. -/
def RunRecord.render (r : RunRecord) : String :=
  String.intercalate "\n" (List.map wireField [
    r.schema, r.name, r.recordedAt, r.sourceDigest, toString r.sourceBytes,
    r.ccompVersion, r.ccompDigest, r.linkDescription, r.machine,
    toString r.exitCode, r.outcome.label, r.certifiedValue, r.receiptPath
  ]) ++ "\n"

/-- Read a run record.  Fail-closed: any deviation is `none`, and a `none`
renders as "no record", never as a pass. -/
def RunRecord.parse (text : String) : Option RunRecord :=
  match ((text.splitOn "\n").map (·.trimAscii.toString)).filter (· != "") with
  | [schema, name, recordedAt, sourceDigest, sourceBytes, ccompVersion,
      ccompDigest, linkDescription, machine, exitCode, outcome,
      certifiedValue, receiptPath] => do
      if schema != runRecordSchema then none
      let bytes ← sourceBytes.toNat?
      let code ← exitCode.toNat?
      let outcome' ← RunOutcome.ofLabel outcome
      some {
        schema, name, recordedAt, sourceDigest, sourceBytes := bytes,
        ccompVersion, ccompDigest, linkDescription, machine,
        exitCode := code, outcome := outcome', certifiedValue, receiptPath }
  | _ => none

/-! ## The states -/

/-- Has `ccomp` accepted this program's C? -/
inductive BuildState where
  /-- The C could not be emitted; the errors. -/
  | emitFailed (errors : List String)
  /-- No record of `ccomp` ever having seen this program here. -/
  | notCompiled
  /-- `ccomp` was given this program and **rejected** it.  Emphatically not the
  same as never having tried, and the two used to print the same sentence. -/
  | rejected (why : String)
  /-- `ccomp` accepted the C recorded in the run record — but that C, or the
  compiler that accepted it, is not the one this build would use now. -/
  | staleCompile (why : String)
  /-- `ccomp` accepted exactly this C text, with this compiler. -/
  | compiled
  deriving Repr

def BuildState.label : BuildState → String
  | .emitFailed _ => "EMIT FAILED"
  | .notCompiled => "NOT COMPILED"
  | .rejected _ => "REJECTED"
  | .staleCompile _ => "STALE"
  | .compiled => "COMPILED"

def BuildState.ok : BuildState → Bool
  | .compiled => true
  | _ => false

/-- Has the binary run, on this C, in this environment? -/
inductive RunState where
  /-- No passing stamp.  Never run here, or the last attempt failed. -/
  | notRun (why : String)
  /-- It ran, but not on this C text, or not with this toolchain.  **This is
  not a pass**, and the distinction is the point of the ledger. -/
  | stale (why : String)
  /-- The last attempt ran and did not agree.  A disagreement and an abnormal
  termination are different failures and are kept apart. -/
  | failed (outcome : RunOutcome) (detail : String)
  /-- It ran, on this exact C, with this toolchain, and agreed. -/
  | ran
  deriving Repr

def RunState.label : RunState → String
  | .notRun _ => "NOT RUN"
  | .stale _ => "STALE"
  | .failed o _ => s!"FAILED ({o.label})"
  | .ran => "RUN"

def RunState.ok : RunState → Bool
  | .ran => true
  | _ => false

/-- Is there a receipt, and does it still bind to the C this build emits? -/
inductive ReceiptState where
  /-- No receipt file.  Not an error — most programs are checked without
  attestation — but never rendered as a pass. -/
  | absent
  /-- A file is there and this tool cannot read it as a receipt. -/
  | unreadable (why : String)
  /-- It parses, and it is about some other text or some other outcome. -/
  | stale (why : String)
  /-- It parses, its verdict is `agrees`, and its `programHash` is the digest
  of the C this build emits.  ⚠ Still not a proof of anything: the
  authoritative check is `receiptBinds` in the kernel, and even a passing
  `receiptBinds` asserts nothing about whether a run happened. -/
  | current (recordedAt attestation : String)
  deriving Repr

def ReceiptState.label : ReceiptState → String
  | .absent => "NO RECEIPT"
  | .unreadable _ => "UNREADABLE"
  | .stale _ => "STALE"
  | .current _ _ => "CURRENT"

def ReceiptState.ok : ReceiptState → Bool
  | .current _ _ => true
  | _ => false

/-- Is a proved Lean chain in place? -/
inductive ChainState where
  /-- No arrow.  `why` is the registrar's reason, and is never empty. -/
  | notProved (why : String)
  /-- An arrow, from `provedBy`, to `proposition`. -/
  | proved (proposition provedBy : String)
  deriving Repr

def ChainState.label : ChainState → String
  | .notProved _ => "NOT PROVED"
  | .proved _ _ => "PROVED"

def ChainState.ok : ChainState → Bool
  | .proved _ _ => true
  | _ => false

/-! ## Structural consistency

Checks the ledger re-runs every time, because each of them is a way for two
internally consistent halves to be about different things. -/

/-- One structural defect, as a sentence. -/
abbrev Defect := String

/-! ## A row -/

/-- **One line of the ledger.** -/
structure LedgerRow where
  name : String
  summary : String
  routeLabel : String
  /-- The C symbol `main` calls. -/
  entryPoint : String
  /-- The constant the emitted `main` compares against. -/
  certifiedValue : Option Int
  /-- Static shape; see `ProgramShape`. -/
  shape : ProgramShape
  /-- The parameters the program was instantiated at. -/
  parameters : List (String × String)
  /-- The denotation theorem, when one exists. -/
  denotation : Option DenotationNote
  /-- SHA-256 of the C this build emits now; `none` when it does not emit. -/
  sourceDigest : Option String
  /-- Its size in bytes. -/
  sourceBytes : Option Nat
  build : BuildState
  run : RunState
  receipt : ReceiptState
  chain : ChainState
  /-- Can a receipt for this program be checked in the kernel at all? -/
  bindable : Bool
  /-- Why not, when it cannot. -/
  bindableWhy : String
  /-- The last recorded attempt, when there is one *and it could be read*. -/
  record : Option RunRecord
  /-- Why the record on disk could not be used, when there was one.  Without
  this, a corrupt record and a missing record print the same sentence — and
  "this program has not been built here" would be an affirmative false claim
  rather than a refusal. -/
  recordUnreadable : Option String
  /-- Structural defects: an artifact that does not reproduce the compiled C, a
  chain that consumes a different value than the binary tested, a route label
  that disagrees with the artifact's route.  A non-empty list fails the
  ledger. -/
  defects : List Defect

/-- A row is clean when it has no structural defect.  This is deliberately
*not* "the program has run": a program that has never been run is a perfectly
clean row that reads `NOT RUN`. -/
def LedgerRow.clean (r : LedgerRow) : Bool := r.defects.isEmpty

end LeanCompCert.Attest
