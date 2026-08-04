import Lean
import LeanCompCert.NativeCheck

/-!
# The ledger verbs

`lean-compcert ledger` and `lean-compcert describe NAME`, over any
`List Attest.ProgramEntry`.  The registry is the caller's; nothing here names a
program, a campaign or a project.

## What the ledger reads, and why it reads it rather than being told

Three files per program, all under the native-check directory:

* `<name>.stamp` — written by `check-native` **only on a passing run**.  Its
  two halves are `hash` of the generated C and `hash` of the toolchain key.
  Comparing them separately is what lets a row say *which* one moved.
* `<name>.run` — written on **every** attempt, passing or not.  This is where
  "when, on what compiler, with what result" comes from, and it is why a build
  tree in which every artifact was killed by the out-of-memory killer does not
  look like one in which nothing was ever tried.
* `<receipts>/<name>.receipt` — the signed record, when `--attest` was used.

Nothing is taken on the caller's word.  The C is re-emitted in memory and
re-digested on every invocation, so "the C has not changed" is a fact this tool
establishes rather than a claim it repeats.

## Staleness

A stamp is *current* when both halves match the environment resolved right now.
When it is not, the ledger says which half moved:

* the generated C changed — the program was edited, so the old run was of some
  other binary;
* the toolchain key changed — a different CompCert, a different target, a
  different startup stub, a different machine.

Either way the row reads `STALE`, never `RUN`.  That distinction is the whole
point of the ledger: evidence about a binary you no longer build is not
evidence about the binary you do.

## Exit status

`0` when every row is structurally clean, `1` when any row has a **defect**.  A
defect is not "has not run" — a program that has never been run is a perfectly
clean row.  A defect is an internal inconsistency:

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

## What a receipt is judged on, and what is opt-in

Parse, verdict, route label, certified value, and `programHash` against the C
this build emits, always.  The **nonce** and the **params digest** only when the
caller supplies `--nonce`/`--params` — without them the ledger has nothing to
compare against, and inventing a value would be worse than saying nothing.  This
is the same position `NativeCheck.receiptStillCurrent` takes.

The ledger never verifies the *signature*: that is `verify-receipt`'s job out of
band and `receiptBinds`'s in the kernel, and a `CURRENT` here has never meant
"cryptographically checked".
-/

namespace LeanCompCert.Attest.Ledger

open LeanCompCert
open LeanCompCert.Attest

/-! ## Reading the evidence -/

private def readIfPresent (path : System.FilePath) : IO (Option String) := do
  if !(← path.pathExists) then return none
  try
    return some (← IO.FS.readFile path)
  catch _ =>
    return none

/-- SHA-256 of a string, or `none` when the digest could not be computed.
Fail-closed: a `none` makes every comparison against it fail. -/
private def digest? (scratch : System.FilePath) (text : String) :
    IO (Option String) := do
  match ← Attest.Tool.sha256Hex scratch text with
  | .error _ => return none
  | .ok value => return some value

/-! ## The structural checks

These do not read the disk.  They ask whether the registration is internally
consistent, and every one of them is a way for two correct halves to be about
different things. -/

/-- The structural defects of one entry.  Empty is the good case.

Read the list of checks as a list of ways two internally consistent halves come
to be about different things.  Every one of them is cheap and re-run on every
invocation, because a check that runs once at review time is a check that stops
being true. -/
def defectsOf (entry : ProgramEntry) : List Defect := Id.run do
  let mut defects : List Defect := []
  match entry.leanSide with
  | .unbindable why =>
      -- No artifact means no route to compare against, so the *only* thing
      -- that can be checked is that the entry is not claiming the route the
      -- proved chain covers.  `straight-line` is the default, so an array or
      -- rolled program that simply forgets to set `routeLabel` lands there —
      -- which is exactly the mislabelling `arrayRolledLabel` exists to stop,
      -- and it would otherwise be unguarded on precisely the entries that
      -- need guarding.
      if entry.routeLabel == EmissionRoute.provedStraightLine.label then
        defects := defects ++ [
          s!"no Artifact reproduces this program's C, yet it is filed under \
             route '{entry.routeLabel}' — the route whose proved chain covers \
             the straight-line emission it is not.  Give it a label no \
             Artifact claims (`Attest.arrayRolledLabel`, or the rolled \
             route's) so receiptBinds refuses a receipt for it rather than \
             comparing it against a scalar program's C."]
      if why.trimAscii.isEmpty then
        defects := defects ++ [
          "the entry claims nothing is proved and gives no reason; a blank \
           gap is not a refusal, it is an omission"]
  | .artifactOnly artifact _ | .chained artifact _ =>
      if artifact.route.label != entry.routeLabel then
        defects := defects ++ [
          s!"route label '{entry.routeLabel}' but the Artifact's route is \
             '{artifact.route.label}'; receiptBinds compares these and would \
             refuse every receipt"]
      match artifact.source?, entry.source? with
      | none, _ =>
          defects := defects ++ [
            "the Artifact's emitter fails, so no receipt for this program can \
             ever bind"]
      | some fromArtifact, some compiled =>
          if fromArtifact != compiled then
            defects := defects ++ [
              "the Artifact re-emits DIFFERENT C from the text that is \
               compiled; a receipt would bind to text ccomp never saw"]
      | some _, none =>
          defects := defects ++ [
            "the Artifact emits and the registered `emitted` does not, so the \
             row describes C that is never compiled"]
  -- A gap that is not explained is an omission, not a refusal; and a chain
  -- whose prose is blank prints an empty proposition to a reviewer.
  match entry.leanSide with
  | .unbindable _ => pure ()
  | .artifactOnly _ why =>
      if why.trimAscii.isEmpty then
        defects := defects ++ [
          "the entry says no chain is proved and gives no reason"]
  | .chained _ chain =>
      if chain.proposition.trimAscii.isEmpty || chain.provedBy.trimAscii.isEmpty then
        defects := defects ++ [
          "the chain is proved and its proposition or its provenance is blank, \
           so the row would tell a reviewer a run bears on nothing in \
           particular"]
  match entry.leanSide.acceptingValue? with
  | none => pure ()
  | some accepting =>
      match entry.certifiedValue with
      | none =>
          defects := defects ++ [
            s!"the proved chain consumes {accepting} but the entry declares no \
               certifiedValue, so nothing says the binary tested it"]
      | some certified =>
          if certified != accepting then
            defects := defects ++ [
              s!"the binary self-checks {certified} and the proved chain \
                 consumes {accepting}; both halves are consistent and they are \
                 about different numbers"]
  -- The entry point is what `main` calls.  A wrong one is prose that no other
  -- check touches, so compare it against the text actually compiled.
  match entry.source? with
  | none => pure ()
  | some source =>
      if !source.contains entry.entryPoint then
        defects := defects ++ [
          s!"the declared entry point '{entry.entryPoint}' does not occur in \
             the emitted C"]
  return defects

/-! ## Building a row -/

/-- Classify one entry against the disk.

`env?` is `none` when the environment could not be resolved — no `ccomp`, no
startup stub.  That is not treated as "everything is fine": without the
toolchain key no stamp can be shown to belong to *this* environment, so every
**run** state reads `STALE` with that reason.  The **compiled** column can still
read `COMPILED` on the strength of a run record whose C digest matches, because
that record names the compiler it used; what cannot be established without the
environment is that the compiler is still the one you have.

`paramsHash?` is `some` only when the caller passed `--params`, and `opts.nonce`
only when they passed `--nonce`.  Both are then *required* of a receipt, exactly
as `receiptBinds` requires them.  Neither is checked when it was not supplied,
because the ledger has nothing to check it against — and it says so rather than
inventing a value. -/
def rowFor (opts : NativeCheck.Options) (env? : Option NativeCheck.Environment)
    (paramsHash? : Option String) (entry : ProgramEntry) : IO LedgerRow := do
  let scratch :=
    match env? with
    | some env => env.scratch
    | none => opts.dir / "digest-scratch"
  let source? := entry.source?
  let sourceDigest? ←
    match source? with
    | none => pure none
    | some text => digest? scratch text
  let recordText? ← readIfPresent (NativeCheck.runRecordPath opts entry.name)
  -- A record that does not parse, or that is about another program, is NOT a
  -- missing record: printing "this program has not been built here" for a
  -- corrupt file would be an affirmative false claim rather than a refusal.
  let (record?, recordUnreadable?) : Option RunRecord × Option String :=
    match recordText? with
    | none => (none, none)
    | some text =>
        match RunRecord.parse text with
        | none =>
            (none, some
              "a run record is on disk and this tool cannot read it: wrong \
               line count, unknown schema, or an unknown outcome label")
        | some record =>
            if record.name != entry.name then
              (none, some
                s!"the run record on disk is about '{record.name}', not \
                   '{entry.name}'; it is another program's evidence")
            else
              (some record, none)
  let stampText? ← readIfPresent (opts.dir / s!"{entry.name}.stamp")
  let receiptText? ←
    readIfPresent (NativeCheck.defaultReceiptDir opts / s!"{entry.name}.receipt")

  -- Does the record describe the C we emit now?
  let recordCurrent : Bool :=
    match record?, sourceDigest? with
    | some record, some digest => record.sourceDigest == digest
    | _, _ => false

  -- …and was it written by the compiler we have now?
  let recordToolchainCurrent : IO Bool := do
    match record?, env? with
    | some record, some env =>
        match ← digest? scratch env.compcertId with
        | none => return false
        | some digest => return record.ccompDigest == digest
    | _, _ => return false
  let recordToolchainCurrent ← recordToolchainCurrent

  -- Does the stamp belong to this C and this environment?
  let stampState : Option (Bool × Bool) :=
    match stampText?, env?, source? with
    | some stampText, some env, some source =>
        match NativeCheck.stampParts stampText with
        | none => some (false, false)
        | some (recordedSource, recordedToolchain) =>
            some (recordedSource == toString (hash source),
              recordedToolchain == toString (hash env.toolchain))
    | _, _, _ => none

  let build : BuildState :=
    match entry.emitted with
    | .error errors => .emitFailed errors.toList
    | .ok _ =>
        match stampState with
        | some (true, true) => .compiled
        | _ =>
            match record? with
            | none => .notCompiled
            | some record =>
                if record.outcome == Attest.RunOutcome.compileFailed then
                  .rejected
                    s!"ccomp rejected this program at {record.recordedAt} \
                       (exit {record.exitCode}); that is not the same as never \
                       having tried"
                else if !record.outcome.compiled then
                  .notCompiled
                else if !recordCurrent then
                  .staleCompile
                    s!"ccomp last accepted C with digest {record.sourceDigest}, \
                       which is not the C this build emits"
                else if !recordToolchainCurrent then
                  .staleCompile
                    s!"this C was accepted by a different CompCert install \
                       ({record.ccompVersion}, identity {record.ccompDigest})"
                else
                  .compiled

  let run : RunState :=
    match entry.emitted with
    | .error _ => .notRun "the C does not emit, so there is nothing to run"
    | .ok _ =>
        match stampState with
        | some (true, true) => .ran
        | some (true, false) =>
            .stale
              "the generated C is unchanged but the toolchain key is not: a \
               different CompCert, target, startup stub, or machine"
        | some (false, true) =>
            .stale
              "the generated C has CHANGED since the last passing run; the run \
               was of a different binary"
        | some (false, false) =>
            .stale
              "neither the generated C nor the toolchain matches the last \
               passing run"
        | none =>
            if env?.isNone then
              .stale
                "the toolchain could not be resolved here (no ccomp, or no \
                 startup stub), so no stamp can be shown to belong to this \
                 environment"
            else
              match record?, recordUnreadable? with
              | _, some why => .notRun why
              | none, none =>
                  .notRun "no stamp and no run record: never built here"
              | some record, none =>
                  -- Everything below is about a record whose C is the C this
                  -- build emits.  Without that guard a leftover record from an
                  -- older version of the program would produce a headline —
                  -- `FAILED (disagrees)`, the strongest accusation here — about
                  -- C that has never been compiled on this machine.
                  if !recordCurrent then
                    .stale
                      s!"the only evidence here is a run record from \
                         {record.recordedAt}, and it is about C with digest \
                         {record.sourceDigest}, not the C this build emits"
                  else
                    match record.outcome with
                    | .agrees =>
                        .notRun
                          s!"a run at {record.recordedAt} agreed on this exact \
                             C, but its stamp is gone; re-run to restore the \
                             evidence"
                    | outcome =>
                        -- `FAILED` is about an *execution* that went wrong.  A
                        -- program `ccomp` rejected, or that failed to link, was
                        -- never executed at all, and saying it "failed" would
                        -- overstate what is known about the binary — there is
                        -- no binary.
                        if outcome.executed then
                          .failed outcome
                            s!"last attempt {record.recordedAt} exited \
                               {record.exitCode}"
                        else
                          .notRun
                            s!"nothing has executed: the last attempt at \
                               {record.recordedAt} ended at {outcome.label} \
                               (exit {record.exitCode})"

  let receipt : ReceiptState ←
    match receiptText? with
    | none => pure .absent
    | some text =>
        match Attest.Tool.parseReceipt text with
        | .error message => pure (.unreadable message)
        | .ok parsed =>
            if parsed.verdict != Attest.RunVerdict.agrees then
              pure (.stale s!"its verdict is '{parsed.verdict.label}', not 'agrees'")
            else if parsed.routeLabel != entry.routeLabel then
              pure (.stale
                s!"it is filed under route '{parsed.routeLabel}' and this \
                   program emits '{entry.routeLabel}'")
            else if entry.certifiedValue.isNone then
              -- `receiptBinds` takes the certified value as an argument, so a
              -- receipt for a program that names no value binds to nothing —
              -- it would tie a signature to a program and a machine but not to
              -- an answer.  The runner refuses to write one; the ledger must
              -- not show a reassuring CURRENT for one that exists anyway.
              pure (.stale
                s!"the receipt records {parsed.value} and this program declares \
                   no certifiedValue, so nothing says that is the answer")
            else if entry.certifiedValue != some parsed.value then
              pure (.stale
                s!"it records the value {parsed.value} and this program \
                   certifies {entry.certifiedValue.getD 0}")
            else if opts.nonce.isSome && opts.nonce != some parsed.nonce then
              -- `--nonce` is a challenge.  A receipt quoting a different one
              -- does not answer it, and `receiptBinds` refuses it.
              pure (.stale
                s!"it quotes nonce {parsed.nonce} and the challenge is \
                   {opts.nonce.getD ""}")
            else if paramsHash?.isSome && paramsHash? != some parsed.paramsHash then
              pure (.stale
                s!"it records paramsHash {parsed.paramsHash} and the supplied \
                   --params digest to {paramsHash?.getD ""}")
            else
              match sourceDigest? with
              | none =>
                  pure (.stale
                    "the C this build emits could not be digested, so the \
                     receipt cannot be compared against it")
              | some digest =>
                  if parsed.programHash == digest then
                    pure (.current parsed.recordedAt parsed.attestation.label)
                  else
                    pure (.stale
                      s!"its programHash {parsed.programHash} is not the digest \
                         of the C this build emits")

  let chain : ChainState :=
    match entry.leanSide with
    | .chained _ c => .proved c.proposition c.provedBy
    | .artifactOnly _ why => .notProved why
    | .unbindable why => .notProved why

  return {
    name := entry.name
    summary := entry.summary
    routeLabel := entry.routeLabel
    entryPoint := entry.entryPoint
    certifiedValue := entry.certifiedValue
    shape := entry.shape
    parameters := entry.parameters
    denotation := entry.denotation
    sourceDigest := sourceDigest?
    sourceBytes := source?.map (·.utf8ByteSize)
    build, run, receipt, chain
    bindable := entry.bindable
    bindableWhy :=
      match entry.leanSide with
      | .unbindable why => why
      | _ => ""
    record := record?
    recordUnreadable := recordUnreadable?
    defects := defectsOf entry }

/-! ## The human table -/

private def pad (width : Nat) (text : String) : String :=
  if text.length ≥ width then text
  else text ++ String.ofList (List.replicate (width - text.length) ' ')

private def columnWidth (rows : List LedgerRow) (field : LedgerRow → String)
    (header : String) : Nat :=
  rows.foldl (fun acc row => max acc (field row).length) header.length

/-- The table.  Six columns, and three of them — `compiled`, `run`, `chain` —
are the three states that must never be collapsed. -/
def renderTable (rows : List LedgerRow) : List String := Id.run do
  let nameW := columnWidth rows (·.name) "program"
  let routeW := columnWidth rows (·.routeLabel) "route"
  let buildW := columnWidth rows (·.build.label) "compiled"
  let runW := columnWidth rows (·.run.label) "run"
  let receiptW := columnWidth rows (·.receipt.label) "receipt"
  let chainW := columnWidth rows (·.chain.label) "chain proved"
  let header :=
    pad nameW "program" ++ "  " ++ pad routeW "route" ++ "  " ++
    pad buildW "compiled" ++ "  " ++ pad runW "run" ++ "  " ++
    pad receiptW "receipt" ++ "  " ++ pad chainW "chain proved" ++ "  bindable"
  let rule :=
    String.ofList (List.replicate header.length '-')
  let mut lines := [header, rule]
  for row in rows do
    lines := lines ++ [
      pad nameW row.name ++ "  " ++ pad routeW row.routeLabel ++ "  " ++
      pad buildW row.build.label ++ "  " ++ pad runW row.run.label ++ "  " ++
      pad receiptW row.receipt.label ++ "  " ++ pad chainW row.chain.label ++
      "  " ++ (if row.bindable then "yes" else "NO")]
  return lines

/-- Everything a row says that a six-column table cannot: the reason behind
every state that is not a plain pass, and every structural defect. -/
def renderNotes (rows : List LedgerRow) : List String := Id.run do
  let mut lines : List String := []
  for row in rows do
    let mut notes : List String := []
    match row.build with
    | .emitFailed errors =>
        notes := notes ++ [s!"compiled: EMIT FAILED — {String.intercalate "; " errors}"]
    | .notCompiled => notes := notes ++ ["compiled: NOT COMPILED — no record of ccomp accepting this program here"]
    | .rejected why => notes := notes ++ [s!"compiled: REJECTED — {why}"]
    | .staleCompile why => notes := notes ++ [s!"compiled: STALE — {why}"]
    | .compiled => pure ()
    match row.run with
    | .notRun why => notes := notes ++ [s!"run: NOT RUN — {why}"]
    | .stale why => notes := notes ++ [s!"run: STALE — {why}"]
    | .failed outcome detail =>
        notes := notes ++ [s!"run: FAILED ({outcome.label}) — {detail}"]
    | .ran => pure ()
    match row.receipt with
    | .absent => pure ()
    | .unreadable why => notes := notes ++ [s!"receipt: UNREADABLE — {why}"]
    | .stale why => notes := notes ++ [s!"receipt: STALE — {why}"]
    | .current at' kind =>
        notes := notes ++ [s!"receipt: current, {kind}, recorded {at'}"]
    match row.chain with
    | .notProved why => notes := notes ++ [s!"chain: NOT PROVED — {why}"]
    | .proved proposition provedBy =>
        notes := notes ++ [s!"chain: PROVED by {provedBy}"]
        notes := notes ++ [s!"       a run bears on: {proposition}"]
    if let some why := row.recordUnreadable then
      -- When the run column already carries this sentence, printing it twice
      -- buries the row's other notes; see the `bindable` case below.
      let runWhy :=
        match row.run with
        | .notRun w => w
        | .stale w => w
        | .failed _ w => w
        | .ran => ""
      if why != runWhy then
        notes := notes ++ [s!"run record: UNREADABLE — {why}"]
    if row.receipt.ok && !row.bindable then
      notes := notes ++ [
        "receipt: current against the emitted C, but this program is NOT \
         bindable — no receiptBinds can ever be applied to it"]
    if !row.bindable then
      -- For an `.unbindable` entry the registrar's reason is the same sentence
      -- in both columns; printing it twice buries the row's other notes.
      let chainWhy :=
        match row.chain with
        | .notProved why => why
        | .proved _ _ => ""
      if row.bindableWhy == chainWhy then
        notes := notes ++ [
          "bindable: NO — no Artifact reproduces this program's C, so \
           receiptBinds can never be applied to a receipt for it (reason above)"]
      else
        notes := notes ++ [s!"bindable: NO — {row.bindableWhy}"]
    for defect in row.defects do
      notes := notes ++ [s!"DEFECT: {defect}"]
    if !notes.isEmpty then
      lines := lines ++ [s!"{row.name}:"] ++ notes.map ("  " ++ ·) ++ [""]
  return lines

/-! ## JSON -/

open Lean in
private def optString (value : Option String) : Json :=
  match value with
  | none => Json.null
  | some text => Json.str text

open Lean in
private def optNat (value : Option Nat) : Json :=
  match value with
  | none => Json.null
  | some n => Lean.toJson n

open Lean in
private def stateJson (label : String) (ok : Bool) (detail : String) : Json :=
  Json.mkObj [("state", Json.str label), ("ok", Json.bool ok),
    ("detail", if detail.isEmpty then Json.null else Json.str detail)]

open Lean in
def recordJson : Option RunRecord → Json
  | none => Json.null
  | some r => Json.mkObj [
      ("recordedAt", Json.str r.recordedAt),
      ("sourceDigest", Json.str r.sourceDigest),
      ("sourceBytes", Lean.toJson r.sourceBytes),
      ("ccompVersion", Json.str r.ccompVersion),
      ("ccompDigest", Json.str r.ccompDigest),
      ("linkDescription", Json.str r.linkDescription),
      ("machine", Json.str r.machine),
      ("exitCode", Lean.toJson r.exitCode),
      ("outcome", Json.str r.outcome.label),
      ("certifiedValue", Json.str r.certifiedValue),
      ("receiptPath", Json.str r.receiptPath)]

open Lean in
def shapeJson (shape : ProgramShape) : Json :=
  Json.mkObj [
    ("family", Json.str shape.family),
    ("regCount", optNat shape.regCount),
    ("arrayLen", optNat shape.arrayLen),
    ("loopCount", optNat shape.loopCount),
    ("initInstrs", optNat shape.initInstrs),
    ("bodyInstrs", optNat shape.bodyInstrs),
    ("epilogueInstrs", optNat shape.epilogueInstrs),
    ("outputReg", optNat shape.outputReg),
    ("dynamicInstrs", optNat shape.dynamicInstrs),
    ("ccirInstrs", optNat shape.ccirInstrs),
    ("cStatements", optNat shape.cStatements),
    ("ccirFunction", optString shape.ccirFunction)]

open Lean in
def denotationJson : Option DenotationNote → Json
  | none => Json.null
  | some note => Json.mkObj [
      ("theoremName", Json.str note.theoremName),
      ("statement", Json.str note.statement),
      ("atTheseParameters", Json.bool note.atTheseParameters),
      ("gap", if note.gap.isEmpty then Json.null else Json.str note.gap)]

open Lean in
def rowJson (row : LedgerRow) : Json :=
  Json.mkObj [
    ("name", Json.str row.name),
    ("summary", Json.str row.summary),
    ("route", Json.str row.routeLabel),
    ("entryPoint", Json.str row.entryPoint),
    ("certifiedValue", optString (row.certifiedValue.map toString)),
    ("shape", shapeJson row.shape),
    ("parameters",
      Json.mkObj (row.parameters.map (fun (k, v) => (k, Json.str v)))),
    ("denotation", denotationJson row.denotation),
    ("sourceDigest", optString row.sourceDigest),
    ("sourceBytes", optNat row.sourceBytes),
    ("compiled", stateJson row.build.label row.build.ok
      (match row.build with
        | .emitFailed errors => String.intercalate "; " errors
        | .rejected why => why
        | .staleCompile why => why
        | .notCompiled => "no record of ccomp accepting this program here"
        | .compiled => "")),
    ("run", stateJson row.run.label row.run.ok
      (match row.run with
        | .notRun why => why
        | .stale why => why
        | .failed _ detail => detail
        | .ran => "")),
    ("receipt", stateJson row.receipt.label row.receipt.ok
      (match row.receipt with
        | .absent => ""
        | .unreadable why => why
        | .stale why => why
        | .current at' kind => s!"{kind}, recorded {at'}")),
    ("chainProved", Json.bool row.chain.ok),
    ("chain", Json.mkObj [
      ("state", Json.str row.chain.label),
      ("proposition", match row.chain with
        | .proved proposition _ => Json.str proposition
        | .notProved _ => Json.null),
      ("provedBy", match row.chain with
        | .proved _ provedBy => Json.str provedBy
        | .notProved _ => Json.null),
      ("gap", match row.chain with
        | .proved _ _ => Json.null
        | .notProved why => Json.str why)]),
    ("bindable", Json.bool row.bindable),
    ("bindableWhy",
      if row.bindableWhy.isEmpty then Json.null else Json.str row.bindableWhy),
    ("lastAttempt", recordJson row.record),
    ("lastAttemptUnreadable", optString row.recordUnreadable),
    ("defects", Json.arr ((row.defects.map Json.str).toArray)),
    ("clean", Json.bool row.clean)]

open Lean in
def ledgerJson (rows : List LedgerRow) (toolchain : Option String) : Json :=
  Json.mkObj [
    ("schema", Json.str "leancompcert-ledger/1"),
    ("toolchainResolved", Json.bool toolchain.isSome),
    ("toolchain", optString toolchain),
    ("programs", Lean.toJson rows.length),
    ("compiled", Lean.toJson (rows.filter (·.build.ok)).length),
    ("run", Lean.toJson (rows.filter (·.run.ok)).length),
    ("receipts", Lean.toJson (rows.filter (·.receipt.ok)).length),
    ("chainProved", Lean.toJson (rows.filter (·.chain.ok)).length),
    ("bindable", Lean.toJson (rows.filter (·.bindable)).length),
    ("defects", Lean.toJson (rows.filter (!·.clean)).length),
    ("rows", Json.arr ((rows.map rowJson).toArray))]

/-! ## `describe` -/

private def optLine (label : String) : Option Nat → List String
  | none => []
  | some n => [s!"  {label}: {n}"]

private def shapeLines (shape : ProgramShape) : List String :=
  [s!"  family: {shape.family}"]
    ++ optLine "registers" shape.regCount
    ++ optLine "array cells" shape.arrayLen
    ++ optLine "loop trip count" shape.loopCount
    ++ optLine "init instructions" shape.initInstrs
    ++ optLine "body instructions (per trip)" shape.bodyInstrs
    ++ optLine "epilogue instructions" shape.epilogueInstrs
    ++ optLine "instructions executed" shape.dynamicInstrs
    ++ optLine "output register" shape.outputReg
    ++ optLine "CCIR straight-line instructions" shape.ccirInstrs
    ++ optLine "restricted-C statements" shape.cStatements
    ++ (match shape.ccirFunction with
        | none => []
        | some name => [s!"  CCIR function: {name}"])

/-- **What is in the compiled program.**

A reviewer should be able to answer "what does this binary actually compute?"
from this output alone, without reading the emitter: the shape, the parameters,
the denotation theorem and what it says, the digest and size of the exact bytes
`ccomp` was handed, the toolchain that last compiled them, and the three
states. -/
def describeLines (entry : ProgramEntry) (row : LedgerRow)
    (listingLimit : Option Nat) : List String := Id.run do
  let mut lines : List String := []
  lines := lines ++ [s!"program {entry.name}", s!"  {entry.summary}", ""]
  lines := lines ++ ["shape"] ++ shapeLines entry.shape ++ [""]
  if entry.parameters.isEmpty then
    lines := lines ++ ["parameters", "  (none declared)", ""]
  else
    lines := lines ++ ["parameters"]
      ++ entry.parameters.map (fun (k, v) => s!"  {k} = {v}") ++ [""]
  lines := lines ++ ["emitted C"]
  lines := lines ++ [s!"  route: {entry.routeLabel}"]
  lines := lines ++ [s!"  entry point: {entry.entryPoint}"]
  lines := lines ++ [
    match row.sourceDigest with
    | some digest => s!"  sha256: {digest}"
    | none => "  sha256: UNAVAILABLE — the C does not emit"]
  lines := lines ++ [
    match row.sourceBytes with
    | some n => s!"  size: {n} bytes"
    | none => "  size: -"]
  lines := lines ++ [
    match entry.certifiedValue with
    | some value => s!"  the emitted main self-checks against: {value}"
    | none => "  the emitted main self-checks against: NOTHING DECLARED"]
  lines := lines ++ [""]

  lines := lines ++ ["denotation theorem"]
  match entry.denotation with
  | none =>
      lines := lines ++ [
        "  NONE — nothing in Lean says what this program's `denote` computes."]
  | some note =>
      lines := lines ++ [s!"  {note.theoremName}", s!"  says: {note.statement}"]
      lines := lines ++ [
        if note.atTheseParameters then
          "  instantiated at these parameters: yes"
        else
          "  instantiated at these parameters: NO"]
      -- Printed whenever it is non-empty, not only when the theorem is at
      -- other parameters.  A theorem CAN be about this binary and still not
      -- say what its number means, and that caveat has to be visible.
      if !note.gap.isEmpty then
        lines := lines ++ [s!"  gap: {note.gap}"]
  lines := lines ++ [""]

  lines := lines ++ ["the three states, kept apart"]
  lines := lines ++ [s!"  compiled     {row.build.label}"]
  lines := lines ++ [s!"  run          {row.run.label}"]
  lines := lines ++ [s!"  chain proved {row.chain.label}"]
  let bindableText := if row.bindable then "yes" else "NO"
  lines := lines ++ [s!"  bindable     {bindableText}"]
  lines := lines ++ [""]

  lines := lines ++ ["what a successful run bears on"]
  match entry.leanSide with
  | .chained _ c =>
      lines := lines ++ [s!"  proposition: {c.proposition}"]
      lines := lines ++ [s!"  proved by: {c.provedBy}"]
      lines := lines ++ [s!"  accepting value: {c.acceptingValue}"]
      lines := lines ++ [
        "  A bound receipt plus an admitted run gives this proposition, by",
        "  Attest.ChainProof.prop_of_receipt.  RunAdmission is still the",
        "  empirical premise and is still not proved here."]
  | .artifactOnly _ why =>
      lines := lines ++ [
        "  NOTHING.  A receipt for this program can be checked by receiptBinds,",
        "  and no proved arrow runs from the value it reports to any",
        "  mathematical statement.",
        s!"  gap: {why}"]
  | .unbindable why =>
      lines := lines ++ [
        "  NOTHING, and no receipt for it can even be checked in the kernel.",
        s!"  gap: {why}"]
  lines := lines ++ [""]

  lines := lines ++ ["last attempt"]
  match row.record, row.recordUnreadable with
  | _, some why =>
      lines := lines ++ [s!"  UNREADABLE RECORD — {why}"]
  | none, none =>
      lines := lines ++ [
        "  NO RECORD — this program has not been built in this directory."]
  | some record, none =>
      lines := lines ++ [
        s!"  at: {record.recordedAt}",
        s!"  outcome: {record.outcome.label} (exit {record.exitCode})",
        s!"  C compiled: sha256 {record.sourceDigest}, {record.sourceBytes} bytes",
        s!"  ccomp: {record.ccompVersion}",
        s!"  ccomp identity digest: {record.ccompDigest}",
        s!"  link: {record.linkDescription}",
        s!"  machine: {record.machine}",
        s!"  self-checked against: {record.certifiedValue}",
        s!"  receipt: {record.receiptPath}"]
  lines := lines ++ [""]

  if !row.defects.isEmpty then
    lines := lines ++ ["DEFECTS"]
      ++ row.defects.map ("  " ++ ·) ++ [""]

  let listing := entry.listing.get
  if !listing.isEmpty then
    let all := listing.splitOn "\n"
    let shown :=
      match listingLimit with
      | none => all
      | some limit =>
          if all.length ≤ limit then all
          else all.take limit ++ [s!"… {all.length - limit} more lines (--full)"]
    lines := lines ++ ["instruction listing"] ++ shown.map ("  " ++ ·) ++ [""]

  return lines

/-! ## The verbs -/

private structure LedgerArgs where
  json : Bool := false
  full : Bool := false
  source : Bool := false
  rest : List String := []

private def parseLedgerArgs : List String → LedgerArgs
  | [] => {}
  | "--json" :: rest => { parseLedgerArgs rest with json := true }
  | "--full" :: rest => { parseLedgerArgs rest with full := true }
  | "--source" :: rest => { parseLedgerArgs rest with source := true }
  | arg :: rest =>
      let parsed := parseLedgerArgs rest
      { parsed with rest := arg :: parsed.rest }

/-- The digest of the caller's `--params` file, when there is one.

`none` means the caller supplied no parameter block, and the ledger then makes
no claim about a receipt's `paramsHash` — it has nothing to compare against, and
inventing a value would be worse than saying nothing. -/
private def resolveParamsHash (opts : NativeCheck.Options)
    (env? : Option NativeCheck.Environment) : IO (Option String) := do
  let some path := opts.paramsFile | return none
  let some text ← readIfPresent path | return none
  let scratch :=
    match env? with
    | some env => env.scratch
    | none => opts.dir / "digest-scratch"
  digest? scratch text

/-- Resolve the environment, reporting rather than failing when it cannot be
resolved.  The ledger is a reporting tool: on a machine with no CompCert it
must still say what is registered, and must say that it cannot judge the
stamps. -/
private def resolve (opts : NativeCheck.Options) :
    IO (Option NativeCheck.Environment × Option String) := do
  match ← NativeCheck.resolveEnvironment opts with
  | .ok env => return (some env, none)
  | .error message => return (none, some message)

/-- `lean-compcert ledger [--json] [check-native options]`. -/
def ledgerVerb (entries : List ProgramEntry) (args : List String) :
    IO UInt32 := do
  let parsed := parseLedgerArgs args
  let opts ←
    match NativeCheck.parseOptions parsed.rest with
    | .error message => IO.eprintln s!"error: {message}"; return 2
    | .ok opts => pure opts
  let (env?, why?) ← resolve opts
  let paramsHash? ← resolveParamsHash opts env?
  let mut rows : List LedgerRow := []
  for entry in entries do
    rows := rows ++ [← rowFor opts env? paramsHash? entry]
  let defective := (rows.filter (!·.clean)).length
  if parsed.json then
    IO.println (ledgerJson rows (env?.map (·.toolchain))).pretty
  else
    if let some why := why? then
      IO.println
        "! the toolchain could not be resolved, so no stamp can be shown to"
      IO.println
        "! belong to this environment; every run state below reads STALE."
      IO.println s!"!   {why}"
      IO.println ""
    IO.println s!"native-check directory: {opts.dir}"
    IO.println s!"receipt directory:      {NativeCheck.defaultReceiptDir opts}"
    IO.println ""
    for line in renderTable rows do
      IO.println line
    IO.println ""
    let notes := renderNotes rows
    if !notes.isEmpty then
      for line in notes do
        IO.println line
    IO.println
      s!"{rows.length} registered; {(rows.filter (·.build.ok)).length} compiled, \
         {(rows.filter (·.run.ok)).length} run, \
         {(rows.filter (·.receipt.ok)).length} with a current receipt, \
         {(rows.filter (·.chain.ok)).length} chain proved, \
         {(rows.filter (·.bindable)).length} bindable"
    IO.println
      "compiled, run and chain proved are three independent facts.  A green run"
    IO.println
      "does not make a green chain: it says a binary agreed with a constant, not"
    IO.println
      "that any Lean statement follows from it."
  if defective != 0 then
    IO.eprintln s!"ledger: {defective} row(s) have structural defects"
    return 1
  return 0

/-- `lean-compcert describe NAME [--full] [--source]`. -/
def describeVerb (entries : List ProgramEntry) (args : List String) :
    IO UInt32 := do
  let parsed := parseLedgerArgs args
  let some name := parsed.rest.head?
    | IO.eprintln "error: describe needs a program name"
      IO.eprintln
        s!"       known: {String.intercalate ", " (entries.map (·.name))}"
      return 2
  let some entry := entries.find? (·.name == name)
    | IO.eprintln s!"error: no registered program named '{name}'"
      IO.eprintln
        s!"       known: {String.intercalate ", " (entries.map (·.name))}"
      return 2
  let opts ←
    match NativeCheck.parseOptions (parsed.rest.drop 1) with
    | .error message => IO.eprintln s!"error: {message}"; return 2
    | .ok opts => pure opts
  let (env?, _) ← resolve opts
  let paramsHash? ← resolveParamsHash opts env?
  let row ← rowFor opts env? paramsHash? entry
  for line in describeLines entry row
      (if parsed.full then none else some 60) do
    IO.println line
  if parsed.source then
    match entry.emitted with
    | .error errors =>
        IO.eprintln "the C does not emit:"
        for error in errors do
          IO.eprintln s!"  {error}"
        return 1
    | .ok source =>
        IO.println "emitted C"
        IO.println source
  if !row.clean then
    IO.eprintln s!"describe: {row.defects.length} structural defect(s)"
    return 1
  return 0

end LeanCompCert.Attest.Ledger
