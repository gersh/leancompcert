import LeanCompCert.Attest.Ledger

/-!
# Cached native cross-check runner

`lean-compcert check-native` gives the `native_decide`-style workflow —
run the computation as fast native code — without ever admitting the
run's outcome as a theorem.  Each registered certificate's generated C
(whose `main` returns 0 exactly when the computed value equals the
certified constant, and 1 exactly when it does not) is compiled with
CompCert and executed, and the result is cached by *content hash*: a
certificate is re-compiled and re-run only when its generated C, the
ccomp version, the link mode, or the startup stub actually changes.

Linking is **freestanding** by default: `ccomp -c` produces an object
with zero undefined symbols, which is assembled together with the tiny
`runtime/start/<arch>.S` entry stub by `as` and linked by `ld` with no
libc, no dynamic loader and no gcc startup glue.  `--hosted` restores
the old single-step `ccomp -o exe exe.c` link for comparison.

Exit-status contract (see `runtime/start/README.md`):

* `0` — the computed value equals the certified constant;
* `1` — it does not (a genuine *disagreement*);
* anything else — **abnormal termination** (`128 + signal`: `134`
  `SIGABRT`, `137` `SIGKILL`/OOM, `139` `SIGSEGV`, …).

An abnormal termination is never reported as a disagreement.  Both
classes fail the check — the runner is fail-closed — but they are
distinct, because "the artifact was killed" says nothing at all about
whether the computed value matches.

Change tracking is two-layered: Lake rebuilds `lean-compcert` when any
certificate's Lean source changes, and this runner re-emits the C
in-memory (cheap) and compares its hash against the stamp of the last
passing run.  Stamps are written only on a passing run, so a failure is
always retried.

The cross-check is corroboration, never a premise: the theorems are
established by `verified_decide` in the kernel, and nothing here feeds
back into Lean's proof state.

## `--attest`: the same run, with a signed record of it

With `--attest` a passing run additionally writes a **run receipt**
(`LeanCompCert/Attest/Receipt.lean`): the digest of the exact C text
compiled, the digest of the inputs, the CompCert identity, the machine
identity, a nonce, a timestamp and the reported value, all under one
signature.  The caching is unchanged — a certificate whose C has not
changed is still not recompiled, and its existing receipt is kept.

A receipt is **not** a premise either.  It becomes one only when a
consumer imports a discharger and applies `Attest.receiptBinds`; see
`docs/use-case-3-attested-run-receipts.md`.  With a locally generated
key it is tamper-evident bookkeeping and nothing stronger — read
`LeanCompCert/Trusted/LocalReceipt.lean` before relying on one.
-/

namespace LeanCompCert.NativeCheck

open LeanCompCert.Attest

structure Cert where
  name : String
  emitted : Except (Array String) String
  /-- Which emitter produced `emitted`.  Must match the `Artifact.route`
  the consumer's Lean-side check uses, because `receiptBinds` compares
  the labels; see `Attest.EmissionRoute`. -/
  routeLabel : String := EmissionRoute.provedStraightLine.label
  /-- The constant the generated `main` compares against — the value this
  certificate certifies.

  Required by `--attest` and by nothing else, so registering a
  certificate for the plain cross-check is unchanged.  A certificate
  without it cannot be attested, because a receipt that did not name the
  value would bind a signature to a program and a machine but not to an
  answer.

  ⚠ Build the `main` from *this* number (`Attest.selfCheckMain`) rather
  than spelling the literal twice.  If the `main` tests one constant and
  the receipt records another, the Lean-side check still passes — both
  sides would agree with each other while the artifact tested something
  else.  Deriving both from one value closes that by construction. -/
  certifiedValue : Option Int := none

/-- The cross-check unit a ledger entry names.

One list, not two: a program is registered once, and both the runner and the
ledger read the same registration.  Keeping them apart is how a ledger comes to
describe a program the runner does not compile, or the reverse. -/
def Cert.ofEntry (entry : Attest.ProgramEntry) : Cert := {
  name := entry.name
  emitted := entry.emitted
  routeLabel := entry.routeLabel
  certifiedValue := entry.certifiedValue
}

/-- How the compiled object becomes an executable. -/
inductive LinkMode where
  /-- `ccomp -c` + `as` on the startup stub + `ld`; no libc. -/
  | freestanding
  /-- `ccomp -o exe exe.c`; gcc's startup glue links glibc. -/
  | hosted
  deriving DecidableEq, Repr

def LinkMode.describe : LinkMode → String
  | .freestanding => "freestanding"
  | .hosted => "hosted"

structure Options where
  dir : System.FilePath := ".lake" / "build" / "native-check"
  force : Bool := false
  extraIncludes : List String := []
  linkMode : LinkMode := .freestanding
  /-- Directory holding the `<arch>.S` startup stubs.  When `none`, a
  short list of candidates relative to the working directory is tried,
  then `$LEAN_COMPCERT_START_DIR`. -/
  startDir : Option System.FilePath := none
  /-- Write a signed run receipt for every passing run. -/
  attest : Bool := false
  /-- Private signing key.  Defaults to `Attest.Tool.defaultKeyPath`. -/
  keyPath : Option System.FilePath := none
  /-- Where receipts are written.  Defaults to `<dir>/receipts`. -/
  receiptDir : Option System.FilePath := none
  /-- Campaign label recorded in every receipt. -/
  campaign : Option String := none
  /-- Challenge nonce.  When absent, a fresh one is drawn for each
  certificate that actually runs; an existing receipt is then honoured
  whatever nonce it quotes.  When present, a receipt quoting a different
  nonce is discarded and the artifact re-runs. -/
  nonce : Option String := none
  /-- File holding the canonical inputs.  Absent means the empty input,
  which is the right answer for a closed certificate. -/
  paramsFile : Option System.FilePath := none

def parseOptions : List String → Except String Options
  | [] => .ok {}
  | "--force" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with force := true }
  | "--attest" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with attest := true }
  | "--key" :: path :: rest => do
      let opts ← parseOptions rest
      .ok { opts with keyPath := some path }
  | "--receipts" :: path :: rest => do
      let opts ← parseOptions rest
      .ok { opts with receiptDir := some path }
  | "--campaign" :: name :: rest => do
      let opts ← parseOptions rest
      .ok { opts with campaign := some name }
  | "--nonce" :: hex :: rest => do
      let opts ← parseOptions rest
      .ok { opts with nonce := some hex }
  | "--params" :: path :: rest => do
      let opts ← parseOptions rest
      .ok { opts with paramsFile := some path }
  | "--hosted" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with linkMode := .hosted }
  | "--freestanding" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with linkMode := .freestanding }
  | "--dir" :: dir :: rest => do
      let opts ← parseOptions rest
      .ok { opts with dir := dir }
  | "--include" :: dir :: rest => do
      let opts ← parseOptions rest
      .ok { opts with extraIncludes := dir :: opts.extraIncludes }
  | "--start-dir" :: dir :: rest => do
      let opts ← parseOptions rest
      .ok { opts with startDir := some dir }
  | arg :: _ => .error s!"unknown check-native argument '{arg}'"

private def firstLine (s : String) : String :=
  ((s.splitOn "\n").headD "").trimAscii.toString

private def toolVersion (cmd : String) (args : Array String) :
    IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    if out.exitCode == 0 then
      let text := out.stdout.trimAscii.toString
      return some (if text.isEmpty then firstLine out.stderr else text)
    return none
  catch _ =>
    return none

private def ccompVersion : IO (Option String) :=
  toolVersion "ccomp" #["-version"]

/-- Identity of the actual CompCert install: a digest of the `ccomp`
binary plus the full text of its `compcert.ini`.

This exists because `ccomp -version` is not enough to tell two installs
apart.  It prints only

    The CompCert C verified compiler, version 3.17

with **no architecture**, so a CompCert configured `aarch64-linux` and one
configured `x86_64-linux` are indistinguishable by version string — and
`arch`, `abi`, `prepro_options`, `asm_options` and `linker_options` all
live in `compcert.ini`, which nothing else here reads.  Cross-compiling is
routine (an `x86_64` CompCert on an `aarch64` host is a supported setup),
and the freestanding link description records `uname -m`, the *host*
machine, not the compiler's *target*.  Without this, a stamp written by
one install would be silently honoured by the other.

Hashing the binary as well means a CompCert rebuilt from patched sources
at the same release number also invalidates stamps.

Failure to resolve any of it yields a constant marker rather than an
error: a missing `compcert.ini` should not break the run, it should just
stop the stamp from claiming more machine-specificity than it has. -/
private def compcertIdentity : IO String := do
  let script :=
    "p=$(command -v ccomp) || exit 1; \
     { sha256sum \"$p\" 2>/dev/null || shasum -a 256 \"$p\" 2>/dev/null || echo no-digest; } \
       | awk '{print \"bin \" $1}'; \
     for c in \"$(dirname \"$p\")/compcert.ini\" \
              \"$(dirname \"$(dirname \"$p\")\")/share/compcert.ini\" \
              /usr/local/share/compcert.ini; do \
       if [ -f \"$c\" ]; then echo 'ini'; cat \"$c\"; exit 0; fi; \
     done; echo 'ini absent'"
  try
    let out ← IO.Process.output { cmd := "sh", args := #["-c", script] }
    if out.exitCode == 0 && !out.stdout.trimAscii.isEmpty then
      return out.stdout.trimAscii.toString
    return "compcert-identity-unavailable"
  catch _ =>
    return "compcert-identity-unavailable"

/-- Identity of the machine the check runs on.

Without this, the cache directory is portable: copying
`.lake/build/native-check/` to another host carries the stamps *and* the
compiled binaries, so a machine that never ran anything reports
`cached` and `pass`.  A shared Docker layer, a restored backup, or an
`rsync` of a checkout is enough to produce that by accident.

Prefers `/etc/machine-id` (persistent per installation, and not secret —
it is a stable identifier, not a credential), then dbus's copy, then
hostname plus `uname -m -s`.  The fallback is weaker but still catches
the common accidents.

**This makes the cache honest, not tamper-proof.** The stamp is an
unsigned file in a directory you own; anyone who can copy it can also
edit it. It defends against a build tree arriving from somewhere else,
which is the realistic failure, not against someone determined to forge
a pass. For evidence that survives an adversary, the artifact has to be
re-run — or run under attestation.

Set `LEAN_COMPCERT_SHARED_CACHE=1` to omit this, which is what you want
if you are deliberately sharing a cache between identical containers and
accept that a hit no longer means "it ran here". -/
private def machineIdentity : IO String := do
  if (← IO.getEnv "LEAN_COMPCERT_SHARED_CACHE") == some "1" then
    return "machine shared-cache-opt-out"
  let script :=
    "if [ -r /etc/machine-id ]; then echo \"id $(cat /etc/machine-id)\"; \
     elif [ -r /var/lib/dbus/machine-id ]; then echo \"id $(cat /var/lib/dbus/machine-id)\"; \
     else echo \"host $(uname -n) $(uname -m) $(uname -s)\"; fi"
  try
    let out ← IO.Process.output { cmd := "sh", args := #["-c", script] }
    if out.exitCode == 0 && !out.stdout.trimAscii.isEmpty then
      return s!"machine {out.stdout.trimAscii}"
    return "machine unidentified"
  catch _ =>
    return "machine unidentified"

/-- Host architecture, normalised to the basename of the startup stub in
`runtime/start/`.  `System.Platform` exposes OS and word size but not the
machine type, so this shells out to `uname -m`. -/
private def hostArch : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "uname", args := #["-m"] }
    if out.exitCode != 0 then return none
    match out.stdout.trimAscii.toString with
    | "aarch64" => return some "aarch64"
    | "arm64" => return some "aarch64"
    | "x86_64" => return some "x86_64"
    | "amd64" => return some "x86_64"
    | _ => return none
  catch _ =>
    return none

/-- Content hash of every regular file under `dir` (path and text),
order-independent of directory enumeration. Unreadable files fall back
to their size. Used so that edits to header directories (e.g. a
caller-supplied `--include` directory) invalidate stamps. -/
private def dirContentHash (dir : System.FilePath) : IO UInt64 := do
  if !(← dir.pathExists) then
    return 0
  let entries ← dir.walkDir
  let sorted := entries.qsort (·.toString < ·.toString)
  let mut h : UInt64 := 0
  for entry in sorted do
    let info ← entry.metadata
    if info.type == IO.FS.FileType.file then
      let contentHash ←
        try
          pure (hash (← IO.FS.readFile entry))
        catch _ =>
          pure (hash info.byteSize.toNat)
      h := mixHash h (mixHash (hash entry.toString) contentHash)
  return h

/-- Content hash of a single file; `0` when it is absent or unreadable.
Used so that editing the startup stub invalidates every stamp.  The
file's *path* is deliberately not mixed in: relocating the checkout or
pointing `--start-dir` at an identical copy of the stub must not force a
recompile, while changing a single instruction in it must. -/
private def fileContentHash (path : System.FilePath) : IO UInt64 := do
  if !(← path.pathExists) then
    return 0
  try
    pure (hash (← IO.FS.readFile path))
  catch _ =>
    pure 0

/-- Stamp recorded after a passing run: generated-C hash plus a
toolchain hash covering the ccomp version, **the `ccomp` binary's digest
and the full text of its `compcert.ini`** (see `compcertIdentity` — the
version string alone does not name the target architecture), the include
configuration (the Lean include path is versioned, so toolchain bumps
change it), the contents of non-toolchain header directories, the link
mode, the assembler/linker versions, and the startup stub's contents.

The consequence worth knowing: a `[cached]` result now means *this
machine, with this CompCert install, already compiled and ran exactly
this generated C and it agreed*.  Change the compiler, its target, the
stub, the headers, or the program, and the stamp is discarded.  That
makes `--force` a deliberate re-verification rather than a routine
necessity — though it is still what you want when producing evidence,
because a stamp records that a run happened, not that you watched it. -/
def stampFor (source toolchain : String) : String :=
  s!"{hash source} {hash toolchain} pass"

/-- The two halves of a stamp, so a reader can be told *which* one moved.

`check-native` only needs "the stamp differs"; the ledger has to say whether
the program changed or the compiler did, because those are different pieces of
news.  Fail-closed: a stamp that does not have this shape is `none` and the row
reads stale. -/
def stampParts (stamp : String) : Option (String × String) :=
  match (stamp.trimAscii.toString.splitOn " ").filter (· != "") with
  | [source, toolchain, "pass"] => some (source, toolchain)
  | _ => none

/-- Everything the freestanding path needs that is resolved once, before
the certificate loop: the assembled startup stub. -/
structure LinkSetup where
  mode : LinkMode
  /-- Assembled `runtime/start/<arch>.S`; `none` in hosted mode. -/
  startObject : Option System.FilePath := none

/-- **Everything the stamp is keyed on, resolved once.**

`run` and the ledger both go through this, so the key the ledger compares a
stamp against is the key the runner wrote — by construction, rather than by two
copies of the same expression staying in step.  A ledger that computed the
toolchain key its own way would eventually disagree with the runner and would
then report every row stale, or worse, none of them. -/
structure Environment where
  opts : Options
  /-- `-I` flags, in the order `ccomp` receives them. -/
  includes : List String
  setup : LinkSetup
  /-- `ccomp -version`, verbatim. -/
  version : String
  /-- The `compcertIdentity` block: the `ccomp` binary's digest and the full
  text of its `compcert.ini`. -/
  compcertId : String
  /-- The `machineIdentity` line. -/
  machineId : String
  /-- Freestanding or hosted, plus stub, assembler and linker identities. -/
  linkDescription : String
  /-- Content hash of the caller-supplied header directories. -/
  headerHash : UInt64
  /-- The exact text `stampFor` is keyed on. -/
  toolchain : String
  /-- Where digests are computed. -/
  scratch : System.FilePath

/-- Where the run record for `name` lives. -/
def runRecordPath (opts : Options) (name : String) : System.FilePath :=
  opts.dir / s!"{name}.run"

/-- Where the receipt for `name` lives, under the default layout. -/
def defaultReceiptDir (opts : Options) : System.FilePath :=
  opts.receiptDir.getD (opts.dir / "receipts")

/-- Signal names for the exit statuses a killed artifact can produce.
`128 + N` is what the shell and Lean's `IO.Process.output` report for a
process that died on signal `N`. -/
private def signalDescription : UInt32 → Option String
  | 129 => some "SIGHUP"
  | 130 => some "SIGINT"
  | 131 => some "SIGQUIT"
  | 132 => some "SIGILL"
  | 133 => some "SIGTRAP"
  | 134 => some "SIGABRT"
  | 135 => some "SIGBUS"
  | 136 => some "SIGFPE"
  | 137 => some "SIGKILL (typically the out-of-memory killer)"
  | 139 => some "SIGSEGV"
  | 143 => some "SIGTERM"
  | code =>
      if 128 < code && code ≤ 255 then
        some s!"signal {code - 128}"
      else
        none

/-- Classification of an artifact's exit status.  Exactly one status —
`1` — means "the computed value differs from the certified constant".
Everything else nonzero is an abnormal termination, which says nothing
about the computed value and must never be reported as a disagreement. -/
private inductive RunVerdict where
  | agrees
  | disagrees
  | abnormal (detail : String)

private def classify (code : UInt32) : RunVerdict :=
  if code == 0 then .agrees
  else if code == 1 then .disagrees
  else match signalDescription code with
    | some name => .abnormal s!"killed by {name} (exit {code})"
    | none => .abnormal s!"unexpected exit status {code}"

private structure Outcome where
  passed : Bool
  cached : Bool

/-! ## Attestation

Everything the receipt writer needs, resolved once before the certificate
loop.  Assembling it can fail (no key, no `openssl`); when it does, the
whole run fails rather than quietly checking without attesting. -/

private structure AttestContext where
  key : System.FilePath
  publicKey : String
  scratch : System.FilePath
  receiptDir : System.FilePath
  campaign : String
  paramsHash : String
  toolchain : Attest.ToolchainId
  machine : String
  /-- `some` when the caller pinned a nonce; otherwise one is drawn per run. -/
  nonce : Option String

private def receiptPath (ctx : AttestContext) (name : String) :
    System.FilePath :=
  ctx.receiptDir / s!"{name}.receipt"

/-- Is the receipt already on disk still the right one for this C text?

Requires that it parses, that its verdict is `agrees`, that its
`programHash` is the digest of the C about to be compiled, and — when the
caller pinned a nonce — that it quotes that nonce.  Anything else means
the artifact re-runs and is re-signed, which is the fail-closed
direction. -/
private def receiptStillCurrent (ctx : AttestContext) (name source : String) :
    IO Bool := do
  let path := receiptPath ctx name
  if !(← path.pathExists) then return false
  let text ← try IO.FS.readFile path catch _ => pure ""
  match Attest.Tool.parseReceipt text with
  | .error _ => return false
  | .ok receipt =>
      if receipt.verdict != Attest.RunVerdict.agrees then return false
      if let some nonce := ctx.nonce then
        if receipt.nonce != nonce then return false
      match ← Attest.Tool.sha256Hex ctx.scratch source with
      | .error _ => return false
      | .ok digest => return receipt.programHash == digest

/-- Write a signed receipt for a run that has just agreed. -/
private def writeReceipt (ctx : AttestContext) (cert : Cert) (source : String)
    (value : Int) : IO (Except String System.FilePath) := do
  let programHash ←
    match ← Attest.Tool.sha256Hex ctx.scratch source with
    | .error message => return .error s!"digesting the emitted C failed: {message}"
    | .ok digest => pure digest
  let nonce ←
    match ctx.nonce with
    | some nonce => pure nonce
    | none =>
        match ← Attest.Tool.freshNonce with
        | .error message => return .error s!"drawing a nonce failed: {message}"
        | .ok nonce => pure nonce
  let recordedAt ← Attest.Tool.utcNow
  let unsigned : Attest.RunReceipt := {
    schema := Attest.schemaVersion
    attestation := .localSignature
    routeLabel := cert.routeLabel
    campaign := ctx.campaign
    digestName := "sha256"
    programHash
    paramsHash := ctx.paramsHash
    toolchain := ctx.toolchain
    value
    verdict := .agrees
    machine := ctx.machine
    nonce
    recordedAt
    publicKey := ctx.publicKey
    signature := ""
  }
  match ← Attest.Tool.signPayload ctx.key ctx.scratch unsigned.payload with
  | .error message => return .error s!"signing failed: {message}"
  | .ok signature =>
      let receipt := { unsigned with signature }
      IO.FS.createDirAll ctx.receiptDir
      let path := receiptPath ctx cert.name
      IO.FS.writeFile path (Attest.Tool.renderReceipt receipt)
      return .ok path

/-- **Record what happened, whatever happened.**

Written on *every* attempt, not only on a passing one, and that is the whole
point.  The stamp is a cache key: it exists only when the run agreed, so a
build tree where nothing has a stamp is indistinguishable from one where every
artifact was killed by the out-of-memory killer.  The record distinguishes
them, and it names the compiler, the machine and the exact C digest, so a
reader can tell whether the evidence is about the program in front of them.

Best-effort by design: a digest this cannot compute is written `-`, which the
ledger reads as "cannot be compared", i.e. stale.  Failing to write a record
never fails a check that otherwise passed — the record is bookkeeping, and
bookkeeping that can break a build gets deleted. -/
private def writeRunRecord (env : Environment) (cert : Cert)
    (source : Option String) (outcome : Attest.RunOutcome) (exitCode : Nat)
    (receiptPath : String) : IO Unit := do
  try
    let recordedAt ← Attest.Tool.utcNow
    let digestOf (text : String) : IO String := do
      match ← Attest.Tool.sha256Hex env.scratch text with
      | .error _ => pure "-"
      | .ok digest => pure digest
    let sourceDigest ←
      match source with
      | none => pure "-"
      | some text => digestOf text
    let ccompDigest ← digestOf env.compcertId
    let record : Attest.RunRecord := {
      schema := Attest.runRecordSchema
      name := cert.name
      recordedAt
      sourceDigest
      sourceBytes := (source.getD "").utf8ByteSize
      ccompVersion := firstLine env.version
      ccompDigest
      linkDescription := firstLine env.linkDescription
      machine := firstLine env.machineId
      exitCode
      outcome
      certifiedValue :=
        match cert.certifiedValue with
        | some value => toString value
        | none => "unstated"
      receiptPath := if receiptPath.isEmpty then "-" else receiptPath }
    IO.FS.createDirAll env.opts.dir
    IO.FS.writeFile (runRecordPath env.opts cert.name) record.render
  catch _ =>
    pure ()

private def runOne (env : Environment) (attest : Option AttestContext)
    (cert : Cert) : IO Outcome := do
  let opts := env.opts
  let includes := env.includes
  let setup := env.setup
  let toolchain := env.toolchain
  match cert.emitted with
  | .error errors =>
      IO.eprintln s!"[FAIL] {cert.name}: C emission failed"
      for error in errors do
        IO.eprintln s!"       {error}"
      writeRunRecord env cert none .emitFailed 0 ""
      return ⟨false, false⟩
  | .ok source =>
      let stamp := stampFor source toolchain
      let stampPath := opts.dir / s!"{cert.name}.stamp"
      if attest.isSome && cert.certifiedValue.isNone then
        IO.eprintln
          s!"[FAIL] {cert.name}: --attest requires the certificate to declare"
        IO.eprintln
          "       `certifiedValue`; a receipt that does not name the value would"
        IO.eprintln
          "       bind a signature to a program and a machine but not to an answer."
        return ⟨false, false⟩
      unless opts.force do
        if (← stampPath.pathExists) then
          if (← IO.FS.readFile stampPath).trimAscii.toString == stamp then
            let receiptCurrent ←
              match attest with
              | none => pure true
              | some ctx => receiptStillCurrent ctx cert.name source
            if receiptCurrent then
              IO.println s!"[cached] {cert.name}: C unchanged since last passing run"
              return ⟨true, true⟩
            IO.println
              s!"[re-run] {cert.name}: stamp current but no matching receipt"
      let cSource := opts.dir / s!"{cert.name}.c"
      let exe := opts.dir / cert.name
      IO.FS.writeFile cSource source
      match setup.mode, setup.startObject with
      | .freestanding, some startObject =>
          let objectPath := opts.dir / s!"{cert.name}.o"
          let compileArgs :=
            includes.toArray ++ #["-c", "-o", objectPath.toString, cSource.toString]
          let compiled ← IO.Process.output { cmd := "ccomp", args := compileArgs }
          if compiled.exitCode != 0 then
            IO.eprintln s!"[FAIL] {cert.name}: ccomp rejected the generated C"
            IO.eprintln compiled.stderr
            writeRunRecord env cert (some source) .compileFailed
              compiled.exitCode.toNat ""
            return ⟨false, false⟩
          let linked ← IO.Process.output {
            cmd := "ld"
            args := #["-o", exe.toString, startObject.toString, objectPath.toString]
          }
          if linked.exitCode != 0 then
            IO.eprintln s!"[FAIL] {cert.name}: freestanding link failed"
            IO.eprintln linked.stderr
            writeRunRecord env cert (some source) .linkFailed
              linked.exitCode.toNat ""
            return ⟨false, false⟩
      | _, _ =>
          let compileArgs := includes.toArray ++ #["-o", exe.toString, cSource.toString]
          let compiled ← IO.Process.output { cmd := "ccomp", args := compileArgs }
          if compiled.exitCode != 0 then
            IO.eprintln s!"[FAIL] {cert.name}: ccomp rejected the generated C"
            IO.eprintln compiled.stderr
            writeRunRecord env cert (some source) .compileFailed
              compiled.exitCode.toNat ""
            return ⟨false, false⟩
      let run ← IO.Process.output { cmd := exe.toString }
      match classify run.exitCode with
      | .disagrees =>
          IO.eprintln
            s!"[FAIL] {cert.name}: native run DISAGREES with the certified value (exit 1)"
          writeRunRecord env cert (some source) .disagrees run.exitCode.toNat ""
          return ⟨false, false⟩
      | .abnormal detail =>
          IO.eprintln s!"[FAIL] {cert.name}: ABNORMAL TERMINATION — not a disagreement"
          IO.eprintln s!"       {detail}"
          IO.eprintln
            "       The artifact did not report a value comparison at all; this run"
          IO.eprintln
            "       is evidence of nothing about the certified constant."
          writeRunRecord env cert (some source) .abnormal run.exitCode.toNat ""
          return ⟨false, false⟩
      | .agrees =>
          match attest, cert.certifiedValue with
          | some ctx, some value =>
              match ← writeReceipt ctx cert source value with
              | .error message =>
                  IO.eprintln s!"[FAIL] {cert.name}: the run agreed but no receipt was written"
                  IO.eprintln s!"       {message}"
                  writeRunRecord env cert (some source) .agrees
                    run.exitCode.toNat ""
                  return ⟨false, false⟩
              | .ok path =>
                  IO.FS.writeFile stampPath (stamp ++ "\n")
                  writeRunRecord env cert (some source) .agrees
                    run.exitCode.toNat path.toString
                  IO.println
                    s!"[run] {cert.name}: compiled with CompCert ({setup.mode.describe}), native check passed; receipt {path}"
                  return ⟨true, false⟩
          | _, _ =>
              IO.FS.writeFile stampPath (stamp ++ "\n")
              writeRunRecord env cert (some source) .agrees run.exitCode.toNat ""
              IO.println
                s!"[run] {cert.name}: compiled with CompCert ({setup.mode.describe}), native check passed"
              return ⟨true, false⟩

/-- Locate `<arch>.S`.  Explicit `--start-dir` wins, then
`$LEAN_COMPCERT_START_DIR`, then a few directories relative to the
working directory so that in-repo runs and the `examples/consumer`
sub-project both work without configuration. -/
private def findStub (opts : Options) (arch : String) :
    IO (Option System.FilePath) := do
  let mut candidates : List System.FilePath := []
  if let some dir := opts.startDir then
    candidates := [dir]
  else
    if let some dir ← IO.getEnv "LEAN_COMPCERT_START_DIR" then
      candidates := [System.FilePath.mk dir]
    candidates := candidates ++ (
      ["runtime/start", "../runtime/start", "../../runtime/start",
       "../../../runtime/start"].map System.FilePath.mk)
  for dir in candidates do
    let stub := dir / s!"{arch}.S"
    if ← stub.pathExists then
      return some stub
  return none

/-- Assemble `runtime/start/<arch>.S` once for the whole run. -/
private def prepareFreestanding (opts : Options) :
    IO (Except String (System.FilePath × String)) := do
  let some arch ← hostArch
    | return .error
        "could not determine the host architecture from `uname -m`; \
         re-run with --hosted"
  let some stub ← findStub opts arch
    | return .error
        s!"startup stub {arch}.S not found; pass --start-dir DIR (or set \
           LEAN_COMPCERT_START_DIR) to the directory holding \
           runtime/start/{arch}.S, or re-run with --hosted"
  let startObject := opts.dir / "start.o"
  let assembled ← IO.Process.output {
    cmd := "as"
    args := #["-o", startObject.toString, stub.toString]
  }
  if assembled.exitCode != 0 then
    return .error s!"assembling {stub} failed:\n{assembled.stderr}"
  let stubHash ← fileContentHash stub
  let asVersion := (← toolVersion "as" #["--version"]).map firstLine |>.getD "as?"
  let ldVersion := (← toolVersion "ld" #["--version"]).map firstLine |>.getD "ld?"
  return .ok (startObject, s!"{arch} {stubHash} {asVersion} {ldVersion}")

/-- Resolve everything the receipt writer needs, once.

The toolchain identity written into a receipt is the same material the
stamp is keyed on: the `ccomp` version line, a digest of the *whole*
`compcertIdentity` block (the `ccomp` binary's own digest plus the full
text of its `compcert.ini`), and the link description.  Digesting that
block keeps the receipt field a fixed 64 hex characters while still
changing whenever the compiler, its target, or the link does.

Every field is reduced to a single line, because the signed payload is
newline-separated. -/
private def prepareAttest (opts : Options) (version compcertId machineId
    linkDescription : String) : IO (Except String AttestContext) := do
  let key := opts.keyPath.getD Attest.Tool.defaultKeyPath
  if !(← key.pathExists) then
    return .error
      s!"no signing key at {key}; run `attest-keygen` first (or pass --key PATH)"
  let scratch := opts.dir / "attest-scratch"
  let publicKey ←
    match ← Attest.Tool.publicKeyHex key scratch with
    | .error message => return .error message
    | .ok hex => pure hex
  let params ←
    match opts.paramsFile with
    | none => pure ""
    | some path =>
        if ← path.pathExists then IO.FS.readFile path
        else return .error s!"params file {path} does not exist"
  let paramsHash ←
    match ← Attest.Tool.sha256Hex scratch params with
    | .error message => return .error message
    | .ok digest => pure digest
  let binaryDigest ←
    match ← Attest.Tool.sha256Hex scratch compcertId with
    | .error message => return .error message
    | .ok digest => pure digest
  if let some nonce := opts.nonce then
    if !Attest.isDigest256 nonce then
      return .error "--nonce must be 64 lowercase hex characters"
  return .ok {
    key
    publicKey
    scratch
    receiptDir := defaultReceiptDir opts
    campaign := opts.campaign.getD "leancompcert-native-check"
    paramsHash
    toolchain := {
      ccompVersion := firstLine version
      binaryDigest
      linkDescription := firstLine linkDescription }
    machine := firstLine machineId
    nonce := opts.nonce }

/-- **Resolve the environment the stamp is keyed on.**

Pulled out of `run` so the ledger can ask the same question and get, by
construction, the same answer.  Everything with a side effect happens here
exactly as it did inline: the cache directory is created, and in freestanding
mode `runtime/start/<arch>.S` is assembled once.

Fails rather than guessing.  No `ccomp` on `PATH` is an error, not an empty
toolchain string — a ledger that silently keyed stamps on `""` would report
every row current on a machine with no compiler. -/
def resolveEnvironment (opts : Options) : IO (Except String Environment) := do
  let some version ← ccompVersion
    | return .error
        "ccomp not found on PATH (CompCert is required for check-native)"
  IO.FS.createDirAll opts.dir
  -- The emitted certificates include only <stdint.h> and <stddef.h>, so
  -- no `-I` flag is required; `--include` remains available for callers
  -- who feed this runner their own C.
  let includes := opts.extraIncludes.map (s!"-I{·}")
  let headerDirs : List System.FilePath :=
    opts.extraIncludes.map System.FilePath.mk
  let mut headerHash : UInt64 := 0
  for dir in headerDirs do
    headerHash := mixHash headerHash (← dirContentHash dir)
  let mut setup : LinkSetup := { mode := opts.linkMode }
  let mut linkDescription := opts.linkMode.describe
  if opts.linkMode == .freestanding then
    match ← prepareFreestanding opts with
    | .error message => return .error message
    | .ok (startObject, stubDescription) =>
        setup := { mode := .freestanding, startObject := some startObject }
        linkDescription := s!"freestanding {stubDescription}"
  let compcertId ← compcertIdentity
  let machineId ← machineIdentity
  let toolchain :=
    version ++ "\n" ++ compcertId ++ "\n" ++ machineId ++ "\n"
      ++ String.intercalate " " includes
      ++ s!"\n{headerHash}\n{linkDescription}"
  return .ok {
    opts, includes, setup, version, compcertId, machineId, linkDescription,
    headerHash, toolchain
    scratch := opts.dir / "digest-scratch" }

def run (certs : List Cert) (args : List String) : IO UInt32 := do
  let opts ←
    match parseOptions args with
    | .error message =>
        IO.eprintln s!"error: {message}"
        return 2
    | .ok opts => pure opts
  let env ←
    match ← resolveEnvironment opts with
    | .error message =>
        IO.eprintln s!"error: {message}"
        return 2
    | .ok env => pure env
  let mut attest : Option AttestContext := none
  if opts.attest then
    match ← prepareAttest opts env.version env.compcertId env.machineId
        env.linkDescription with
    | .error message =>
        IO.eprintln s!"error: {message}"
        return 2
    | .ok ctx =>
        attest := some ctx
        IO.println
          s!"attesting with the local key {ctx.key} (public {ctx.publicKey.take 16}…)"
        IO.println
          "  a locally signed receipt is TAMPER-EVIDENT, not attested: the key sits"
        IO.println
          "  on the machine that ran the binary.  See LeanCompCert/Trusted/LocalReceipt.lean."
  let mut passed := 0
  let mut cached := 0
  let mut failed := 0
  for cert in certs do
    let outcome ← runOne env attest cert
    if outcome.passed then
      passed := passed + 1
      if outcome.cached then
        cached := cached + 1
    else
      failed := failed + 1
  if failed == 0 then
    IO.println
      s!"native check: {passed} certificates agree with their certified values ({cached} cached, {passed - cached} run, {opts.linkMode.describe} link)"
    return 0
  IO.eprintln s!"native check: {failed} FAILED, {passed} passed"
  return 1

end LeanCompCert.NativeCheck
