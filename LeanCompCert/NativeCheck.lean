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
-/

namespace LeanCompCert.NativeCheck

structure Cert where
  name : String
  emitted : Except (Array String) String

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

private def parseOptions : List String → Except String Options
  | [] => .ok {}
  | "--force" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with force := true }
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
private def stampFor (source toolchain : String) : String :=
  s!"{hash source} {hash toolchain} pass"

/-- Everything the freestanding path needs that is resolved once, before
the certificate loop: the assembled startup stub. -/
private structure LinkSetup where
  mode : LinkMode
  /-- Assembled `runtime/start/<arch>.S`; `none` in hosted mode. -/
  startObject : Option System.FilePath := none

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

private def runOne (opts : Options) (includes : List String)
    (setup : LinkSetup) (toolchain : String) (cert : Cert) : IO Outcome := do
  match cert.emitted with
  | .error errors =>
      IO.eprintln s!"[FAIL] {cert.name}: C emission failed"
      for error in errors do
        IO.eprintln s!"       {error}"
      return ⟨false, false⟩
  | .ok source =>
      let stamp := stampFor source toolchain
      let stampPath := opts.dir / s!"{cert.name}.stamp"
      unless opts.force do
        if (← stampPath.pathExists) then
          if (← IO.FS.readFile stampPath).trimAscii.toString == stamp then
            IO.println s!"[cached] {cert.name}: C unchanged since last passing run"
            return ⟨true, true⟩
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
            return ⟨false, false⟩
          let linked ← IO.Process.output {
            cmd := "ld"
            args := #["-o", exe.toString, startObject.toString, objectPath.toString]
          }
          if linked.exitCode != 0 then
            IO.eprintln s!"[FAIL] {cert.name}: freestanding link failed"
            IO.eprintln linked.stderr
            return ⟨false, false⟩
      | _, _ =>
          let compileArgs := includes.toArray ++ #["-o", exe.toString, cSource.toString]
          let compiled ← IO.Process.output { cmd := "ccomp", args := compileArgs }
          if compiled.exitCode != 0 then
            IO.eprintln s!"[FAIL] {cert.name}: ccomp rejected the generated C"
            IO.eprintln compiled.stderr
            return ⟨false, false⟩
      let run ← IO.Process.output { cmd := exe.toString }
      match classify run.exitCode with
      | .disagrees =>
          IO.eprintln
            s!"[FAIL] {cert.name}: native run DISAGREES with the certified value (exit 1)"
          return ⟨false, false⟩
      | .abnormal detail =>
          IO.eprintln s!"[FAIL] {cert.name}: ABNORMAL TERMINATION — not a disagreement"
          IO.eprintln s!"       {detail}"
          IO.eprintln
            "       The artifact did not report a value comparison at all; this run"
          IO.eprintln
            "       is evidence of nothing about the certified constant."
          return ⟨false, false⟩
      | .agrees =>
          IO.FS.writeFile stampPath (stamp ++ "\n")
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

def run (certs : List Cert) (args : List String) : IO UInt32 := do
  let opts ←
    match parseOptions args with
    | .error message =>
        IO.eprintln s!"error: {message}"
        return 2
    | .ok opts => pure opts
  let some version ← ccompVersion
    | IO.eprintln "error: ccomp not found on PATH (CompCert is required for check-native)"
      return 2
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
    | .error message =>
        IO.eprintln s!"error: {message}"
        return 2
    | .ok (startObject, stubDescription) =>
        setup := { mode := .freestanding, startObject := some startObject }
        linkDescription := s!"freestanding {stubDescription}"
  let compcertId ← compcertIdentity
  let machineId ← machineIdentity
  let toolchain :=
    version ++ "\n" ++ compcertId ++ "\n" ++ machineId ++ "\n"
      ++ String.intercalate " " includes
      ++ s!"\n{headerHash}\n{linkDescription}"
  let mut passed := 0
  let mut cached := 0
  let mut failed := 0
  for cert in certs do
    let outcome ← runOne opts includes setup toolchain cert
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
