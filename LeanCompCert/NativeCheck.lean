/-!
# Cached native cross-check runner

`lean-compcert check-native` gives the `native_decide`-style workflow —
run the computation as fast native code — without ever admitting the
run's outcome as a theorem.  Each registered certificate's generated C
(whose `main` returns 0 exactly when the computed value equals the
certified constant) is compiled with CompCert and executed, and the
result is cached by *content hash*: a certificate is re-compiled and
re-run only when its generated C (or the ccomp version) actually
changes.

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

structure Options where
  dir : System.FilePath := ".lake" / "build" / "native-check"
  force : Bool := false
  extraIncludes : List String := []

private def parseOptions : List String → Except String Options
  | [] => .ok {}
  | "--force" :: rest => do
      let opts ← parseOptions rest
      .ok { opts with force := true }
  | "--dir" :: dir :: rest => do
      let opts ← parseOptions rest
      .ok { opts with dir := dir }
  | "--include" :: dir :: rest => do
      let opts ← parseOptions rest
      .ok { opts with extraIncludes := dir :: opts.extraIncludes }
  | arg :: _ => .error s!"unknown check-native argument '{arg}'"

private def ccompVersion : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "ccomp", args := #["-version"] }
    if out.exitCode == 0 then
      return some out.stdout.trimAscii.toString
    return none
  catch _ =>
    return none

private def leanIncludeDir : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
    if out.exitCode == 0 then
      return some (out.stdout.trimAscii.toString ++ "/include")
    return none
  catch _ =>
    return none

/-- Content hash of every regular file under `dir` (path and text),
order-independent of directory enumeration. Unreadable files fall back
to their size. Used so that edits to header directories (e.g. the
CompCert runtime shim) invalidate stamps. -/
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

/-- Stamp recorded after a passing run: generated-C hash plus a
toolchain hash covering the ccomp version, the include configuration
(the Lean include path is versioned, so toolchain bumps change it), and
the contents of non-toolchain header directories. -/
private def stampFor (source toolchain : String) : String :=
  s!"{hash source} {hash toolchain} pass"

private structure Outcome where
  passed : Bool
  cached : Bool

private def runOne (opts : Options) (includes : List String)
    (toolchain : String) (cert : Cert) : IO Outcome := do
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
      let compileArgs := includes.toArray ++ #["-o", exe.toString, cSource.toString]
      let compiled ← IO.Process.output { cmd := "ccomp", args := compileArgs }
      if compiled.exitCode != 0 then
        IO.eprintln s!"[FAIL] {cert.name}: ccomp rejected the generated C"
        IO.eprintln compiled.stderr
        return ⟨false, false⟩
      let run ← IO.Process.output { cmd := exe.toString }
      if run.exitCode != 0 then
        IO.eprintln
          s!"[FAIL] {cert.name}: native run disagrees with the certified value (exit {run.exitCode})"
        return ⟨false, false⟩
      IO.FS.writeFile stampPath (stamp ++ "\n")
      IO.println s!"[run] {cert.name}: compiled with CompCert, native check passed"
      return ⟨true, false⟩

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
  let mut includes := opts.extraIncludes.map (s!"-I{·}")
  let mut headerDirs : List System.FilePath :=
    opts.extraIncludes.map System.FilePath.mk
  if (← (System.FilePath.mk "runtime/include").pathExists) then
    includes := includes ++ ["-Iruntime/include"]
    headerDirs := headerDirs ++ [System.FilePath.mk "runtime/include"]
  if let some leanInclude ← leanIncludeDir then
    includes := includes ++ [s!"-I{leanInclude}"]
  let mut headerHash : UInt64 := 0
  for dir in headerDirs do
    headerHash := mixHash headerHash (← dirContentHash dir)
  let toolchain :=
    version ++ "\n" ++ String.intercalate " " includes ++ s!"\n{headerHash}"
  let mut passed := 0
  let mut cached := 0
  let mut failed := 0
  for cert in certs do
    let outcome ← runOne opts includes toolchain cert
    if outcome.passed then
      passed := passed + 1
      if outcome.cached then
        cached := cached + 1
    else
      failed := failed + 1
  if failed == 0 then
    IO.println
      s!"native check: {passed} certificates agree with their certified values ({cached} cached, {passed - cached} run)"
    return 0
  IO.eprintln s!"native check: {failed} FAILED, {passed} passed"
  return 1

end LeanCompCert.NativeCheck
