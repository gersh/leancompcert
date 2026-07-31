import LeanCompCert.Trusted.Evidence

/-!
# Resolution: where evidence comes from, decided outside Lean

The Lean source states the **obligation**; a configuration file states **how it
is resolved**.  Nothing in a `.lean` file selects `cache` versus `run` versus
`attest`, and nothing in a configuration file can assert a result — the config
says where to *get* evidence, and `RunEvidence.verify` still checks that what
arrived is well formed and answers the claim.

The property this buys, and the reason the policy lives outside Lean:

> **Changing the resolution policy does not change the proof term.**

A use site elaborates to `<decl>._evidenced.run.ax p n <decl>._evidenced.run.evidence h`
whatever the policy was.  Only the *definition* of the evidence constant
differs between a developer iterating on the cache and a release build
consuming attestations.  So nobody edits Lean source to switch regimes, and the
regime actually used is recorded in the evidence record and in the ledger
rather than inferred.

## The configuration file

Plain `key = value` lines; `#` starts a comment.  Two files are read, in this
order, the second overriding keys of the first:

* `leancompcert-evidence.cfg` — the project policy, checked in;
* `leancompcert-evidence.local.cfg` — the developer's override, not checked in.

Discovery walks up from the current directory.  `$LEAN_COMPCERT_EVIDENCE_CONFIG`
names a file directly and skips the walk.

```
# leancompcert-evidence.cfg  — project policy
policy       = attest, cache      # prefer an attestation; fall back to a stamp
evidence-dir = evidence
ledger       = evidence/ledger.log
producer     = ./scripts/produce-evidence.sh
require-live-machine = true
```

```
# leancompcert-evidence.local.cfg  — developer override
policy = cache, run               # a stamp if one exists, otherwise run it
```

`policy` is an ordered preference list; the first mode with usable evidence
wins.  There is **no default**: with no configuration file the tactic fails
rather than silently picking the weakest option.

The project default is `attest, cache` — *use attestation if available*.  The
local default is `cache, run` — *use the stamp if a previous run exists,
otherwise run it*.  Note the ordering: `cache` precedes `run` so that a routine
build stays a stamp check.  `run` first is a deliberate choice for when you
want the computation actually performed.

## Where evidence files live

`<evidence-dir>/<key>.<mode>.evidence`, one record per shard per mode, in the
same `key = value` format.  They are produced **out of band** by
`scripts/produce-evidence.sh`, never by the build: the computation happens
once, and every later build reads a record.
-/

namespace LeanCompCert.Trusted

open System (FilePath)

/-! ## Failure modes, kept distinguishable

Three of these are different in kind and a caller must be able to tell them
apart: *no evidence available* and *evidence present but stale* are recoverable
by producing evidence again; *evidence present but invalid* is a real
problem — a record that does not answer the claim it was filed under. -/
inductive ResolveFailure where
  /-- No configuration file was found.  Fail closed. -/
  | noConfig (searched : List String)
  /-- The configuration is unreadable or names an unknown mode. -/
  | badConfig (path : String) (reason : String)
  /-- Every mode in the policy was tried and none had a record.  Recoverable:
  produce evidence. -/
  | noEvidence (key : String) (policy : List RunMode) (looked : List String)
  /-- A record exists but does not describe this machine (or this toolchain,
  when the live check is on).  Recoverable: re-run here. -/
  | stale (key : String) (mode : RunMode) (reason : String)
  /-- A record exists, is current, and does not answer the claim.  Not
  recoverable by re-running; something is wrong. -/
  | invalid (key : String) (mode : RunMode) (reason : String)
  deriving Repr

def RunMode.name : RunMode → String
  | .cache => "cache"
  | .run => "run"
  | .attest => "attest"

def RunMode.ofName? : String → Option RunMode
  | "cache" => some .cache
  | "run" => some .run
  | "attest" => some .attest
  | _ => none

def RunVerdict.name : RunVerdict → String
  | .agrees => "agrees"
  | .disagrees => "disagrees"
  | .abnormal => "abnormal"

def RunVerdict.ofName? : String → Option RunVerdict
  | "agrees" => some .agrees
  | "disagrees" => some .disagrees
  | "abnormal" => some .abnormal
  | _ => none

def ResolveFailure.message : ResolveFailure → String
  | .noConfig searched =>
      "evidenced_decide: NO EVIDENCE CONFIGURATION.\n" ++
      "  Resolution policy is deliberately not a Lean-source decision, and there is\n" ++
      "  no default: a missing configuration fails closed rather than silently\n" ++
      "  selecting the weakest option.\n" ++
      "  Looked for leancompcert-evidence.cfg in:\n" ++
      String.intercalate "\n" (searched.map (fun s => "    " ++ s))
  | .badConfig path reason =>
      s!"evidenced_decide: unusable configuration {path}: {reason}"
  | .noEvidence key policy looked =>
      s!"evidenced_decide: NO EVIDENCE AVAILABLE for '{key}'.\n" ++
      s!"  Policy was: {String.intercalate ", " (policy.map RunMode.name)}\n" ++
      "  Looked for:\n" ++
      String.intercalate "\n" (looked.map (fun s => "    " ++ s)) ++
      "\n  This is recoverable: produce evidence with\n" ++
      s!"    scripts/produce-evidence.sh {key} --mode run"
  | .stale key mode reason =>
      s!"evidenced_decide: EVIDENCE PRESENT BUT STALE for '{key}' ({mode.name}).\n" ++
      s!"  {reason}\n" ++
      "  A record of a run elsewhere is not a run here.  This is recoverable:\n" ++
      s!"    scripts/produce-evidence.sh {key} --mode run"
  | .invalid key mode reason =>
      s!"evidenced_decide: EVIDENCE PRESENT BUT INVALID for '{key}' ({mode.name}).\n" ++
      s!"  {reason}\n" ++
      "  Re-running will NOT fix this: the record does not answer the claim it was\n" ++
      "  filed under.  Either the claim changed or the record is for something else."

/-! ## Configuration -/

structure EvidenceConfig where
  /-- Ordered preference over resolution modes. -/
  policy : List RunMode
  evidenceDir : FilePath
  ledger : FilePath
  /-- Command invoked for `run` when no record exists.  `none` disables it. -/
  producer : Option String
  /-- Compare the record's machine identity against this machine.  On by
  default: a stamp copied from another host is the realistic accident. -/
  requireLiveMachine : Bool
  /-- Which files the configuration was read from, for messages. -/
  sources : List String

private def trim (s : String) : String := s.trimAscii.toString

private def stripComment (s : String) : String :=
  match s.splitOn "#" with
  | [] => ""
  | head :: _ => head

/-- `key = value` lines, comments stripped, later keys winning. -/
private def parseKeyValues (text : String) : List (String × String) :=
  let lines := (text.splitOn "\n").map stripComment
  lines.foldr (init := []) fun line acc =>
    match line.splitOn "=" with
    | key :: rest =>
        if rest.isEmpty then acc
        else (trim key, trim (String.intercalate "=" rest)) :: acc
    | [] => acc

private def lookupKey (kvs : List (String × String)) (key : String) :
    Option String :=
  (kvs.filter (fun kv => kv.1 == key)).getLast?.map (·.2)

private def parsePolicy (s : String) : Except String (List RunMode) := do
  let parts := (s.splitOn ",").map trim |>.filter (fun p => !p.isEmpty)
  if parts.isEmpty then throw "empty policy list"
  parts.mapM fun p =>
    match RunMode.ofName? p with
    | some m => pure m
    | none => throw s!"unknown resolution mode '{p}' (expected cache, run or attest)"

private def configNames : List String :=
  ["leancompcert-evidence.cfg", "leancompcert-evidence.local.cfg"]

/-- Directories from the current one up to the filesystem root. -/
private def ancestors (dir : FilePath) : List FilePath :=
  let rec go (d : FilePath) (fuel : Nat) : List FilePath :=
    match fuel with
    | 0 => [d]
    | fuel + 1 =>
        match d.parent with
        | some parent => d :: go parent fuel
        | none => [d]
  go dir 64

/-- Find the directory holding `leancompcert-evidence.cfg`, walking up. -/
private def findConfigDir : IO (Option FilePath × List String) := do
  let cwd ← IO.currentDir
  let mut searched : List String := []
  for dir in ancestors cwd do
    let candidate := dir / "leancompcert-evidence.cfg"
    searched := searched ++ [candidate.toString]
    if ← candidate.pathExists then
      return (some dir, searched)
  return (none, searched)

/-- Read the project configuration and its optional local override.

Fails closed: no `leancompcert-evidence.cfg` anywhere up the tree is an
error, not a default. -/
def readConfig : IO (Except ResolveFailure EvidenceConfig) := do
  let mut baseDir : FilePath := "."
  let mut files : List FilePath := []
  match ← IO.getEnv "LEAN_COMPCERT_EVIDENCE_CONFIG" with
  | some path =>
      let p : FilePath := path
      unless ← p.pathExists do
        return .error (.noConfig [path])
      baseDir := p.parent.getD "."
      files := [p]
  | none =>
      let (dir?, searched) ← findConfigDir
      match dir? with
      | none => return .error (.noConfig searched)
      | some dir =>
          baseDir := dir
          files := [dir / "leancompcert-evidence.cfg"]
          let localPath := dir / "leancompcert-evidence.local.cfg"
          if ← localPath.pathExists then
            files := files ++ [localPath]
  let mut kvs : List (String × String) := []
  for file in files do
    kvs := kvs ++ parseKeyValues (← IO.FS.readFile file)
  let policyText := (lookupKey kvs "policy").getD ""
  let policy ←
    match parsePolicy policyText with
    | .ok p => pure p
    | .error reason =>
        return .error (.badConfig (files.getLast?.map (·.toString) |>.getD "?") reason)
  let evidenceDir : FilePath :=
    baseDir / ((lookupKey kvs "evidence-dir").getD "evidence")
  let ledger : FilePath :=
    baseDir / ((lookupKey kvs "ledger").getD "evidence/ledger.log")
  let producer := lookupKey kvs "producer"
  let requireLiveMachine :=
    match lookupKey kvs "require-live-machine" with
    | some "false" => false
    | _ => true
  return .ok {
    policy, evidenceDir, ledger, producer, requireLiveMachine
    sources := files.map (·.toString) }

/-! ## Machine identity, live

Same notion as `NativeCheck.machineIdentity`: `/etc/machine-id` when it is
readable, then dbus's copy, then hostname.  Deliberately a file read rather
than a subprocess, so that the staleness check costs microseconds and a build's
cost stays independent of what the artifact did. -/
def liveMachineIdentity : IO String := do
  for path in ["/etc/machine-id", "/var/lib/dbus/machine-id"] do
    try
      if ← (FilePath.mk path).pathExists then
        let text := (← IO.FS.readFile path).trimAscii.toString
        if !text.isEmpty then
          return "machine-id:" ++ text
    catch _ => pure ()
  try
    let out ← IO.Process.output { cmd := "uname", args := #["-n", "-m", "-s"] }
    if out.exitCode == 0 then
      return "hostname:" ++ out.stdout.trimAscii.toString
  catch _ => pure ()
  return "machine-unidentified"

/-! ## Evidence records on disk -/

/-- A record as read from disk: everything a `RunEvidence` needs except the
program, which comes from the goal so that it cannot be forged by the file. -/
structure ResolvedEvidence where
  mode : RunMode
  key : String
  expected : Nat
  shard : ShardId
  artifactDigest : String
  toolchain : String
  machine : String
  /-- Empty in `cache` mode. -/
  nonce : String
  echoedNonce : String
  observed : Nat
  verdict : RunVerdict
  recordedAt : String
  /-- TDX pieces; all empty outside `attest` mode. -/
  quoteDigest : String
  reportData : String
  pinnedKey : String
  path : String
  deriving Repr

private def required (kvs : List (String × String)) (key : String) :
    Except String String :=
  match lookupKey kvs key with
  | some v => .ok v
  | none => .error s!"missing field '{key}'"

private def optional (kvs : List (String × String)) (key : String) : String :=
  (lookupKey kvs key).getD ""

private def requiredNat (kvs : List (String × String)) (key : String) :
    Except String Nat := do
  let text ← required kvs key
  match text.toNat? with
  | some n => .ok n
  | none => .error s!"field '{key}' is not a natural number: '{text}'"

def parseEvidence (path : String) (text : String) :
    Except String ResolvedEvidence := do
  let kvs := parseKeyValues text
  let format ← required kvs "format"
  unless format == "lean-compcert-evidence/1" do
    throw s!"unknown record format '{format}'"
  let modeText ← required kvs "mode"
  let some mode := RunMode.ofName? modeText
    | throw s!"unknown mode '{modeText}'"
  let verdictText ← required kvs "verdict"
  let some verdict := RunVerdict.ofName? verdictText
    | throw s!"unknown verdict '{verdictText}'"
  let key ← required kvs "key"
  let expected ← requiredNat kvs "expected"
  let campaign ← required kvs "shard-campaign"
  let index ← requiredNat kvs "shard-index"
  let count ← requiredNat kvs "shard-count"
  let lo ← requiredNat kvs "shard-lo"
  let hi ← requiredNat kvs "shard-hi"
  let carryIn ← required kvs "shard-carry-in"
  let carryOut ← required kvs "shard-carry-out"
  let artifactDigest ← required kvs "artifact-digest"
  let toolchain ← required kvs "toolchain"
  let machine ← required kvs "machine"
  let observed ← requiredNat kvs "observed"
  let recordedAt ← required kvs "recorded-at"
  return {
    mode, key, expected
    shard := { campaign, index, count, lo, hi, carryIn, carryOut }
    artifactDigest, toolchain, machine
    nonce := optional kvs "nonce"
    echoedNonce := optional kvs "echoed-nonce"
    observed, verdict, recordedAt
    quoteDigest := optional kvs "quote-digest"
    reportData := optional kvs "report-data"
    pinnedKey := optional kvs "pinned-key"
    path }

/-- Read one record, if it exists. -/
private def loadRecord (cfg : EvidenceConfig) (key : String) (mode : RunMode) :
    IO (Option (Except String ResolvedEvidence)) := do
  let path := cfg.evidenceDir / s!"{key}.{mode.name}.evidence"
  if ← path.pathExists then
    return some (parseEvidence path.toString (← IO.FS.readFile path))
  return none

/-- Run the configured producer for `run` mode, with a fresh nonce. -/
private def randomNonce : IO String := do
  let bytes ← IO.FS.withFile "/dev/urandom" .read fun handle => handle.read 32
  let hexDigits : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7',
      '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let mut out := ""
  for i in [0 : bytes.size] do
    let n := (bytes.get! i).toNat
    out := (out.push hexDigits[n / 16]!).push hexDigits[n % 16]!
  return out

private def invokeProducer (cfg : EvidenceConfig) (key : String) :
    IO (Except String Unit) := do
  match cfg.producer with
  | none => return .error "no `producer` configured, so `run` cannot be satisfied"
  | some command =>
      let nonce ← randomNonce
      let out ← IO.Process.output {
        cmd := "sh"
        args := #["-c", s!"{command} {key} --mode run --nonce {nonce}"] }
      if out.exitCode == 0 then
        return .ok ()
      return .error s!"producer exited {out.exitCode}:\n{out.stderr}"

/-- Resolve evidence for `key` by walking the configured policy.

Returns the first mode that yields a record which is present, current and
parseable.  A record that is present but describes another machine is
**stale**, and resolution moves on to the next mode rather than accepting it;
if no mode succeeds the last stale reason is what the caller is told, because
that is the actionable one. -/
def resolve (cfg : EvidenceConfig) (key : String) :
    IO (Except ResolveFailure ResolvedEvidence) := do
  let liveMachine ← liveMachineIdentity
  let mut looked : List String := []
  let mut lastProblem : Option ResolveFailure := none
  for mode in cfg.policy do
    let path := cfg.evidenceDir / s!"{key}.{mode.name}.evidence"
    looked := looked ++ [path.toString]
    let mut record ← loadRecord cfg key mode
    if record.isNone && mode == RunMode.run then
      match ← invokeProducer cfg key with
      | .ok _ => record ← loadRecord cfg key mode
      | .error reason =>
          lastProblem := some (.noEvidence key cfg.policy (looked ++ [reason]))
    match record with
    | none => pure ()
    | some (.error reason) =>
        lastProblem := some (.invalid key mode s!"{path}: {reason}")
    | some (.ok evidence) =>
        if evidence.key != key then
          lastProblem := some (.invalid key mode
            s!"record is filed under key '{evidence.key}', not '{key}'")
        else if evidence.mode != mode then
          lastProblem := some (.invalid key mode
            s!"record in {path} declares mode '{evidence.mode.name}'")
        else if cfg.requireLiveMachine && evidence.machine != liveMachine then
          lastProblem := some (.stale key mode
            s!"the record was produced on '{evidence.machine}'; this is '{liveMachine}'")
        else
          return .ok evidence
  match lastProblem with
  | some failure => return .error failure
  | none => return .error (.noEvidence key cfg.policy looked)

/-- Append one line to the resolution ledger, so that which regime satisfied
which obligation is recorded rather than inferred.  Ledger writes never fail a
build: an unwritable ledger is a reporting problem, not a soundness one. -/
def appendLedger (cfg : EvidenceConfig) (declName : String)
    (evidence : ResolvedEvidence) : IO Unit := do
  try
    if let some dir := cfg.ledger.parent then
      IO.FS.createDirAll dir
    let line :=
      s!"{declName} key={evidence.key} mode={evidence.mode.name} " ++
      s!"shard={evidence.shard.campaign}[{evidence.shard.index}/{evidence.shard.count}] " ++
      s!"artifact={evidence.artifactDigest} machine={evidence.machine} " ++
      s!"expected={evidence.expected} recorded-at={evidence.recordedAt}\n"
    let handle ← IO.FS.Handle.mk cfg.ledger IO.FS.Mode.append
    handle.putStr line
  catch _ => pure ()

end LeanCompCert.Trusted
