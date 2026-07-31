import LeanCompCert.Trusted.ArtifactRun

/-!
# Worked instances: what `verify` accepts, and what it refuses

`Trusted/Evidence.lean` proves the negative facts *in general*.  This file
exhibits them on concrete records, so that a reader can see the checker run
and so that a regression in `verify` fails a build rather than a review.

The program is `copyIdxProgram`, whose denotation the kernel can evaluate
outright (`copyIdxProgram.denote = some 2` is `rfl`).  That makes it a genuine
**positive control**: the admitted value is independently known, so a record
that made `verify` accept the wrong answer would be caught here.

Nothing in this file uses the tactic, because the tactic reads evidence files
produced out of band and a fresh checkout has none.  For the tactic end to end,
see `tests/evidenced-decide/`.
-/

namespace LeanCompCert.Trusted.Demo

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Trusted

/-! ## The positive control -/

/-- The kernel knows the answer.  Independent of everything below. -/
theorem demo_denote : copyIdxProgram.denote = some 2 := rfl

def demoShard : ShardId := {
  campaign := "campaign:copyIdx"
  index := 0
  count := 1
  lo := 0
  hi := 3
  carryIn := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  carryOut := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" }

def demoChallenge : RunChallenge := {
  program := copyIdxProgram
  expected := 2
  shard := demoShard
  artifactDigest := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  toolchain := "compcert-3.17-freestanding-x86_64"
  machine := "machine-id:00000000000000000000000000000000" }

def demoFacts : RunFacts := {
  artifactDigest := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  toolchain := "compcert-3.17-freestanding-x86_64"
  machine := "machine-id:00000000000000000000000000000000"
  observed := 2
  echoedNonce := ""
  verdict := .agrees
  recordedAt := "2026-07-31T00:00:00Z" }

/-- A well-formed cache record: the fast path a routine build takes. -/
def cachedEvidence : RunEvidence := .cachedStamp demoChallenge demoFacts

/-- The challenge nonce for the fresh-run records below. -/
def nonceA : String :=
  "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"

/-- A different nonce — one nobody could have predicted before the run that
produced `nonceA`'s evidence. -/
def nonceB : String :=
  "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"

/-- A well-formed fresh-run record, echoing the nonce it was challenged with. -/
def freshEvidence : RunEvidence :=
  .freshRun demoChallenge nonceA { demoFacts with echoedNonce := nonceA }

/-! ## Accepted -/

theorem cached_accepted : cachedEvidence.verify 2 = true := by rfl

theorem fresh_accepted : freshEvidence.verify 2 = true := by rfl

/-- The admitted value is the value the kernel computes.  This is the check
that a passing record cannot be passing for the wrong reason. -/
theorem accepted_value_is_right :
    copyIdxProgram.denote = some 2 := demo_denote

/-! ## Refused

One instance per failure mode.  Each is `rfl`, so `verify` really runs. -/

/-- Wrong artifact digest. -/
theorem refuse_wrong_artifact :
    RunEvidence.verify
      (.cachedStamp demoChallenge
        { demoFacts with
            artifactDigest :=
              "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" })
      2 = false := by rfl

/-- Wrong machine: a stamp carried over from another host. -/
theorem refuse_wrong_machine :
    RunEvidence.verify
      (.cachedStamp demoChallenge
        { demoFacts with
            machine := "machine-id:11111111111111111111111111111111" })
      2 = false := by rfl

/-- **Wrong nonce.**  Evidence produced under `nonceA` cannot answer a claim
quoting `nonceB`; a stale record fails rather than silently passing. -/
theorem refuse_wrong_nonce :
    RunEvidence.verify
      (.freshRun demoChallenge nonceB { demoFacts with echoedNonce := nonceA })
      2 = false := by rfl

/-- **A cache read cannot masquerade as a run.**  A cached stamp claiming to
have echoed a nonce fails. -/
theorem refuse_cached_claiming_nonce :
    RunEvidence.verify
      (.cachedStamp demoChallenge { demoFacts with echoedNonce := nonceA })
      2 = false := by rfl

/-- Truncated record: a 63-character digest. -/
theorem refuse_truncated_digest :
    RunEvidence.verify
      (.cachedStamp
        { demoChallenge with
            artifactDigest :=
              "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" }
        { demoFacts with
            artifactDigest :=
              "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" })
      2 = false := by rfl

/-- Truncated record: an empty machine identity. -/
theorem refuse_empty_machine :
    RunEvidence.verify
      (.cachedStamp { demoChallenge with machine := "" }
        { demoFacts with machine := "" })
      2 = false := by rfl

/-- Mismatched output: the record answers `2`, the claim says `3`. -/
theorem refuse_wrong_value :
    cachedEvidence.verify 3 = false := by rfl

/-- Wrong program: the axiom's binding premise `e.challenge.program = p` holds
for `copyIdxProgram` and for nothing else.  This is the clause that used to live
inside `verify`; moving it out made it O(1) and made it work for programs the
kernel cannot reduce. -/
theorem binds_this_program : cachedEvidence.challenge.program = copyIdxProgram :=
  rfl

/-- And it is a real constraint: the same record does not bind a program with a
different trip count. -/
theorem refuse_wrong_program :
    cachedEvidence.challenge.program ≠ { copyIdxProgram with loopCount := 4 } := by
  decide

/-- And the binding costs the same for a program the kernel cannot evaluate: it
is one delta step on the evidence constant and two projections, never a walk
over the instruction lists. -/
example : cachedEvidence.challenge.expected = 2 := rfl

/-- A disagreement is not an agreement. -/
theorem refuse_disagrees :
    RunEvidence.verify
      (.cachedStamp demoChallenge { demoFacts with verdict := .disagrees })
      2 = false := by rfl

/-- An abnormal termination says nothing about the computed value, and is
never reported as a disagreement — nor accepted as an agreement. -/
theorem refuse_abnormal :
    RunEvidence.verify
      (.cachedStamp demoChallenge { demoFacts with verdict := .abnormal })
      2 = false := by rfl

/-- An incoherent shard: shard 3 of 2. -/
theorem refuse_bad_shard :
    RunEvidence.verify
      (.cachedStamp
        { demoChallenge with shard := { demoShard with index := 3, count := 2 } }
        demoFacts)
      2 = false := by rfl

/-- TDX attestation is not implemented and does not pretend to be. -/
theorem refuse_tdx :
    RunEvidence.verify
      (.tdxAttested demoChallenge nonceA
        { quoteDigest := "0000000000000000000000000000000000000000000000000000000000000000"
          reportData := "0000000000000000000000000000000000000000000000000000000000000000"
          pinnedKey := "0000000000000000000000000000000000000000000000000000000000000000" })
      2 = false := by rfl

/-! ## The admission, exhibited

This is the only declaration in the package that carries the axiom without
going through the tactic. -/

/-- Admitting the run of `copyIdxProgram` from the cached record.  The kernel
independently knows the same fact (`demo_denote`), so this exhibits the
mechanism without asserting anything new. -/
theorem demo_admitted : copyIdxProgram.denote = some 2 :=
  denote_of_evidence cachedEvidence binds_this_program cached_accepted

end LeanCompCert.Trusted.Demo
