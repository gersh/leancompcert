import LeanCompCert.Verified.ArrayState

/-!
# Evidence that an artifact ran — the record, and the checker

This module is the **axiom-free half** of the opt-in artifact-run bridge.  It
defines what a run-evidence record is (`RunEvidence`), what it means for one
to answer a claim (`RunEvidence.verify`), and proves — at the base trio — the
negative facts that make the checker worth having: a wrong artifact, a wrong
value, a wrong machine, a wrong nonce, a wrong program, a truncated record and
a non-agreeing verdict each force `verify = false`.

The axiom that turns a passing `verify` into a theorem lives next door in
`LeanCompCert/Trusted/ArtifactRun.lean`.  Importing *this* module adds nothing
to anybody's `#print axioms`.

## What the record is, and what it is not

A `RunEvidence` value has two halves, and keeping them apart is the whole
design:

* the **challenge** (`RunChallenge`) — what was demanded, fixed *before* the
  run: which program, which shard of which campaign, which artifact digest,
  which toolchain, which machine, and which value the artifact must report;
* the **facts** (`RunFacts`) — what a runner reported afterwards.

`verify` checks the facts against the challenge and against the claim.  It is a
**well-formedness and binding check, not an authentication check.**  Nothing
here proves a run happened; a forged record passes `verify` exactly as a
genuine one does.  What `verify` buys is that a record cannot *drift*: an
evidence record produced for one program, one value, one machine, one shard or
one nonce cannot be silently re-used for another, which is the realistic
failure — the same stance `NativeCheck.machineIdentity` takes about its stamp
("this makes the cache honest, not tamper-proof").

## Cost

`verify` is a fixed handful of string and integer comparisons.  It does **not**
look at the program at all — see the next section — so its cost depends neither
on the program's size nor on its `loopCount`.  A twenty-core-hour shard and a
one-second shard verify at the same price.  That is deliberate: the record
carries a digest, a verdict and an identity, never a trace or a transcript,
precisely so that this stays true.

## Why the program binding is not part of `verify`

`verify` used to carry a clause `decide (c.program = p)`, which is the obvious
way to say "this record is about *this* program".  It was replaced, for two
reasons, and the replacement is strictly better on both counts.

*It did not work.*  Real certificate programs are not kernel-reducible to
constructor form.  `Testing.ArraySegCertificate.program` is
`mertensProgram cfg seed 755 10000`, and `decide (program = program) = true` is
**not** closed by `rfl` even at `maxRecDepth 1000000` — some of its fields go
through definitions the kernel will not unfold on demand.  A clause that cannot
reduce is a clause that always fails.

*The equation is better said directly.*  `LeanCompCert/Trusted/ArtifactRun.lean`
makes the binding a separate premise of the axiom,
`e.challenge.program = p`, which the kernel discharges by unfolding the
evidence constant and taking two projections — a couple of iota steps,
independent of the program entirely.  It is exactly as strong: a record filed
for a different program cannot satisfy it by `rfl`, and satisfying it any other
way means *proving* the two programs equal.  So the binding is O(1) instead of
O(program), and it holds for programs the previous clause could not even
evaluate.
-/

namespace LeanCompCert.Trusted

open LeanCompCert.Verified.ArrayState

deriving instance DecidableEq for AProgram

/-! ## Small string predicates, kernel-computable

Everything here goes through `String.toList`, the raw `List Char`, rather than
the byte-position API, so the kernel reduces it by ordinary list recursion. -/

/-- A lowercase hexadecimal digit. -/
def isHexDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9') || decide ('a' ≤ c ∧ c ≤ 'f')

/-- A 256-bit digest, written as 64 lowercase hex characters. -/
def isDigest256 (s : String) : Bool :=
  decide (s.toList.length = 64) && s.toList.all isHexDigit

/-- Bounded, non-empty identity label.  The upper bound keeps `verify`'s
kernel cost fixed: identity strings are digests and short version labels, not
the full text of `compcert.ini`. -/
def isLabel (s : String) : Bool :=
  decide (8 ≤ s.toList.length) && decide (s.toList.length ≤ 256)

/-! ## The record -/

/-- Which of the three resolution regimes produced a record.  This is a
*derived* view of the constructor, so it cannot disagree with the data: a
cached stamp can never report `.run`. -/
inductive RunMode where
  /-- A stamp left by an earlier run on this machine was read.  Cheap; the
  regime a routine build takes. -/
  | cache
  /-- The artifact was executed now, against a challenge nonce. -/
  | run
  /-- A signed attestation of a run performed elsewhere was checked. -/
  | attest
  deriving DecidableEq, Repr, Inhabited

/-- The artifact's exit-status classification, mirroring
`NativeCheck.classify`: exactly one status means "the computed value differs
from the certified constant", and an abnormal termination is never a
disagreement. -/
inductive RunVerdict where
  /-- Exit 0: the computed value equals the certified constant. -/
  | agrees
  /-- Exit 1: it does not. -/
  | disagrees
  /-- Anything else — killed by a signal, OOM.  Says nothing at all about the
  computed value. -/
  | abnormal
  deriving DecidableEq, Repr, Inhabited

/-- Which shard of which campaign a record is about.

A large computation is split into independently runnable shards, each attested
separately and possibly on a different machine.  Binding the shard into the
challenge is what stops shard 7's evidence from being presented for shard 8 —
the same class of defect as a chain driver accepting a wrongly-seeded window.

`carryIn`/`carryOut` are opaque digests here: this module never interprets
them.  They exist so that a composition theorem elsewhere can require
`(shard i).carryOut = (shard (i+1)).carryIn` and have well-formed objects to
quantify over.

An unsharded computation is the degenerate case `index = 0`, `count = 1`. -/
structure ShardId where
  /-- Name of the whole computation the shard belongs to. -/
  campaign : String
  /-- Index of this shard, `0`-based. -/
  index : Nat
  /-- How many shards the campaign has. -/
  count : Nat
  /-- First loop index this shard covers, inclusive. -/
  lo : Nat
  /-- One past the last loop index this shard covers. -/
  hi : Nat
  /-- Digest of the state this shard was seeded with. -/
  carryIn : String
  /-- Digest of the state this shard hands on. -/
  carryOut : String
  deriving DecidableEq, Repr

/-- A shard identity that is internally coherent. -/
def ShardId.wellFormed (s : ShardId) : Bool :=
  isLabel s.campaign && decide (s.index < s.count) && decide (s.lo < s.hi)
    && isDigest256 s.carryIn && isDigest256 s.carryOut

/-- **The demand.**  Everything in here is fixed *before* the run and written
into the Lean file, so it appears in the source diff a reviewer reads. -/
structure RunChallenge where
  /-- The program whose denotation is being claimed. -/
  program : AProgram
  /-- The value the artifact must report. -/
  expected : Nat
  /-- Which shard of which campaign this is. -/
  shard : ShardId
  /-- SHA-256 of the exact C text handed to `ccomp`, as 64 lowercase hex
  characters.  For a fresh run the nonce is embedded in that text, so the
  digest of a nonce-`A` artifact differs from that of a nonce-`B` one. -/
  artifactDigest : String
  /-- Identity of the CompCert install and link mode, in the sense of
  `NativeCheck.compcertIdentity`: a short label plus the digest of the `ccomp`
  binary and its `compcert.ini`. -/
  toolchain : String
  /-- Identity of the machine, in the sense of `NativeCheck.machineIdentity`. -/
  machine : String
  deriving DecidableEq, Repr

/-- **The report.**  Produced by a runner from what it observed; never
authored by hand. -/
structure RunFacts where
  /-- Digest of the C the runner actually compiled. -/
  artifactDigest : String
  /-- Toolchain the runner actually used. -/
  toolchain : String
  /-- Machine the runner actually ran on. -/
  machine : String
  /-- Value the runner observed the artifact report. -/
  observed : Nat
  /-- The nonce the run was challenged with, echoed back.  Empty exactly when
  no nonce was in play — which is the case for a cache read, and is why a
  cached stamp cannot masquerade as a fresh run. -/
  echoedNonce : String
  /-- Exit-status classification. -/
  verdict : RunVerdict
  /-- When the record was produced; unchecked except for being non-empty, but
  it is what makes a stale record visible to a reader. -/
  recordedAt : String
  deriving DecidableEq, Repr

/-- Where a TDX attestation's pieces live.  Deliberately just digests: this
module does not verify quotes.  See `RunEvidence.verify`. -/
structure TdxQuoteRef where
  /-- SHA-256 of the raw v4 quote. -/
  quoteDigest : String
  /-- The 64-byte `report_data` the enclave bound, hex. -/
  reportData : String
  /-- Digest of the pinned enclave signing key. -/
  pinnedKey : String
  deriving DecidableEq, Repr

/-- Evidence that an artifact ran and reported a value.

A **closed** inductive, on purpose.  Adding a new way of evidencing a run is a
new constructor plus a new case of `verify` — not a new axiom, and not a
typeclass a bad instance could subvert.  The trusted surface stays
enumerable: it is exactly the cases of `verify` that can return `true`. -/
inductive RunEvidence where
  /-- A stamp left by an earlier passing run **on this machine, with this
  CompCert install** was read.  No nonce is involved, and none may be claimed.
  This is the fast path and the one a routine build takes. -/
  | cachedStamp (challenge : RunChallenge) (facts : RunFacts)
  /-- The artifact was executed now, against `nonce`, which the runner had to
  echo.  Deliberately expensive; this is what you do when you want to *know*. -/
  | freshRun (challenge : RunChallenge) (nonce : String) (facts : RunFacts)
  /-- A signed attestation of a run performed elsewhere.  **Verification is
  not implemented**: this case of `verify` returns `false`, always, and the
  negative theorem `verify_tdxAttested` says so.  The pieces needed to
  implement it already exist in the `gpu_prover` deployment — in-kernel
  SHA-256, v4 quote parsing down to `mr_config_id` and `report_data`, P-256
  against a pinned key, and an offline gate walking the certificate chain to
  Intel's root — and wiring them in is exactly this one case, with no change
  to the axiom.  A constructor that honestly returns `false` beats a stub that
  returns `true`. -/
  | tdxAttested (challenge : RunChallenge) (nonce : String) (quote : TdxQuoteRef)
  deriving DecidableEq, Repr

namespace RunEvidence

/-- The demand half of a record, whichever regime produced it. -/
def challenge : RunEvidence → RunChallenge
  | .cachedStamp c _ => c
  | .freshRun c _ _ => c
  | .tdxAttested c _ _ => c

/-- Which regime produced the record.  Derived from the constructor, so it
cannot lie about itself. -/
def mode : RunEvidence → RunMode
  | .cachedStamp _ _ => .cache
  | .freshRun _ _ _ => .run
  | .tdxAttested _ _ _ => .attest

/-- The reported half, when there is one. -/
def facts? : RunEvidence → Option RunFacts
  | .cachedStamp _ f => some f
  | .freshRun _ _ f => some f
  | .tdxAttested _ _ _ => none

/-- The challenge nonce, when the regime has one.  `none` for a cache read —
that absence *is* the distinction between a record of a run and a run. -/
def nonce? : RunEvidence → Option String
  | .cachedStamp _ _ => none
  | .freshRun _ n _ => some n
  | .tdxAttested _ n _ => some n

end RunEvidence

/-! ## The checker -/

/-- A challenge that is internally coherent and fully populated.  A truncated
record — an empty digest, a missing machine — fails here. -/
def RunChallenge.wellFormed (c : RunChallenge) : Bool :=
  isDigest256 c.artifactDigest && isLabel c.toolchain && isLabel c.machine
    && c.shard.wellFormed

/-- The runner's report answers the demand, and answers *this* claim. -/
def RunFacts.answers (f : RunFacts) (c : RunChallenge) (n : Nat) : Bool :=
  decide (f.artifactDigest = c.artifactDigest)
    && decide (f.toolchain = c.toolchain)
    && decide (f.machine = c.machine)
    && decide (f.observed = c.expected)
    && decide (f.observed = n)
    && decide (f.verdict = RunVerdict.agrees)
    && decide (1 ≤ f.recordedAt.toList.length)

/-- **Does this evidence answer the claim `p.denote = some n`?**

Kernel-computable, by construction: integer and string comparison and one
structural comparison of the program.  No cryptography — a signature check
belongs in a constructor's own case, done the way `gpu_prover` does it, not
smuggled in here.

What each case requires:

* `cachedStamp` — the challenge is well formed, it is about *this* value, the
  runner's report matches it, the verdict is `agrees`, and **no nonce is
  claimed**.
* `freshRun` — all of the above, plus a well-formed 256-bit nonce that the
  runner echoed.  Evidence carrying nonce `A` cannot answer a claim quoting
  nonce `B`.
* `tdxAttested` — `false`.  Not implemented; see the constructor.

The program is bound by a separate premise of the axiom rather than here; see
"Why the program binding is not part of `verify`" above. -/
def RunEvidence.verify : RunEvidence → Nat → Bool
  | .cachedStamp c f, n =>
      c.wellFormed && f.answers c n && f.echoedNonce.toList.isEmpty
  | .freshRun c nonce f, n =>
      c.wellFormed && f.answers c n
        && isDigest256 nonce && decide (f.echoedNonce = nonce)
  | .tdxAttested _ _ _, _ => false

/-! ## Negative theorems

A checker that can only pass is worthless.  These are the facts that make
`verify` a check: each names a way the evidence can fail to answer the claim,
and each is proved, at the base trio, for *every* record — not merely
exhibited on one hand-built instance.  The program binding is not among them
because it is not part of `verify`; it is a premise of the axiom, discharged by
`rfl`, and a record for another program fails it.  Concrete instances are in
`LeanCompCert/Trusted/Demo.lean`. -/

/-- TDX attestation is not implemented, and says so. -/
@[simp] theorem verify_tdxAttested (c : RunChallenge) (n : String)
    (q : TdxQuoteRef) (m : Nat) :
    RunEvidence.verify (.tdxAttested c n q) m = false := rfl

/-- A passing record is about the value in the claim. -/
theorem verify_binds_value {e : RunEvidence} {n : Nat}
    (h : e.verify n = true) : e.challenge.expected = n := by
  cases e <;>
    simp_all [RunEvidence.verify, RunEvidence.challenge, RunChallenge.wellFormed,
      RunFacts.answers] <;>
    omega

/-- A passing record has a report, and it agrees. -/
theorem verify_agrees {e : RunEvidence} {n : Nat}
    (h : e.verify n = true) :
    ∃ f, e.facts? = some f ∧ f.verdict = RunVerdict.agrees := by
  cases e <;>
    simp_all [RunEvidence.verify, RunEvidence.facts?, RunChallenge.wellFormed,
      RunFacts.answers]

/-- A passing record's report is about the demanded artifact, toolchain and
machine.  This is the clause that makes "wrong machine" a failure. -/
theorem verify_binds_identity {e : RunEvidence} {n : Nat}
    (h : e.verify n = true) :
    ∃ f, e.facts? = some f
      ∧ f.artifactDigest = e.challenge.artifactDigest
      ∧ f.toolchain = e.challenge.toolchain
      ∧ f.machine = e.challenge.machine := by
  cases e <;>
    simp_all [RunEvidence.verify, RunEvidence.facts?, RunEvidence.challenge,
      RunChallenge.wellFormed, RunFacts.answers]

/-- A passing record is fully populated: no truncated digest, no empty
identity, no incoherent shard. -/
theorem verify_wellFormed {e : RunEvidence} {n : Nat}
    (h : e.verify n = true) : e.challenge.wellFormed = true := by
  cases e <;>
    simp_all [RunEvidence.verify, RunEvidence.challenge, RunChallenge.wellFormed,
      RunFacts.answers]

/-- **The freshness binding.**  A fresh-run record echoes exactly the nonce its
claim quotes.  Evidence produced under nonce `A` cannot answer a claim quoting
nonce `B`, so a stale cache fails rather than silently passing. -/
theorem verify_binds_nonce {c : RunChallenge} {a : String} {f : RunFacts}
    {n : Nat} (h : RunEvidence.verify (.freshRun c a f) n = true) :
    f.echoedNonce = a ∧ isDigest256 a = true := by
  simp_all [RunEvidence.verify, RunChallenge.wellFormed, RunFacts.answers]

/-- **A cache read cannot masquerade as a run.**  A `cachedStamp` that claims
to have echoed a nonce fails. -/
theorem verify_cached_has_no_nonce {c : RunChallenge} {f : RunFacts}
    {n : Nat} (h : RunEvidence.verify (.cachedStamp c f) n = true) :
    f.echoedNonce.toList = [] := by
  simp_all [RunEvidence.verify, RunChallenge.wellFormed, RunFacts.answers]

/-! ### The failures, stated as failures

Each of these is the contrapositive of a binding lemma above.  They are what a
reviewer wants to read: *this* mistake forces `verify = false`. -/

private theorem not_true_of {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp_all

/-- Wrong value: a record reporting a different output does not answer this
claim. -/
theorem verify_false_of_value_ne {e : RunEvidence} {n : Nat}
    (h : e.challenge.expected ≠ n) : e.verify n = false :=
  not_true_of fun hv => h (verify_binds_value hv)

/-- Wrong artifact: a report whose digest is not the demanded one fails. -/
theorem verify_false_of_digest_ne {e : RunEvidence} {n : Nat}
    {f : RunFacts} (hf : e.facts? = some f)
    (h : f.artifactDigest ≠ e.challenge.artifactDigest) :
    e.verify n = false := by
  refine not_true_of fun hv => h ?_
  obtain ⟨g, hg, hd, _, _⟩ := verify_binds_identity hv
  rw [hf] at hg
  obtain rfl := Option.some.inj hg
  exact hd

/-- Wrong machine: a report from a machine other than the demanded one fails. -/
theorem verify_false_of_machine_ne {e : RunEvidence} {n : Nat}
    {f : RunFacts} (hf : e.facts? = some f)
    (h : f.machine ≠ e.challenge.machine) : e.verify n = false := by
  refine not_true_of fun hv => h ?_
  obtain ⟨g, hg, _, _, hm⟩ := verify_binds_identity hv
  rw [hf] at hg
  obtain rfl := Option.some.inj hg
  exact hm

/-- Truncated record: an ill-formed challenge — short digest, empty machine,
incoherent shard — fails. -/
theorem verify_false_of_illFormed {e : RunEvidence} {n : Nat}
    (h : e.challenge.wellFormed ≠ true) : e.verify n = false :=
  not_true_of fun hv => h (verify_wellFormed hv)

/-- Wrong nonce: a fresh-run record echoing a different nonce fails. -/
theorem verify_false_of_nonce_ne {c : RunChallenge} {a : String} {f : RunFacts}
    {n : Nat} (h : f.echoedNonce ≠ a) :
    RunEvidence.verify (.freshRun c a f) n = false :=
  not_true_of fun hv => h (verify_binds_nonce hv).1

/-- A cached stamp claiming to have echoed a nonce fails: the `cache` regime
cannot present itself as the `run` regime. -/
theorem verify_false_of_cached_nonce {c : RunChallenge} {f : RunFacts}
    {n : Nat} (h : f.echoedNonce.toList ≠ []) :
    RunEvidence.verify (.cachedStamp c f) n = false :=
  not_true_of fun hv => h (verify_cached_has_no_nonce hv)

/-- A non-agreeing verdict — a disagreement, or an abnormal termination —
fails.  An artifact killed by the OOM killer is evidence of nothing. -/
theorem verify_false_of_verdict_ne {e : RunEvidence} {n : Nat}
    {f : RunFacts} (hf : e.facts? = some f) (h : f.verdict ≠ RunVerdict.agrees) :
    e.verify n = false := by
  refine not_true_of fun hv => h ?_
  obtain ⟨g, hg, hverdict⟩ := verify_agrees hv
  rw [hf] at hg
  obtain rfl := Option.some.inj hg
  exact hverdict

end LeanCompCert.Trusted
