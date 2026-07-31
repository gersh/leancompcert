import Lean
import LeanCompCert.Trusted.ArtifactRun
import LeanCompCert.Trusted.Resolve

/-!
# `evidenced_decide` — one word, like `native_decide`

```lean
theorem shard7 : myProgram.denote = some 4 := by evidenced_decide
```

The tactic states the obligation and nothing else.  **How** the obligation is
resolved — a cache stamp, a fresh run, an attestation — is a configuration
decision made outside Lean (`LeanCompCert/Trusted/Resolve.lean`), so switching
from iterating locally to producing attested evidence never means editing Lean
source, and the proof term is the same either way.

What it does, in order:

1. reads the goal, which must be `p.denote = some n` for a closed `p`;
2. resolves evidence for the obligation's **key** — the string argument if
   given, otherwise the enclosing declaration's name — through the configured
   policy;
3. mints two auxiliary declarations:
   * `<decl>._evidenced.run.evidence : RunEvidence`, the record, as data, and
   * `<decl>._evidenced.run.ax : EvidencedRun`, **a fresh axiom for this use
     site**;
4. closes the goal with
   `ax p n evidence (rfl : evidence.challenge.program = p) (rfl : verify evidence n = true)`,
   so the kernel re-checks both that the record is about *this* program and
   that it answers *this* claim;
5. appends a line to the ledger recording which regime satisfied which
   obligation.

Step 3 is why `#print axioms` on a downstream theorem enumerates **one entry
per admitted execution** rather than collapsing a 230-shard campaign into one
line.  It is deliberately the same idiom as `native_decide`'s
`<decl>._native.native_decide.ax_1_1`.

## Failure is loud, and the three kinds are distinguishable

There is no silent fallback.  On failure the tactic reports which of these
happened:

* **no evidence available** — the policy was walked and no record was found;
  recoverable by producing evidence;
* **evidence present but stale** — a record exists but was produced on another
  machine; recoverable by re-running here;
* **evidence present but invalid** — a record exists, is current, and does not
  answer the claim; *not* recoverable by re-running, and a real problem.

A missing configuration file is its own, fourth failure: fail closed rather
than defaulting to the weakest option.

## Cost

Resolution is a file read and a `/etc/machine-id` comparison.  The kernel check
is `verify`, whose price is bounded by the program's *source* size and is
independent of its `loopCount` — a shard that ran for twenty core-hours costs
exactly what a shard that ran for a second costs.  That is the property that
makes this a replacement for `native_decide` rather than merely a better trust
story: builds do not redo the work.
-/

namespace LeanCompCert.Trusted

open Lean Elab Tactic Meta
open LeanCompCert.Verified.ArrayState

/-! ## Reflecting a resolved record back into an `Expr`

The record supplies every field **except the program**, which is taken from
the goal.  A file therefore cannot claim to be about a different program than
the one under proof: that binding is made here and re-checked by `verify` in
the kernel. -/

private def strE (s : String) : Expr := Expr.lit (.strVal s)

private def verdictE : RunVerdict → Expr
  | .agrees => mkConst ``RunVerdict.agrees
  | .disagrees => mkConst ``RunVerdict.disagrees
  | .abnormal => mkConst ``RunVerdict.abnormal

private def shardE (s : ShardId) : Expr :=
  mkAppN (mkConst ``ShardId.mk)
    #[strE s.campaign, mkNatLit s.index, mkNatLit s.count, mkNatLit s.lo,
      mkNatLit s.hi, strE s.carryIn, strE s.carryOut]

private def challengeE (p : Expr) (r : ResolvedEvidence) : Expr :=
  mkAppN (mkConst ``RunChallenge.mk)
    #[p, mkNatLit r.expected, shardE r.shard, strE r.artifactDigest,
      strE r.toolchain, strE r.machine]

private def factsE (r : ResolvedEvidence) : Expr :=
  mkAppN (mkConst ``RunFacts.mk)
    #[strE r.artifactDigest, strE r.toolchain, strE r.machine,
      mkNatLit r.observed, strE r.echoedNonce, verdictE r.verdict,
      strE r.recordedAt]

private def evidenceE (p : Expr) (r : ResolvedEvidence) : Expr :=
  match r.mode with
  | .cache =>
      mkApp2 (mkConst ``RunEvidence.cachedStamp) (challengeE p r) (factsE r)
  | .run =>
      mkApp3 (mkConst ``RunEvidence.freshRun) (challengeE p r) (strE r.nonce)
        (factsE r)
  | .attest =>
      mkApp3 (mkConst ``RunEvidence.tdxAttested) (challengeE p r) (strE r.nonce)
        (mkAppN (mkConst ``TdxQuoteRef.mk)
          #[strE r.quoteDigest, strE r.reportData, strE r.pinnedKey])

/-- Names for this use site's auxiliary declarations, avoiding collisions when
one declaration admits several computations. -/
private def freshAuxNames (base : Name) : MetaM (Name × Name) := do
  let env ← getEnv
  let root := base ++ `_evidenced ++ `run
  let mut axName := root ++ `ax
  let mut evName := root ++ `evidence
  let mut i := 1
  while env.contains axName do
    i := i + 1
    axName := root ++ Name.mkSimple s!"ax_{i}"
    evName := root ++ Name.mkSimple s!"evidence_{i}"
  return (axName, evName)

/-- `evidenced_decide` — admit an out-of-band artifact run.

Optionally takes the obligation's key as a string literal; it defaults to the
enclosing declaration's name. -/
syntax (name := evidencedDecide) "evidenced_decide" (ppSpace str)? : tactic

@[tactic evidencedDecide] def evalEvidencedDecide : Tactic := fun stx => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← whnfR (← instantiateMVars (← goal.getType))
    let some (_, lhs, rhs) := target.eq?
      | throwError ("evidenced_decide: the goal is not an equation.\n" ++
          "  It must have the shape `p.denote = some n` with `p : AProgram` closed.\n" ++
          "  What this tactic discharges is an EXECUTION, not your mathematics: the\n" ++
          "  step from `p.denote = some n` to the statement you care about is the\n" ++
          "  encoding gap, and it is yours to prove.")
    unless lhs.isAppOfArity ``AProgram.denote 1 do
      throwError m!"evidenced_decide: the left-hand side is not `AProgram.denote p`.{indentExpr lhs}"
    let p := lhs.appArg!
    unless rhs.isAppOfArity ``Option.some 2 do
      throwError m!"evidenced_decide: the right-hand side is not `some n`.{indentExpr rhs}"
    let nOrig := rhs.appArg!
    let some n := (← whnf nOrig).rawNatLit?
      | throwError m!"evidenced_decide: the claimed value is not a numeral.{indentExpr nOrig}"
    if p.hasFVar || p.hasMVar then
      throwError ("evidenced_decide: the program must be closed.\n" ++
        "  It becomes part of an auxiliary definition, so it cannot mention local\n" ++
        "  hypotheses or metavariables.")
    let declName := (← Lean.Elab.Term.getDeclName?).getD `_evidencedDecide
    let key :=
      match stx[1].getOptional? with
      | some lit => lit.isStrLit?.getD declName.toString
      | none => declName.toString
    -- Resolution: entirely outside Lean.
    let cfg ←
      match ← readConfig with
      | .error failure => throwError failure.message
      | .ok cfg => pure cfg
    let resolved ←
      match ← resolve cfg key with
      | .error failure => throwError failure.message
      | .ok resolved => pure resolved
    if resolved.expected != n then
      throwError (ResolveFailure.invalid key resolved.mode
        s!"the record reports expected={resolved.expected}, the goal claims {n}").message
    if resolved.observed != n then
      throwError (ResolveFailure.invalid key resolved.mode
        s!"the record reports observed={resolved.observed}, the goal claims {n}").message
    -- The record, as data.
    let (axName, evName) ← freshAuxNames declName
    addDecl (Declaration.defnDecl {
      name := evName
      levelParams := []
      type := mkConst ``RunEvidence
      value := evidenceE p resolved
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe })
    let evConst := mkConst evName
    let verifyApp := mkApp2 (mkConst ``RunEvidence.verify) evConst nOrig
    let trueE := mkConst ``Bool.true
    unless (← whnf verifyApp).isConstOf ``Bool.true do
      throwError (ResolveFailure.invalid key resolved.mode
        ("`RunEvidence.verify` rejects the record from " ++ resolved.path ++ ".\n" ++
         "  Every clause of the checker is documented in Trusted/Evidence.lean; the\n" ++
         "  usual causes are a digest that is not 64 lowercase hex characters, an\n" ++
         "  identity label outside 8..256 characters, an incoherent shard, a verdict\n" ++
         "  that is not `agrees`, a cached stamp claiming a nonce, or a fresh run\n" ++
         "  whose echoed nonce differs from the one it was challenged with.")).message
    -- One axiom for this use site, of exactly the shared schema type.
    addDecl (Declaration.axiomDecl {
      name := axName
      levelParams := []
      type := mkConst ``EvidencedRun
      isUnsafe := false })
    let hVerify ←
      mkExpectedTypeHint (← mkEqRefl trueE) (← mkEq verifyApp trueE)
    -- The program binding, discharged definitionally: the evidence constant
    -- unfolds to a constructor and two projections give back exactly `p`.  A
    -- couple of iota steps, whatever the program is — which is the point, and
    -- why this is a premise instead of a clause of `verify`.
    let evProgram :=
      mkApp (mkConst ``RunChallenge.program)
        (mkApp (mkConst ``RunEvidence.challenge) evConst)
    let hBind ← mkExpectedTypeHint (← mkEqRefl p) (← mkEq evProgram p)
    goal.assign (mkAppN (mkConst axName) #[p, nOrig, evConst, hBind, hVerify])
    replaceMainGoal []
    appendLedger cfg declName.toString resolved

end LeanCompCert.Trusted
