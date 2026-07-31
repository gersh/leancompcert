# `evidenced_decide`, end to end

This directory is not part of `lake build`, on purpose: the tactic reads
evidence records produced **out of band**, and a fresh checkout has none.  A
default build that needed a run to have happened would defeat the point.

## Run it

```bash
# 0. the artifact's generated C, and a passing native cross-check
lake exe lean-compcert check-native --force

# 1a. a cache record — reads the stamp; costs nothing
scripts/produce-evidence.sh mobius-seg --mode cache

# 1b. or a fresh run — embeds a 256-bit challenge nonce in the compiled C,
#     so no earlier stamp can match, and executes the artifact now
scripts/produce-evidence.sh mobius-seg --mode run

# 2. choose a policy (there is no default; a missing config fails closed)
cp leancompcert-evidence.local.cfg.example leancompcert-evidence.local.cfg

# 3. elaborate the obligation
LEAN_PATH=.lake/build/lib/lean lake env lean tests/evidenced-decide/Shard.lean
```

## What to look at

* `evidence/mobius-seg.cache.evidence` — the record.  Every field `verify`
  checks is in it, in plain text.
* `evidence/ledger.log` — one line per resolved obligation, recording which
  regime satisfied it.  Resolution is recorded, not inferred.
* the `#print axioms` output at the end of `Shard.lean` — one entry per
  admitted execution, named after the use site.

## Things worth breaking on purpose

Each of these must fail, and must fail *differently*:

| edit | expected failure |
| --- | --- |
| delete `evidence/mobius-seg.cache.evidence` | *no evidence available* — recoverable |
| change `machine = ` to another id | *evidence present but stale* — recoverable |
| change `expected = 4` to `5` | *evidence present but invalid* — not recoverable |
| truncate `artifact-digest` by one character | *invalid*: `verify` rejects the record |
| copy the `run` record to `<key>.cache.evidence` | *invalid*: a cache record may not echo a nonce |
| delete `leancompcert-evidence.cfg` | *no evidence configuration* — fail closed |
