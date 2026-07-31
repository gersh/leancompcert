#!/usr/bin/env bash
# Produce a run-evidence record for one artifact, out of band.
#
#   scripts/produce-evidence.sh KEY --mode run   [--nonce HEX64] [shard options]
#   scripts/produce-evidence.sh KEY --mode cache [shard options]
#   scripts/produce-evidence.sh KEY --mode attest        (refuses: not implemented)
#
# This is the *only* thing that executes an artifact.  Builds read the record it
# writes; they never run anything.  That is what makes build time independent of
# how long the computation took.
#
# The two modes differ in exactly the way the evidence record says they do:
#
#   cache  A stamp left by an earlier passing `check-native` run on this machine
#          is read.  Cheap.  No nonce is involved, and the record says so — an
#          empty `echoed-nonce` is what stops a cache read from being presented
#          as a run.
#
#   run    A fresh 256-bit nonce is embedded in the generated C, so the artifact
#          digest is nonce-dependent and no earlier stamp can match it; the C is
#          compiled with CompCert and executed now.  Deliberately expensive.
#
# Shard options, for a computation split into independently runnable pieces:
#
#   --campaign NAME   default "campaign:KEY"
#   --shard I/N       default 0/1
#   --range LO:HI     default 0:1
#   --carry-in HEX64  default sha256("")
#   --carry-out HEX64 default sha256("")
#
# Exit status: 0 on a written record, non-zero otherwise.  A disagreeing or
# abnormally terminating artifact writes NO record: `verify` would refuse it
# anyway, and a file on disk that cannot be used is worse than no file.

set -euo pipefail

die() { printf 'produce-evidence: %s\n' "$*" >&2; exit 1; }

sha256() { sha256sum "$1" | awk '{print $1}'; }
sha256_stdin() { sha256sum | awk '{print $1}'; }

EMPTY_DIGEST=$(printf '' | sha256_stdin)

KEY=""
MODE=""
NONCE=""
CAMPAIGN=""
SHARD_INDEX=0
SHARD_COUNT=1
RANGE_LO=0
RANGE_HI=1
CARRY_IN="$EMPTY_DIGEST"
CARRY_OUT="$EMPTY_DIGEST"

while [ $# -gt 0 ]; do
  case "$1" in
    --mode) MODE="$2"; shift 2 ;;
    --nonce) NONCE="$2"; shift 2 ;;
    --campaign) CAMPAIGN="$2"; shift 2 ;;
    --shard) SHARD_INDEX="${2%%/*}"; SHARD_COUNT="${2##*/}"; shift 2 ;;
    --range) RANGE_LO="${2%%:*}"; RANGE_HI="${2##*:}"; shift 2 ;;
    --carry-in) CARRY_IN="$2"; shift 2 ;;
    --carry-out) CARRY_OUT="$2"; shift 2 ;;
    -*) die "unknown option $1" ;;
    *) [ -z "$KEY" ] || die "more than one key given"; KEY="$1"; shift ;;
  esac
done

[ -n "$KEY" ] || die "no key given"
[ -n "$MODE" ] || die "no --mode given (cache, run or attest)"
[ -n "$CAMPAIGN" ] || CAMPAIGN="campaign:$KEY"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CHECK_DIR="$ROOT/.lake/build/native-check"
EVIDENCE_DIR="$ROOT/evidence"
C_FILE="$CHECK_DIR/$KEY.c"
STAMP="$CHECK_DIR/$KEY.stamp"

mkdir -p "$EVIDENCE_DIR"

# ---------------------------------------------------------------- identities
# These must agree, character for character, with what
# LeanCompCert/Trusted/Resolve.lean computes live, and with the notions
# LeanCompCert/NativeCheck.lean already uses for its stamps.

machine_identity() {
  if [ -r /etc/machine-id ]; then
    printf 'machine-id:%s' "$(tr -d '[:space:]' < /etc/machine-id)"
  elif [ -r /var/lib/dbus/machine-id ]; then
    printf 'machine-id:%s' "$(tr -d '[:space:]' < /var/lib/dbus/machine-id)"
  else
    printf 'hostname:%s' "$(uname -n -m -s)"
  fi
}

# `ccomp -version` does not name the target architecture, so — exactly as
# NativeCheck.compcertIdentity explains — the binary and its compcert.ini are
# digested too.  Truncated to 32 hex so the label stays inside verify's bound.
toolchain_identity() {
  local link="$1" bin ini_text version digest
  bin="$(command -v ccomp)" || die "ccomp not on PATH"
  # Just the version number: `verify` bounds identity labels, and the record is
  # for machines to compare, not to read prose out of.
  version="$(ccomp -version 2>&1 | head -1 | grep -o '[0-9][0-9.]*' | head -1)"
  [ -n "$version" ] || version="unknown"
  ini_text=""
  for candidate in \
      "$(dirname "$bin")/compcert.ini" \
      "$(dirname "$(dirname "$bin")")/share/compcert.ini" \
      /usr/local/share/compcert.ini; do
    if [ -f "$candidate" ]; then ini_text="$(cat "$candidate")"; break; fi
  done
  digest="$( { sha256 "$bin"; printf '%s' "$ini_text"; } | sha256_stdin )"
  printf 'compcert-%s-%s-%s' "$version" "$link" "${digest:0:32}"
}

MACHINE="$(machine_identity)"

# ------------------------------------------------------------- the artifact

[ -f "$C_FILE" ] || die "no generated C at $C_FILE
  Produce it first:  lake exe lean-compcert check-native --force"

# The certified constant is read out of the artifact's own `main`, from the exact
# comparison whose result becomes the exit status, so it cannot drift from what
# was compiled.  Matching the whole `== UINT64_C(N) ? 0 : 1` shape matters: the
# generated C is full of other UINT64_C literals.
EXPECTED="$(sed -n 's/.*== UINT64_C(\([0-9][0-9]*\)) ? 0 : 1.*/\1/p' "$C_FILE" | head -1)"
[ -n "$EXPECTED" ] || die "could not read the certified constant out of $C_FILE"

RECORDED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

write_record() {
  local mode="$1" digest="$2" toolchain="$3" nonce="$4" echoed="$5" verdict="$6"
  local out="$EVIDENCE_DIR/$KEY.$mode.evidence"
  cat > "$out" <<EOF
format = lean-compcert-evidence/1
mode = $mode
key = $KEY
expected = $EXPECTED
observed = $EXPECTED
verdict = $verdict
artifact-digest = $digest
toolchain = $toolchain
machine = $MACHINE
nonce = $nonce
echoed-nonce = $echoed
recorded-at = $RECORDED_AT
shard-campaign = $CAMPAIGN
shard-index = $SHARD_INDEX
shard-count = $SHARD_COUNT
shard-lo = $RANGE_LO
shard-hi = $RANGE_HI
shard-carry-in = $CARRY_IN
shard-carry-out = $CARRY_OUT
EOF
  printf 'produce-evidence: wrote %s\n' "$out"
}

case "$MODE" in
  cache)
    [ -f "$STAMP" ] || die "no stamp at $STAMP
  A cache record asserts that THIS machine already compiled and ran exactly this
  generated C.  There is no stamp, so there is nothing to record.  Run:
      lake exe lean-compcert check-native"
    grep -q ' pass$' "$STAMP" || die "the stamp at $STAMP is not a passing stamp"
    DIGEST="$(sha256 "$C_FILE")"
    write_record cache "$DIGEST" "$(toolchain_identity freestanding)" "" "" agrees
    ;;

  run)
    if [ -z "$NONCE" ]; then
      NONCE="$(head -c 32 /dev/urandom | od -An -tx1 | tr -d ' \n')"
    fi
    case "$NONCE" in
      *[!0-9a-f]* | "") die "the nonce must be lowercase hex" ;;
    esac
    [ "${#NONCE}" -eq 64 ] || die "the nonce must be 64 hex characters (256 bits)"

    WORK="$(mktemp -d)"
    trap 'rm -rf "$WORK"' EXIT
    NONCED="$WORK/$KEY.c"
    # The nonce goes INTO the compiled source, so the artifact digest is
    # nonce-dependent: no stamp from an earlier nonce can match this one, and a
    # fresh nonce forces a real compile and a real execution.
    {
      printf '/* lean-compcert challenge nonce: %s */\n' "$NONCE"
      cat "$C_FILE"
      printf 'static const char lean_compcert_nonce[] = "%s";\n' "$NONCE"
    } > "$NONCED"
    DIGEST="$(sha256 "$NONCED")"

    ARCH="$(uname -m)"
    case "$ARCH" in
      aarch64|arm64) STUB_ARCH=aarch64 ;;
      x86_64|amd64) STUB_ARCH=x86_64 ;;
      *) STUB_ARCH="" ;;
    esac
    STUB="$ROOT/runtime/start/$STUB_ARCH.S"

    if [ -n "$STUB_ARCH" ] && [ -f "$STUB" ]; then
      LINK=freestanding
      as -o "$WORK/start.o" "$STUB"
      ccomp -c -o "$WORK/$KEY.o" "$NONCED"
      ld -o "$WORK/$KEY.exe" "$WORK/start.o" "$WORK/$KEY.o"
    else
      LINK=hosted
      ccomp -o "$WORK/$KEY.exe" "$NONCED"
    fi

    set +e
    "$WORK/$KEY.exe"
    STATUS=$?
    set -e

    case "$STATUS" in
      0) VERDICT=agrees ;;
      1) die "the artifact DISAGREES with the certified constant (exit 1).
  No record written." ;;
      *) die "ABNORMAL TERMINATION (exit $STATUS) — not a disagreement.
  The artifact did not report a value comparison at all, so this run is evidence
  of nothing.  No record written." ;;
    esac

    write_record run "$DIGEST" "$(toolchain_identity "$LINK")" "$NONCE" "$NONCE" "$VERDICT"
    ;;

  attest)
    die "attestation is NOT IMPLEMENTED.
  RunEvidence.tdxAttested exists and RunEvidence.verify returns false for it, on
  purpose: a constructor that honestly refuses beats a stub that passes.  The
  pieces needed to close it — in-kernel SHA-256, v4 quote parsing to
  mr_config_id/report_data, P-256 against a pinned key, and an offline gate
  walking the chain to Intel's root — already exist in the gpu_prover
  deployment.  Wiring them in is one case of verify and no new axiom."
    ;;

  *)
    die "unknown mode '$MODE' (expected cache, run or attest)"
    ;;
esac
