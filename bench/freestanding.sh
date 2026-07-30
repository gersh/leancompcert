#!/usr/bin/env bash
# Shared compile+link helpers for emitted certificate artifacts.
#
# Source this from a bench driver:
#
#     . "$(cd "$(dirname "$0")" && pwd)/freestanding.sh"
#     fs_init || exit 1
#     fs_cc "$WORK/art" "$WORK/art.c"        # freestanding (default arm)
#     fs_gcc "$WORK/art.gcc" "$WORK/art.c"   # hosted gcc comparison arm
#
# The freestanding arm is `ccomp -c` + `as` on runtime/start/<arch>.S +
# `ld`.  A CompCert object for an emitted artifact has zero undefined
# symbols, so no libc and no gcc startup glue is needed; the resulting
# binary is static with zero undefined dynamic symbols.  No `-I` flags
# are needed either: the emitted units include only <stdint.h> and
# <stddef.h>.
#
# ASYMMETRY, on purpose: `fs_gcc` keeps the ordinary hosted link.  The
# gcc arm exists to cross-check CompCert's *arithmetic*, so it is
# deliberately built the conventional way; only the CompCert artifact —
# the one whose provenance we care about — is freestanding.  Sizes and
# `nm -D` counts are therefore not comparable between the two arms.
#
# Exit-status contract of every artifact built here (see
# runtime/start/README.md): 0 = computed value equals the certified
# constant, 1 = it differs, anything else = abnormal termination
# (128 + signal), which is NOT a disagreement.

fs_init() {
  FS_ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
  case "$(uname -m)" in
    aarch64|arm64) FS_ARCH=aarch64 ;;
    x86_64|amd64)  FS_ARCH=x86_64 ;;
    *) echo "freestanding.sh: unsupported architecture $(uname -m)" >&2
       return 1 ;;
  esac
  FS_STUB="$FS_ROOT/runtime/start/$FS_ARCH.S"
  if [ ! -f "$FS_STUB" ]; then
    echo "freestanding.sh: missing startup stub $FS_STUB" >&2
    return 1
  fi
  FS_START_O="${FS_WORK:-${TMPDIR:-/tmp}}/lcc_start.$$.$FS_ARCH.o"
  as -o "$FS_START_O" "$FS_STUB" || {
    echo "freestanding.sh: assembling $FS_STUB failed" >&2
    return 1
  }
  export FS_ROOT FS_ARCH FS_STUB FS_START_O
}

# fs_cc OUT SRC -- freestanding CompCert build; no libc.
fs_cc() {
  local out="$1" src="$2" obj="$1.o"
  ccomp -c -o "$obj" "$src" >/dev/null 2>&1 || return 1
  ld -o "$out" "$FS_START_O" "$obj" >/dev/null 2>&1 || return 1
}

# fs_cc_hosted OUT SRC -- old single-step CompCert link through gcc's
# startup glue.  Kept as an escape hatch / comparison point, matching
# `lean-compcert check-native --hosted`.
fs_cc_hosted() {
  ccomp -o "$1" "$2" >/dev/null 2>&1
}

# fs_gcc OUT SRC -- hosted gcc -O2 cross-check arm (see ASYMMETRY above).
fs_gcc() {
  gcc -O2 -o "$1" "$2" >/dev/null 2>&1
}

fs_cleanup() {
  [ -n "${FS_START_O:-}" ] && rm -f "$FS_START_O"
  return 0
}
