#!/usr/bin/env bash
# Measurement driver for stage (b) of the Helfgott--Platt Goldbach prime
# ladder: the Proth test, in the proved fragment.
#
#   bench/tg_proth.sh [REFERENCE_CPP]
#
# Reproduces every number in bench/results/tg_proth.md on this box:
#
#   1. correctness -- the emitted artifact's exit status against an
#      independent Python `pow(a,(N-1)//2,N)` replay, over primes,
#      composites and non-witnesses;
#   2. cost -- the emitted artifact (CompCert, freestanding, and gcc -O2)
#      against GMP's `mpz_powm` on the *same* 91-bit modulus and exponent;
#   3. the reference producer's own end-to-end cost, if its source is
#      given.
#
# CPU (user) time throughout: this box is shared.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/bench/results"
WORK="${TMPDIR:-/tmp}/tg_proth.$$"
mkdir -p "$OUT" "$WORK"
cd "$ROOT"
. "$ROOT/bench/freestanding.sh"
FS_WORK="$WORK" fs_init || exit 1

# Proth exponent of the reference producer, and the k-window width that
# covers the ladder to 10^27 (k < 2^39 there).
N_EXP=52
KBITS=39

# --------------------------------------------------------------- (1) correct
# Four real Proth primes near 2^91 with a genuine witness, one composite,
# and two non-witnesses of a prime.  Fields: k a expected_exit
CASES="274877906947 3 0
274877906962 3 0
274877906976 5 0
274877907025 3 0
274877906946 3 1
274877906947 2 1
274877906947 7 1"

printf 'k,a,N,python_pass,ccomp_exit,gcc_exit,verdict\n' > "$OUT/tg_proth_check.csv"
fail=0
while read -r k a want; do
  [ -z "$k" ] && continue
  lake env lean --run bench/TGProthEmit.lean "$N_EXP" "$k" "$a" "$KBITS" 1 \
    "$WORK/c.c" > /dev/null || { echo "emit failed"; exit 1; }
  ccomp -c -o "$WORK/c.o" "$WORK/c.c" > /dev/null 2>&1 &&
    ld -o "$WORK/c.cc" "$FS_START_O" "$WORK/c.o"
  "$WORK/c.cc"; cc_exit=$?
  gcc -O2 -o "$WORK/c.gcc" "$WORK/c.c" && "$WORK/c.gcc"; gcc_exit=$?
  py=$(python3 -c "N=$k*2**$N_EXP+1; print(1 if pow($a,(N-1)//2,N)==N-1 else 0)")
  nval=$(python3 -c "print($k*2**$N_EXP+1)")
  want_py=$(( 1 - want ))
  if [ "$cc_exit" = "$want" ] && [ "$gcc_exit" = "$want" ] && [ "$py" = "$want_py" ]
  then verdict=agree; else verdict=DISAGREE; fail=$((fail+1)); fi
  printf '%s,%s,%s,%s,%s,%s,%s\n' "$k" "$a" "$nval" "$py" "$cc_exit" \
    "$gcc_exit" "$verdict" >> "$OUT/tg_proth_check.csv"
done <<EOF
$CASES
EOF
cat "$OUT/tg_proth_check.csv"
echo "correctness: $fail disagreements"

# ------------------------------------------------------------------ (2) cost
# The certificate artifact runs the loop KBITS+N_EXP-1 times = one Proth
# test.  REPS multiplies the loop count with the *same body*, so the cost
# per test is the total divided by REPS.  Only REPS=1 carries a theorem.
K=274877906947
A=3
REPS=200000

lake env lean --run bench/TGProthEmit.lean "$N_EXP" "$K" "$A" "$KBITS" 1 \
  "$WORK/one.c" > /dev/null
ONE_BYTES=$(stat -c %s "$WORK/one.c")
s=$(date +%s%N); ccomp -c -o "$WORK/one.o" "$WORK/one.c" > /dev/null 2>&1
ld -o "$WORK/one.cc" "$FS_START_O" "$WORK/one.o"; e=$(date +%s%N)
CCOMP_MS=$(( (e-s)/1000000 ))
EXE_BYTES=$(stat -c %s "$WORK/one.cc")
UNDEF=$(nm -D --undefined-only "$WORK/one.cc" 2>/dev/null | wc -l)

lake env lean --run bench/TGProthEmit.lean "$N_EXP" "$K" "$A" "$KBITS" \
  "$REPS" "$WORK/many.c" > /dev/null
ccomp -c -o "$WORK/many.o" "$WORK/many.c" > /dev/null 2>&1
ld -o "$WORK/many.cc" "$FS_START_O" "$WORK/many.o"
gcc -O2 -o "$WORK/many.gcc" "$WORK/many.c"

best() { local b=99999; for i in 1 2 3; do
    t=$(/usr/bin/time -f '%U' "$1" 2>&1 >/dev/null | tail -1)
    b=$(python3 -c "print(min($b,$t))"); done; echo "$b"; }
CC_S=$(best "$WORK/many.cc")
GCC_S=$(best "$WORK/many.gcc")

cat > "$WORK/gmp.c" <<'EOF'
#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
int main(int argc, char **argv) {
  long reps = atol(argv[2]);
  mpz_t N, a, e, r, target;
  mpz_inits(N, a, e, r, target, NULL);
  mpz_set_str(N, argv[1], 10);
  mpz_set_ui(a, atol(argv[3]));
  mpz_sub_ui(e, N, 1); mpz_fdiv_q_2exp(e, e, 1);
  mpz_sub_ui(target, N, 1);
  struct timespec t0, t1; long ok = 0;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t0);
  for (long i = 0; i < reps; i++) { mpz_powm(r, a, e, N);
    ok += (mpz_cmp(r, target) == 0); }
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t1);
  printf("%.6f %ld\n", (t1.tv_sec-t0.tv_sec)+1e-9*(t1.tv_nsec-t0.tv_nsec), ok);
  return 0;
}
EOF
gcc -O2 -o "$WORK/gmp" "$WORK/gmp.c" -lgmp
NVAL=$(python3 -c "print($K*2**$N_EXP+1)")
GMP_S=$("$WORK/gmp" "$NVAL" "$REPS" "$A" | cut -d' ' -f1)

printf 'engine,us_per_proth_test,ratio_vs_gmp\n' > "$OUT/tg_proth.csv"
python3 - "$CC_S" "$GCC_S" "$GMP_S" "$REPS" "$ONE_BYTES" "$EXE_BYTES" \
    "$CCOMP_MS" "$UNDEF" >> "$OUT/tg_proth.csv" <<'PY'
import sys
cc, gc, gmp, reps = (float(x) for x in sys.argv[1:5])
c_bytes, exe_bytes, ccomp_ms, undef = (int(x) for x in sys.argv[5:9])
g = 1e6*gmp/reps
for name, t in (("gmp mpz_powm", gmp), ("this port, gcc -O2", gc),
                ("this port, ccomp", cc)):
    us = 1e6*t/reps
    print("%s,%.3f,%.2f" % (name, us, us/g))
print("# artifact: %d bytes C, %d bytes exe, %d undefined dynamic symbols,"
      " ccomp+ld %d ms" % (c_bytes, exe_bytes, undef, ccomp_ms))
PY
cat "$OUT/tg_proth.csv"

# ------------------------------------------------------------- (3) reference
if [ $# -ge 1 ] && [ -f "$1" ]; then
  DIGEST=$(sha256sum "$1" | cut -d' ' -f1)
  g++ -std=c++20 -O2 \
    -DSPARKINTERVAL_TG_GOLDBACH_NATIVE_SOURCE_SHA256="\"$DIGEST\"" \
    -o "$WORK/ladder" "$1" -lgmp || exit 1
  ANCHOR=4000000000000000000
  target=$(python3 -c "print(4*10**23 + $ANCHOR)")
  "$WORK/ladder" --anchor-number $ANCHOR --target-number "$target" \
    --output "$WORK/stream" | tee "$OUT/tg_proth_reference.json"
fi

rm -rf "$WORK"
