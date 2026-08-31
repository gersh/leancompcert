#!/bin/sh
set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_root"

output=${1:-.lake/build/integration/exact-clight}
compcert_coq_dir=${COMPCERT_DIR:-/home/gersh/CompCert-3.17}
if [ ! -x "$compcert_coq_dir/clightgen" ]; then
  echo "CompCert clightgen not found at $compcert_coq_dir/clightgen" >&2
  exit 1
fi

mkdir -p "$output"
lake build LeanCompCert.Verified.ProgramClightEmit \
  LeanCompCert.Verified.ArrayProgramClightEmit

rolled_c="$output/rolled-10m.c"
rolled_source="$output/rolled-10m-source.v"
lake env lean --run bench/RolledFixedPointExactEmit.lean \
  "$rolled_c" "$rolled_source"
rm -rf "$output/rolled-check" "$output/rolled-selftest"
python3 scripts/clight-exact-rolled.py \
  --compcert "$compcert_coq_dir" \
  "$rolled_c" "$rolled_source" "$output/rolled-check"
python3 scripts/clight-exact-rolled.py \
  --compcert "$compcert_coq_dir" \
  --self-test "$output/rolled-selftest"

array_c="$output/array.c"
array_source="$output/array-source.v"
array_cache="$output/array-proof-cache"
lake env lean --run bench/ArrayExactEmit.lean "$array_c" "$array_source"
rm -rf "$output/array-check" "$output/array-mutant-check"
python3 scripts/clight-exact-array.py \
  --compcert "$compcert_coq_dir" --proof-cache "$array_cache" \
  "$array_c" "$array_source" "$output/array-check"
array_mutant="$output/array-mutant.c"
sed 's/(v_3 + v_1)/(v_3 - v_1)/' "$array_c" > "$array_mutant"
if python3 scripts/clight-exact-array.py \
    --compcert "$compcert_coq_dir" --proof-cache "$array_cache" \
    "$array_mutant" "$array_source" "$output/array-mutant-check"; then
  echo "array exact checker accepted a mutated operator" >&2
  exit 1
fi

for r2_shard in first second; do
  r2_c="$output/r2-dense-$r2_shard.c"
  r2_source="$output/r2-dense-$r2_shard-source.v"
  r2_check="$output/r2-dense-$r2_shard-check"
  lake env lean --run bench/R2DenseHeadExactEmit.lean \
    "$r2_shard" "$r2_c" "$r2_source"
  rm -rf "$r2_check"
  python3 scripts/clight-exact-array.py \
    --compcert "$compcert_coq_dir" --proof-cache "$array_cache" \
    "$r2_c" "$r2_source" "$r2_check"
done

echo "exact rolled scalar, array, and production R2 Clight gates: PASS"
