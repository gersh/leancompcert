#!/bin/sh
set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
corpus="$project_root/.lake/build/prominent-projects"
lean_prefix=$(lean --print-prefix)

ensure_checkout() {
  name=$1
  repository=$2
  revision=$3
  directory="$corpus/$name"

  if [ -d "$directory/.git" ]; then
    actual=$(git -C "$directory" rev-parse HEAD)
    if [ "$actual" != "$revision" ]; then
      echo "$name is at $actual, expected $revision" >&2
      exit 1
    fi
    return
  fi

  mkdir -p "$directory"
  git -C "$directory" init
  git -C "$directory" remote add origin "$repository"
  git -C "$directory" fetch --depth 1 origin "$revision"
  git -C "$directory" checkout --detach FETCH_HEAD
}

ensure_checkout mathlib4 \
  https://github.com/leanprover-community/mathlib4.git \
  520045ab14e26149ee970e2e617ca04b09bde5d6
ensure_checkout batteries \
  https://github.com/leanprover-community/batteries.git \
  023ce7d62a0531e22a5331e20b587817a80d49ff
ensure_checkout aesop \
  https://github.com/leanprover-community/aesop.git \
  a7dbf0c63b694e47f425f3dcddbc0e178bb432d3
ensure_checkout doc-gen4 \
  https://github.com/leanprover/doc-gen4.git \
  4df39adbbe5f699a7653f526e0e6faa2d34d404e

cd "$project_root"
lake build LeanCompCert LeanCompCert.Testing.VerifiedDecide
lake env lean compatibility/native-decide/TacticSyntax.lean
lake env lean compatibility/native-decide/LeanLakeInterop.lean
lean compatibility/native-decide/LeanLspInterop.lean

patch --dry-run -p1 \
  < "$project_root/compatibility/native-decide/lean-4.32.1-no-native-decide.patch" \
  -d "$lean_prefix"

mathlib="$corpus/mathlib4"

leancompcert_path="$project_root/.lake/build/lib/lean"
(
  cd "$mathlib"
  LEAN_PATH="$leancompcert_path:${LEAN_PATH-}" lake env lean \
    "$project_root/compatibility/native-decide/MathlibInterop.lean"
  lake build
)

opaque_log="$project_root/.lake/build/native-decide-mathlib-opaque.log"
if (
  cd "$mathlib"
  LEAN_PATH="$leancompcert_path:${LEAN_PATH-}" lake env lean \
    "$project_root/compatibility/native-decide/MathlibOpaque.expected-failure.lean"
) >"$opaque_log" 2>&1; then
  echo "opaque mathlib computation unexpectedly became kernel-reducible" >&2
  exit 1
fi
if ! grep -q "Std.Format" "$opaque_log"; then
  echo "mathlib failure changed; inspect $opaque_log" >&2
  exit 1
fi

for package in batteries aesop doc-gen4; do
  package_dir="$corpus/$package"
  (
    cd "$package_dir"
    lake build
  )
done

echo "native_decide compatibility matrix passed"
