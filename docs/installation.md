# Installation

Three things to get in place: a CompCert `ccomp` binary, this package, and a
`require` line in your Lean project. CompCert is the only one that is any work,
because it must be built from source.

## 1. CompCert

`ccomp` is not packaged by most distributions and there are no official
binaries, so plan on building it. This package is tested against **CompCert
3.17**.

### Prerequisites

CompCert is written in Coq and OCaml. You need a matching set:

| tool | version used here |
| --- | --- |
| Coq | 8.18.0 |
| OCaml | 4.14.1 / 4.14.2 |
| Menhir | 20231231 |

The easiest route is opam:

```console
opam switch create 4.14.2 ocaml-base-compiler.4.14.2
eval $(opam env --switch=4.14.2)
opam install coq.8.18.0 menhir
```

### Build and install

```console
curl -LO https://compcert.org/release/compcert-3.17.tgz
tar xf compcert-3.17.tgz && cd CompCert-3.17
./configure aarch64-linux        # or x86_64-linux, see below
make -j"$(nproc)"
sudo make install                # installs ccomp and compcert.ini
```

`./configure -help` lists the targets. Common ones are `x86_64-linux`,
`aarch64-linux`, `arm-linux`, `rv64-linux`, `ppc-linux`.

### Two things that will cost you an afternoon

**CompCert has no `-target` flag.** The architecture is fixed at *configure*
time and baked into `compcert.ini`. To emit for a second architecture you build
a second CompCert into a separate tree — do not `make distclean` over a working
install you still need:

```console
cp -a CompCert-3.17 compcert-x86_64
cd compcert-x86_64 && make distclean
eval $(opam env --switch=4.14.2)
./configure x86_64-linux && make -j"$(nproc)"
```

**`configure` may not find MenhirLib even when Menhir is installed.** It asks
`menhir --suggest-menhirLib`, and a bare shell can get an answer like
`/usr/lib/ocaml/menhirLib` that does not exist, at which point configure aborts
with *"cannot determine the location of the Menhir API library"*. The fix is to
run `eval $(opam env --switch=<your switch>)` first so the opam path
(`~/.opam/4.14.2/lib/menhirLib`) is what gets suggested. Note that
`-use-external-MenhirLib` is a **different** flag and is not the fix — the
bundled MenhirLib is the one you want, it just has to be locatable.

### Verify the install

```console
$ ccomp -version
The CompCert C verified compiler, version 3.17

$ grep -E '^arch|^abi' /usr/local/share/compcert.ini
arch=aarch64
abi=standard
```

**Watch the `arch` value.** For a `x86_64-linux` build the field reads
`arch=x86`, **not** `x86_64`:

```
$ grep -E '^arch|^prepro_options' compcert-x86_64/compcert.ini
prepro_options=-m64 -U__GNUC__ -U__SIZEOF_INT128__ -E
arch=x86
```

Any tooling that string-matches `arch` against `x86_64` will reject a perfectly
good 64-bit install — a mistake already made once downstream of this package.
The 32/64 distinction lives in `-m64`, not in `arch`, so check for `arch=x86`
together with `-m64` in `prepro_options`.

### What CompCert does and does not do itself

`compcert.ini` delegates preprocessing, assembly, and linking to `gcc`:

```
prepro=gcc
asm=gcc
linker=gcc
```

Only the C-to-assembly step is covered by CompCert's semantic-preservation
proof. The assembler and linker are outside the theorem — see
[the trust chain](tutorial-4-trust-chain.md).

This matters when cross-compiling. `ccomp -S` on the host emits assembly for
the configured target — that *is* the proved step — but assembling and linking
needs a toolchain for that architecture. If you do not have a cross-toolchain,
run those two steps inside a container for the target platform; it costs
nothing in trust, because they were never inside the theorem. See
[x86_64 enclave toolchain](../compatibility/x86_64-enclave-toolchain.md).

## 2. This package

```console
git clone https://github.com/gersh/leancompcert.git
cd leancompcert
lake build
```

You also need **Python 3.11+** for the driver. Either use it from the checkout:

```console
./bin/lean-compcert doctor
```

or install it into a virtualenv:

```console
python3 -m venv .venv
.venv/bin/pip install -e .
lean-compcert doctor
```

`doctor` is the fastest way to confirm the pieces line up. A healthy report
looks like this:

```console
$ ./bin/lean-compcert doctor
lean-compcert 0.2.0
lean: /home/you/.elan/bin/lean (Lean (version 4.32.1, aarch64-unknown-linux-gnu, ...))
lake: /home/you/.elan/bin/lake (Lake version 5.0.0-src+f054605 (Lean version 4.32.1))
ccomp: /usr/local/bin/ccomp (The CompCert C verified compiler, version 3.17)
python3: /usr/bin/python3 (Python 3.12.3)
```

If `ccomp` is missing from that list, the rest of this package will not do
anything useful — go back to step 1.

## 3. Adding it to your Lean project

The package targets Lean **4.32.1** and builds unchanged under 4.32.0.

Pin it by revision in `lakefile.toml` — this is the recommended form, because
an artifact's trust story should not move under you:

```toml
[[require]]
name = "leancompcert"
git = "https://github.com/gersh/leancompcert.git"
rev = "f28d73c"          # pin a commit, not a branch
```

If you consume Mathlib as well, keep `mathlib` **last** in the require list so
its transitive dependency set (`aesop`, `batteries`, `Qq`) stays authoritative
across path packages.

For local development against a checkout:

```toml
[[require]]
name = "leancompcert"
path = "../leancompcert"
```

A complete worked consumer — library, executable, toolchain pin, and the
five-line `check-native` wiring — is in
[`examples/consumer/`](../examples/consumer/).

Then import what you need:

```lean
import LeanCompCert                    -- everything
import LeanCompCert.Verified.LogFixed  -- or just one primitive
```

## 4. Wiring the cross-check

Registering a certificate with `check-native` makes the build compile its
generated C with `ccomp` and run the self-checking binary:

```console
lake exe lean-compcert check-native
```

It is content-hash cached, so a second run reports `[cached]`. **Pass
`--force` when you want real timings or a genuine re-verification** — a cached
pass is not evidence that anything ran.

Note what this is and is not. The compiled binary is a *cross-check*: its exit
status is never admitted as a theorem. The certificate's own proof stands on
the kernel, and `#print axioms` should show the base trio and nothing else. See
[use case 1](use-case-1-verified-native-decide.md).

## 5. Freestanding artifacts

Artifacts can be emitted with no libc at all. The CompCert object has **zero**
undefined symbols; the only glibc references in a default build
(`__libc_start_main`, `abort`) come from gcc's startup glue. Measured on
aarch64: 70,504 bytes dynamic by default versus **1,328 bytes static**
freestanding, both exiting 0.

Entry stubs for both architectures are checked in under `runtime/start/`. They
are five instructions each — outside CompCert's theorem, but auditable at a
glance.

## Troubleshooting

**`configure` cannot find the Menhir API library** — see above; run
`eval $(opam env --switch=<switch>)` first.

**Tooling rejects a working x86_64 install** — `compcert.ini` says `arch=x86`,
not `x86_64`.

**`ccomp` stack-overflows on generated C** — you are almost certainly emitting
a large table as literal initializers. 27,421 entries became 82,277 init
statements and 5.3 MB of C: gcc compiled it in 22 s, `ccomp` overflowed and was
still climbing past 27 GB with an unlimited stack. Generate the table in the
loop instead; see
[choosing a strategy](choosing-a-strategy.md#4-traps).

**A certificate reports `[cached]` and you wanted a real run** — pass `--force`.
