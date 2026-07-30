# Building enclave-runnable artifacts (x86_64) from an aarch64 host

**Problem.** Intel TDX is x86_64 only. The `ccomp` installed at
`/usr/local/bin/ccomp` is configured `arch=aarch64` and emits aarch64. CompCert
has **no `-target` flag** — the architecture is fixed at *configure* time and
baked into `compcert.ini`. An earlier note calling this a hard blocker was
wrong: `x86_64-linux` is a first-class CompCert target (`configure` line 54).

## Building the x86_64 compiler

Prerequisites were already present: Coq 8.18.0, OCaml 4.14.1, menhir 20231231.

    cp -a ~/CompCert-3.17/. ~/compcert-x86_64/     # keep the aarch64 build intact
    cd ~/compcert-x86_64 && make distclean
    eval $(opam env --switch=4.14.2)               # REQUIRED, see below
    ./configure x86_64-linux
    make -j6

**The opam env line is not optional.** Without it `configure` aborts with
"cannot determine the location of the Menhir API library": bare
`menhir --suggest-menhirLib` returns `/usr/lib/ocaml/menhirLib`, which does not
exist here. The working path is `/home/gersh/.opam/4.14.2/lib/menhirLib`, which
is what the aarch64 build used (`MENHIR_DIR` in its `Makefile.config`).
Note `-use-external-MenhirLib` is a *different* flag and is not what you want —
the bundled MenhirLib is used, only its location must be discoverable.

## Assembling and linking: use Docker, not a cross-toolchain

`compcert.ini` delegates preprocessing, assembly and linking to `gcc`. This host
has **no** x86_64 cross-toolchain (`x86_64-linux-gnu-{gcc,as,ld}` all absent),
the system `ld` supports only aarch64 emulations, and installing
`gcc-x86-64-linux-gnu` needs sudo we do not have.

Do this instead:

1. `ccomp -S` on the host to emit **x86_64 assembly** — this is the step
   CompCert's semantic-preservation proof actually covers;
2. assemble and link inside the `linux/amd64` Docker build, which already works
   here through emulation (`docker buildx ls` shows `linux/amd64`), and which is
   how the campaign image is built anyway.

This costs nothing in trust: the assembler and linker are outside CompCert's
theorem either way, so moving them into the image build changes nothing about
what is proved, and it avoids a system-level install.

## Freestanding artifacts

Emit with no libc. The CompCert object has **zero** undefined symbols; the only
glibc references (`__libc_start_main`, `abort`) come from gcc's default startup
glue. Measured on aarch64: default build 70,504 bytes dynamic vs **1,328 bytes
static** freestanding, both exit 0.

The x86_64 `_start` counterpart of the aarch64 stub:

    .global _start
    _start:
        call main
        mov  %eax, %edi
        mov  $60, %eax      /* __NR_exit */
        syscall

Five instructions, outside CompCert's theorem but auditable at a glance. See
`Ports/` for the aarch64 stub already checked in.
