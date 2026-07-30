# Freestanding startup stubs

These are the `_start` entry points used to link emitted certificate
artifacts **without libc**.  They exist because a CompCert-produced
object for an emitted artifact has *zero* undefined symbols: everything
the artifact needs is in the artifact.  The only reason the old
`ccomp -o art art.c` binaries pulled in `abort@GLIBC_2.17` and
`__libc_start_main@GLIBC_2.34` was gcc's default startup glue
(`crt1.o`/`crti.o`/`crtbegin.o`), which the artifact never calls.

## Contract

An artifact linked against one of these stubs must satisfy:

* it defines `main` with **no parameters**;
* `main` returns `uint64_t` (or `int`) — the emitters all produce
  `return <computed> == <certified> ? 0 : 1;`;
* the **process exit status is the low 8 bits of that return value**,
  delivered straight to the kernel with no libc in between;
* there is **no libc**: no `atexit`/`__cxa_atexit` handlers run, no
  `stdio` buffers are flushed, no destructors run, no dynamic loader is
  involved, no `.init_array`/`.fini_array` is executed;
* consequently the artifact must not print anything, must not call any
  library function, and must communicate its result *only* through
  `main`'s return value.

The exit-status convention the rest of the pipeline relies on:

| status | meaning |
| --- | --- |
| `0` | computed value **equals** the certified constant |
| `1` | computed value **differs** from the certified constant |
| anything else | **abnormal termination** — never a disagreement |

In particular `128 + N` means the process died on signal `N`
(`134` = `SIGABRT`, `137` = `SIGKILL`, typically the OOM killer,
`139` = `SIGSEGV`).  `LeanCompCert/NativeCheck.lean` classifies those
separately and loudly; both classes still fail the check.

## Files

* `aarch64.S` — AArch64/Linux.  **Assembled and executed** on the
  development host (GNU as + GNU ld, CompCert 3.17).  Uses
  `x8 = 93 = __NR_exit`.
* `x86_64.S` — x86-64/Linux SysV.  **UNASSEMBLED and UNTESTED**: the
  development host is aarch64.  Uses `%eax = 231 = __NR_exit_group`.

The two stubs deliberately use different exit syscalls.  `aarch64.S`
keeps `__NR_exit` because that is the exact instruction sequence that was
hand-verified end to end here (`__NR_exit_group = 94` was also measured
and behaves identically for these single-threaded artifacts).
`x86_64.S` uses `__NR_exit_group` because it could not be tested on this
box and `exit_group` is the unconditionally correct choice — it is what
libc's `_exit(2)` issues, and it stays correct if an artifact ever gains
a second thread.

## Building an artifact

```sh
ccomp -c -o art.o art.c                  # no -I flags are needed
as    -o start.o runtime/start/aarch64.S # or x86_64.S
ld    -o art start.o art.o
./art; echo $?
```

`bench/freestanding.sh` packages exactly this as a shell function, and
`lean-compcert check-native` does the same three steps from Lean.  Note
that `gcc` is *not* in this path at all: `as` assembles the stub
directly.  `ccomp -nostdlib -o art start.o art.o` also works but is
strictly worse — it re-enters gcc as a linker driver and produced a
larger binary (1920 B vs 1464 B for the same artifact).

## Verifying a new port of these stubs

Two checks, both run on the aarch64 stub before it was checked in:

```sh
printf 'int main(void){return 7;}\n' > ret7.c
ccomp -c -o ret7.o ret7.c && as -o start.o runtime/start/<arch>.S
ld -o ret7 start.o ret7.o && ./ret7; echo $?     # must print 7

printf 'int main(void){volatile int*p=0;*p=1;return 0;}\n' > seg.c
ccomp -c -o seg.o seg.c
ld -o seg start.o seg.o && ./seg; echo $?        # must print 139, not 0
```

The first proves the stub propagates `main`'s return value; the second
proves a crash is still visible as a signal death rather than being
silently swallowed into a "clean" exit 0.
