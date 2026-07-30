/*
 * Freestanding process entry point for emitted certificate artifacts
 * (AArch64 / Linux).
 *
 * Contract (see runtime/start/README.md):
 *   - the artifact provides `main` with no parameters;
 *   - `main` returns uint64_t (or int); the process exit status is the
 *     low 8 bits of that return value;
 *   - there is no libc, no atexit, no stdio, no dynamic loader.
 *
 * The kernel enters at `_start` with sp 16-byte aligned and argc at
 * (sp).  `bl main` does not touch sp, so main's entry alignment is the
 * ABI-required one.  main's return value is already in x0, which is
 * exactly where the exit syscall wants the status, so no move is needed.
 *
 * Syscall: x8 = 93 = __NR_exit.  The artifacts are single-threaded, so
 * __NR_exit terminates the whole process.  (__NR_exit_group = 94 is the
 * multi-threaded-correct analogue and was measured to behave identically
 * here; 93 is kept because it is the byte-for-byte hand-verified recipe.)
 *
 * ASSEMBLED AND TESTED on aarch64 Linux with GNU as + GNU ld.
 */
    .text
    .global _start
    .type   _start, %function
_start:
    bl      main            /* main() -> x0 */
    mov     x8, #93         /* __NR_exit */
    svc     #0
    brk     #0              /* unreachable: fault loudly if exit returns */
    .size   _start, . - _start

    .section .note.GNU-stack,"",%progbits
