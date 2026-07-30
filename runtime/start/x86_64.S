/*
 * Freestanding process entry point for emitted certificate artifacts
 * (x86-64 / Linux, System V ABI).
 *
 * !!! UNASSEMBLED / UNTESTED on the machine this file was written on
 * !!! (an aarch64 host with no x86-64 assembler or emulator available).
 * !!! The aarch64 sibling stub is the one that has actually been run.
 * !!! Assemble and run the `return 7` / deliberate-SIGSEGV checks from
 * !!! runtime/start/README.md before trusting this on the enclave.
 *
 * Contract (see runtime/start/README.md):
 *   - the artifact provides `main` with no parameters;
 *   - `main` returns uint64_t (or int); the process exit status is the
 *     low 8 bits of that return value;
 *   - there is no libc, no atexit, no stdio, no dynamic loader.
 *
 * ABI notes:
 *   - On entry the kernel guarantees %rsp is 16-byte aligned and that
 *     argc sits at (%rsp), argv at 8(%rsp).  The emitted `main` takes no
 *     arguments, so argc/argv are simply ignored.
 *   - SysV requires %rsp + 8 to be a multiple of 16 at a function's entry
 *     point, i.e. %rsp must be 16-aligned immediately *before* the call.
 *     It is, so a bare `call main` is correct; no extra `sub $8, %rsp`
 *     padding must be inserted (doing so would in fact misalign main).
 *   - %rbp is zeroed to terminate frame-pointer walks, as glibc's own
 *     _start does.
 *   - `main` returns its value in %rax; for an `int`/`uint64_t` result
 *     the exit status only uses the low 8 bits, so moving %eax is enough.
 *
 * Exit syscall number: 231 = __NR_exit_group (NOT 60 = __NR_exit).
 * Reason: __NR_exit terminates only the calling thread; it happens to end
 * the process for a single-threaded artifact, but __NR_exit_group is what
 * libc's _exit(2) issues and is unconditionally correct even if a future
 * artifact ever spawns a thread.  Since this stub cannot be tested here,
 * the strictly safer of the two numbers was chosen.
 */
    .text
    .globl  _start
    .type   _start, @function
_start:
    xorl    %ebp, %ebp      /* end of the frame-pointer chain */
    call    main            /* main() -> %eax */
    movl    %eax, %edi      /* exit status */
    movl    $231, %eax      /* __NR_exit_group */
    syscall
    hlt                     /* unreachable: fault loudly if exit returns */
    .size   _start, . - _start

    .section .note.GNU-stack,"",@progbits
