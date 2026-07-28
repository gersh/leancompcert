/*
 * CompCert-facing subset of <stdatomic.h> used by Lean's public lean.h.
 *
 * This header preserves the ABI layout of _Atomic-qualified fields but routes
 * the only operation used by lean.h to an external adapter.  The adapter is
 * compiled by the host C compiler, so it remains outside CompCert's verified
 * compilation boundary.  It must not be used by the strict runtime profile.
 */
#ifndef LEAN_COMPCERT_STDATOMIC_H
#define LEAN_COMPCERT_STDATOMIC_H

#define _Atomic(type) type

typedef enum {
    memory_order_relaxed = 0,
    memory_order_consume = 1,
    memory_order_acquire = 2,
    memory_order_release = 3,
    memory_order_acq_rel = 4,
    memory_order_seq_cst = 5
} memory_order;

extern int lean_compcert_atomic_fetch_sub_int(
    volatile int * object,
    int operand);

static inline int atomic_fetch_sub_explicit(
    volatile int * object,
    int operand,
    memory_order order) {
    (void)order;
    return lean_compcert_atomic_fetch_sub_int(object, operand);
}

#endif
