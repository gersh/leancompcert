/*
 * Hybrid-runtime adapter.  This file is intentionally compiled with the host
 * compiler and is reported as conventionally compiled in probe provenance.
 */
#include <stdatomic.h>

int lean_compcert_atomic_fetch_sub_int(volatile int * object, int operand) {
    return atomic_fetch_sub_explicit(
        (_Atomic int *)object,
        operand,
        memory_order_relaxed);
}
