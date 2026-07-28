#include <stdio.h>
#include <stdlib.h>

void lean_compcert_unreachable(const char * reason) {
    if (reason != NULL) {
        fputs("lean-compcert: unreachable: ", stderr);
        fputs(reason, stderr);
        fputc('\n', stderr);
    }
    abort();
}
