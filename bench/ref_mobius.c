#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  long L = atol(argv[1]);
  signed char *mu = malloc(L);
  uint64_t *rem = malloc(8L * L);
  for (long i = 0; i < L; i++) { mu[i] = 1; rem[i] = (uint64_t)i; }
  for (long p = 2; p < L; p++) {
    if (rem[p] == (uint64_t)p) {
      for (long j = p; j < L; j += p) { mu[j] = -mu[j]; rem[j] /= (uint64_t)p; }
      uint64_t pp = (uint64_t)p * (uint64_t)p;
      if (pp < (uint64_t)L) for (long j = (long)pp; j < L; j += (long)pp) mu[j] = 0;
    }
  }
  long s = 0;
  for (long i = 1; i < L; i++) { if (rem[i] > 1) mu[i] = -mu[i]; s += mu[i]; }
  printf("%ld\n", L + s);
  return 0;
}
