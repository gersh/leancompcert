/* Independent oracle for the Dirichlet ladder record checker.
 *
 *   gcc -O2 -std=c99 -Wall -Wextra -o ref_dirichlet_ladder \
 *       bench/ref_dirichlet_ladder.c
 *   ccomp -O -o ref_dirichlet_ladder_cc bench/ref_dirichlet_ladder.c
 *
 *   ./ref_dirichlet_ladder [--source | --test] [FILE]
 *
 * With no FILE the built-in six-record stream is used.  With a FILE, decimal
 * u64 words are read separated by whitespace and/or commas.  Exactly one line
 * is printed: the decimal count of failed checks.  Zero means accept.
 *
 * --test  (the default) uses a scaled-down height schedule with small numbers.
 * --source uses Platt's Theorem 7.1 schedule,
 *
 *     T_q = max( 10^8/q , 200 + 7.5e7/q )   for even q,
 *     T_q = max( 10^8/q , 200 + 3.75e7/q )  for odd q,
 *
 * multiplied through by q so that q*T_q stays an exact integer:
 *
 *     q*T_q = max( hFloor , hLin*q + (q odd ? hOdd : hEven) ).
 *
 * The height is DERIVED from these four constants, not read from the record;
 * the record's own tqNum must agree with the derivation.
 *
 * This file was written from the written specification alone.  Nothing in it
 * was copied from, or checked against, the implementation it cross-checks.
 *
 * Every quantity below is uint64_t and every arithmetic operation wraps
 * modulo 2^64.  That is intentional: the artifact wraps, so the oracle must
 * wrap in exactly the same places rather than promoting to a wider type or
 * trapping.  There is no floating point anywhere.
 *
 * Record layout, 12 words per record, record i at words 12*i .. 12*i+11:
 *
 *    0 tag        character identity, q*2^20 + charOrdinal
 *    1 blk        0-based block index within the character
 *    2 lower      running zero count at the block's lower ordinate
 *    3 slots      advertised bracket count in this block
 *    4 upper      advertised running count at the block's upper ordinate
 *    5 bits       64 sign samples, bit j = sign of sample j
 *    6 stat       resolved stationary (double-zero) cells
 *    7 isLast     1 on a character's final block, else 0
 *    8 uElem      scaled+biased Turing numerator group
 *    9 henc       scaled Turing window width
 *   10 tqNum      q * T_q, an exact integer
 *   11 conjFirst  record index of the conjugate character's first block
 *   12 digest     running digest of every bitmap in the stream, through here
 *
 * The digest chains as  digest = prevDigest*2654435761 + bits, wrapping mod
 * 2^64, as ONE chain over the whole stream - it does not reset at a character
 * boundary - and the epilogue pins the final value against termDigest.
 *
 * It does not make any bit true: a producer who forges a bitmap forges the
 * digest with it.  What it does is pin the accepted object down to one
 * specific bitmap sequence rather than an equivalence class of bitmaps with
 * the same transition count, so an independent replay has something exact to
 * disagree with, and it makes that pinning uniform in position - a change at
 * any record forces every later digest to be rewritten, and the last record,
 * which has no successor, is pinned from outside by termDigest instead.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define RECW      13
#define MAXSTAT   4
#define WINW      2

static const uint64_t MASK63 = 0x7FFFFFFFFFFFFFFFULL; /* 2^63 - 1 */
static const uint64_t HEXP   = 10485760ULL;
static const uint64_t USCALE = 81920ULL;
static const uint64_t DMUL   = 2654435761ULL;  /* bitmap digest chain */

/* The height schedule baked into a checker instance. */
static const uint64_t SRC_TERM  = 4027133456908973396ULL;
static const uint64_t TST_TERM  = 7745614187404094850ULL;

static const uint64_t SRC_FLOOR = 100000000ULL;
static const uint64_t SRC_LIN   = 200ULL;
static const uint64_t SRC_EVEN  = 75000000ULL;
static const uint64_t SRC_ODD   = 37500000ULL;

static const uint64_t TST_FLOOR = 1ULL;
static const uint64_t TST_LIN   = 10ULL;
static const uint64_t TST_EVEN  = 0ULL;
static const uint64_t TST_ODD   = 10ULL;

/* 78 words = 6 records of 13.  This stream must score 0 under --test. */
static const uint64_t builtin_stream[78] = {
    3145729ULL, 0ULL, 0ULL, 3ULL, 3ULL, 5ULL, 0ULL, 0ULL,
        0ULL, 0ULL, 40ULL, 3ULL, 5ULL,
    3145729ULL, 1ULL, 3ULL, 2ULL, 5ULL, 3ULL, 0ULL, 0ULL,
        0ULL, 0ULL, 40ULL, 3ULL, 13272178808ULL,
    3145729ULL, 2ULL, 5ULL, 2ULL, 7ULL, 1ULL, 0ULL, 1ULL,
        120012800ULL, 10485760ULL, 40ULL, 3ULL, 16783401980632001273ULL,
    5242881ULL, 0ULL, 0ULL, 3ULL, 3ULL, 5ULL, 0ULL, 0ULL,
        0ULL, 0ULL, 60ULL, 0ULL, 7994887169443407662ULL,
    5242881ULL, 1ULL, 3ULL, 2ULL, 5ULL, 3ULL, 0ULL, 0ULL,
        0ULL, 0ULL, 60ULL, 0ULL, 4762022776277718225ULL,
    5242881ULL, 2ULL, 5ULL, 2ULL, 7ULL, 1ULL, 0ULL, 1ULL,
        120012800ULL, 10485760ULL, 60ULL, 0ULL, 7745614187404094850ULL
};

/* Population count and set-index sum over bit positions 0..62, written out by
 * hand rather than delegated to a compiler builtin: ccomp has no popcount
 * intrinsic, and a shared intrinsic would be a shared assumption. */
static uint64_t transition_stats(uint64_t t, uint64_t *sj_out)
{
    uint64_t k;
    uint64_t cnt = 0;
    uint64_t sj = 0;
    for (k = 0; k < 63; k++) {
        if ((t >> k) & 1ULL) {
            cnt = cnt + 1ULL;
            sj = sj + k;
        }
    }
    *sj_out = sj;
    return cnt;
}

/* The whole checker: one streaming pass over n = nw/RECW records. */
static uint64_t run_checker(const uint64_t *w, uint64_t nw,
                            uint64_t hFloor, uint64_t hLin,
                            uint64_t hEven, uint64_t hOdd,
                            uint64_t termDigest)
{
    uint64_t n = nw / (uint64_t)RECW;
    uint64_t i;

    uint64_t viol = 0;
    uint64_t prevTag = 0;
    uint64_t prevBlk = 0;
    uint64_t prevUpper = 0;
    uint64_t prevBit = 0;
    uint64_t stFirstBit = 0;   /* first sample bit of the current character */
    uint64_t trI0 = 0, sj0 = 0;
    uint64_t trI1 = 0, sj1 = 0;
    uint64_t prevLast = 1;
    uint64_t prevConj = 0;
    uint64_t prevDigest = 0;

    for (i = 0; i < n; i++) {
        const uint64_t *r = w + RECW * i;

        uint64_t tag       = r[0];
        uint64_t blk       = r[1];
        uint64_t lower     = r[2];
        uint64_t slots     = r[3];
        uint64_t upper     = r[4];
        uint64_t bits      = r[5];
        uint64_t stat      = r[6];
        uint64_t isLast    = r[7];
        uint64_t uElem     = r[8];
        uint64_t henc      = r[9];
        uint64_t tqNum     = r[10];
        uint64_t conjFirst = r[11];
        uint64_t digest    = r[12];

        uint64_t t = (bits ^ (bits >> 1)) & MASK63;
        uint64_t sj = 0;
        uint64_t trI = transition_stats(t, &sj);

        uint64_t recFirstBit = bits & 1ULL;
        uint64_t lastBit = (bits >> 63) & 1ULL;

        uint64_t same = (tag == prevTag) ? 1ULL : 0ULL;
        uint64_t newch = same ? 0ULL : 1ULL;
        uint64_t isLastB = (isLast == 1ULL) ? 1ULL : 0ULL;
        uint64_t cross = (same && (prevBit != recFirstBit)) ? 1ULL : 0ULL;
        uint64_t derived = trI + cross + 2ULL * stat;
        uint64_t q = tag >> 20;

        /* Derived source height: tq = max(hFloor, hLin*q + cq). */
        uint64_t qOdd = q & 1ULL;
        uint64_t cq = qOdd ? hOdd : hEven;
        uint64_t alt = hLin * q + cq;
        uint64_t tq = (alt >= hFloor) ? alt : hFloor;

        uint64_t stair = 127ULL * trI0 + 63ULL * trI + 64ULL * cross;
        uint64_t stairSub = sj0 + sj;
        uint64_t stairOk = (stairSub <= stair) ? 1ULL : 0ULL;
        uint64_t stairW = stairOk ? (stair - stairSub) : 0ULL;
        uint64_t stairScaled = stairW * USCALE;
        uint64_t uOk = (stairScaled <= uElem) ? 1ULL : 0ULL;
        uint64_t uEnc = uOk ? (uElem - stairScaled) : 0ULL;

        uint64_t addr = (uint64_t)RECW * conjFirst + 11ULL;
        uint64_t inRange = (addr < (uint64_t)RECW * n) ? 1ULL : 0ULL;

        uint64_t upperEven = ((upper & 1ULL) == 0ULL) ? 1ULL : 0ULL;
        uint64_t bitMatch = (stFirstBit == lastBit) ? 1ULL : 0ULL;

        /*  1 */ if (tag < prevTag) viol++;
        /*  2 */ if (newch && prevLast != 1ULL) viol++;
        /*  3 */ if (same && prevLast == 1ULL) viol++;
        /*  4 */ if (blk != (same ? prevBlk + 1ULL : 0ULL)) viol++;
        /*  5 */ if (lower != (same ? prevUpper : 0ULL)) viol++;
        /*  6 */ if (upper != lower + slots) viol++;
        /*  7 */ if (isLast > 1ULL) viol++;
        /*  8 */ if (stat > (uint64_t)MAXSTAT) viol++;
        /*  9 */ if (slots != derived) viol++;
        /* 10 */ if (isLastB && blk < (uint64_t)(WINW - 1)) viol++;
        /* 11 */ if (isLastB && henc != HEXP) viol++;
        /* 12 */ if (isLastB && !stairOk) viol++;
        /* 13 */ if (isLastB && !uOk) viol++;
        /* 14 */ if (isLastB && !(uEnc < (upper + 1ULL) * henc)) viol++;
        /* 15 */ if (isLastB && (bitMatch != upperEven)) viol++;
        /* 16 */ if (tqNum != tq) viol++;   /* every record, not just the last */
        /* 17 */ if (isLastB && 5ULL * (blk + 1ULL) * q < tq) viol++;
        /* 18 */ if (isLastB && tq <= 5ULL * blk * q) viol++;
        /* 19 */ if (newch && !inRange) viol++;
        /* 20 */ if (newch && inRange && w[addr] != i) viol++;
        /* 21 */ if (same && conjFirst != prevConj) viol++;
        /* 22 */ if (!isLastB && uElem != 0ULL) viol++;
        /* 23 */ if (!isLastB && henc != 0ULL) viol++;
        /* 24 */ if (isLastB && uEnc < upper * henc) viol++;
        /* 25 */ if (digest != prevDigest * DMUL + bits) viol++;

        prevTag = tag;
        prevBlk = blk;
        prevUpper = upper;
        prevBit = lastBit;
        if (!same) stFirstBit = recFirstBit;
        if (same) {
            trI0 = trI1;
            sj0 = sj1;
        } else {
            trI0 = 0;
            sj0 = 0;
        }
        trI1 = trI;
        sj1 = sj;
        prevLast = isLast;
        prevConj = conjFirst;
        prevDigest = digest;
    }

    if (prevLast != 1ULL) viol++;
    if (prevDigest != termDigest) viol++;

    return viol;
}

/* Decimal u64 words separated by whitespace and/or commas, grown
 * geometrically.  Parsed by hand so that the comma-separated form the source
 * stream uses needs no preprocessing. */
static uint64_t *read_words(const char *path, uint64_t *nw_out)
{
    FILE *f = fopen(path, "r");
    uint64_t cap = 256;
    uint64_t nw = 0;
    uint64_t *w;
    int c;

    if (f == NULL) {
        fprintf(stderr, "ref_dirichlet_ladder: cannot open %s\n", path);
        return NULL;
    }
    w = (uint64_t *)malloc((size_t)cap * sizeof(uint64_t));
    if (w == NULL) {
        fprintf(stderr, "ref_dirichlet_ladder: out of memory\n");
        fclose(f);
        return NULL;
    }
    c = fgetc(f);
    for (;;) {
        uint64_t v;
        while (c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
               c == '\f' || c == '\v' || c == ',')
            c = fgetc(f);
        if (c == EOF) break;
        if (c < '0' || c > '9') {
            fprintf(stderr, "ref_dirichlet_ladder: bad character in %s\n",
                    path);
            free(w);
            fclose(f);
            return NULL;
        }
        v = 0;
        while (c >= '0' && c <= '9') {
            v = v * 10ULL + (uint64_t)(c - '0');
            c = fgetc(f);
        }
        if (nw == cap) {
            uint64_t *w2;
            cap = cap * 2;
            w2 = (uint64_t *)realloc(w, (size_t)cap * sizeof(uint64_t));
            if (w2 == NULL) {
                fprintf(stderr, "ref_dirichlet_ladder: out of memory\n");
                free(w);
                fclose(f);
                return NULL;
            }
            w = w2;
        }
        w[nw] = v;
        nw = nw + 1;
    }
    fclose(f);
    *nw_out = nw;
    return w;
}

static int streq(const char *a, const char *b)
{
    while (*a != '\0' && *a == *b) { a++; b++; }
    return *a == '\0' && *b == '\0';
}

int main(int argc, char **argv)
{
    uint64_t viol;
    uint64_t hFloor = TST_FLOOR, hLin = TST_LIN;
    uint64_t hEven = TST_EVEN, hOdd = TST_ODD;
    uint64_t termDigest = TST_TERM;
    const char *path = NULL;
    int k;

    for (k = 1; k < argc; k++) {
        if (streq(argv[k], "--source")) {
            hFloor = SRC_FLOOR; hLin = SRC_LIN;
            hEven = SRC_EVEN;   hOdd = SRC_ODD;
            termDigest = SRC_TERM;
        } else if (streq(argv[k], "--test")) {
            hFloor = TST_FLOOR; hLin = TST_LIN;
            hEven = TST_EVEN;   hOdd = TST_ODD;
            termDigest = TST_TERM;
        } else if (path == NULL && argv[k][0] != '-') {
            path = argv[k];
        } else {
            fprintf(stderr, "usage: %s [--source | --test] [FILE]\n", argv[0]);
            return 1;
        }
    }

    if (path != NULL) {
        uint64_t nw = 0;
        uint64_t *w = read_words(path, &nw);
        if (w == NULL) return 1;
        viol = run_checker(w, nw, hFloor, hLin, hEven, hOdd, termDigest);
        free(w);
    } else {
        viol = run_checker(builtin_stream, (uint64_t)78,
                           hFloor, hLin, hEven, hOdd, termDigest);
    }
    printf("%llu\n", (unsigned long long)viol);
    return 0;
}
