#!/usr/bin/env python3
"""Independent replay of the Helfgott--Platt ladder producer's stream.

Two jobs, both in plain Python integer arithmetic, sharing nothing with the
reference C++ or with Lean:

  parse   read the producer's binary stream, print the header, and write the
          inter-rung delta list that `bench/TGLadderEmit.lean` consumes.
  sieve   count the survivors of a window of the progression k*2^n+1 against
          the odd primes below 16000 -- the ground truth the emitted sieve
          artifact is compared against.

Usage:
  tg_replay.py parse STREAM DELTAS_OUT
  tg_replay.py sieve START COUNT
"""

import json
import sys

SIEVE_BOUND = 16000
PROTH_EXPONENT = 52
MAGIC = b"TGNPLD1\n"


def primes_below(bound):
    sieve = bytearray([1]) * bound
    sieve[0] = sieve[1] = 0
    i = 2
    while i * i < bound:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return [i for i in range(bound) if sieve[i]]


def sieve_table(n=PROTH_EXPONENT, bound=SIEVE_BOUND):
    rows = []
    for p in primes_below(bound):
        if p == 2:
            continue
        rows.append((p, p - pow(pow(2, n, p), -1, p)))
    return rows


def cmd_sieve(start, count):
    rows = sieve_table()
    survivors = 0
    for k in range(start, start + count):
        if k == 0:
            continue
        if all(k % p != r for p, r in rows):
            survivors += 1
    print(json.dumps({"start": start, "count": count, "survivors": survivors}))


def cmd_parse(stream_path, deltas_path):
    data = open(stream_path, "rb").read()
    assert data[:8] == MAGIC, "bad magic"
    header_len = int.from_bytes(data[8:16], "little")
    header = json.loads(data[16 : 16 + header_len].decode())
    body = data[16 + header_len :]

    deltas = []
    witnesses = []
    pos = 0
    while pos < len(body):
        value = 0
        shift = 0
        while True:
            byte = body[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            if byte < 0x80:
                break
            shift += 7
        deltas.append(value)
        witnesses.append(body[pos])
        pos += 1

    assert len(deltas) == header["record_count"], "record count mismatch"
    n = header["proth_exponent"]
    step = int(header["coverage_step"])
    anchor = int(header["anchor_number"])
    target = int(header["target_number"])

    ks = []
    running = 0
    for d in deltas:
        running += d
        ks.append(running)

    # Independently re-derive the ladder property the Lean checker proves.
    numbers = [k * 2**n + 1 for k in ks]
    assert anchor < numbers[0] <= anchor + step, "first rung out of reach"
    for a, b in zip(numbers, numbers[1:]):
        assert a < b <= a + step, "gap violation"
    assert target <= numbers[-1] + step, "target not reached"

    bound = step // 2**n
    inter = deltas[1:]
    assert all(1 <= d <= bound for d in inter), "delta out of range"

    open(deltas_path, "w").write("".join("%d\n" % d for d in inter))
    print(
        json.dumps(
            {
                "records": len(deltas),
                "proth_exponent": n,
                "coverage_step": str(step),
                "delta_bound": bound,
                "k0": ks[0],
                "final_k": ks[-1],
                "inter_records": len(inter),
                "inter_sum": sum(inter),
                "max_delta": max(inter) if inter else 0,
                "witnesses_used": sorted(set(witnesses)),
            }
        )
    )


if __name__ == "__main__":
    if sys.argv[1] == "sieve":
        cmd_sieve(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == "parse":
        cmd_parse(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit(__doc__)
