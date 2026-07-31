#!/usr/bin/env python3
"""Turn the CDEM Abel scan's twelve result cells into the two inequalities the
reduction actually asserts, and say whether they hold.

    bench/abel_check.py runs/abel_prod_cc.out [runs/abel_prod_gcc.out ...]

The artifact's output register is the number of failed *guards* (the mark
cursor, the bisection bracket, the incremental `⌊√k⌋`, `a ≤ 2³¹`); it does not
test the inequalities.  Those are

    uPos ≤ uNeg + 324880457633740
    v    ≤ 48710223109607260068028

with `W = 10¹⁸`, `K = 199330`, `N = 5·10⁹`, matching
`MathExtras/NumberTheory/Analysis/CohenDressElMarrakiReproducibleSourceDefs.lean`
(`ReproducibleTableAbelVerifierOutput`), whose two fields are
`reproducibleVerifierUIncrement ≤ 324880457633740/10¹⁸` and
`reproducibleVerifierVIncrement ≤ 48710223109607260068028/10¹⁸`.

Slots: 0/1 uPos lo/hi, 2/3 uNeg lo/hi, 4/5 v lo/hi, 6 tv, 7 F (wrapped u64),
8 G, 9 ⌊√N⌋, 10 divisor cursor, 11 violations.
"""

import json
import re
import sys

U_TARGET = 324880457633740
V_TARGET = 48710223109607260068028
M64 = 1 << 64


def read(path):
    txt = open(path).read()
    viol = re.search(r"^violations (\d+)", txt, re.M)
    s = {int(a): int(b) for a, b in re.findall(r"^slot(\d+) (\d+)", txt, re.M)}
    if viol is None or len(s) < 12:
        raise SystemExit("%s: incomplete output" % path)
    return int(viol.group(1)), [s[i] for i in range(12)]


def main():
    reports = {}
    for path in sys.argv[1:]:
        viol, s = read(path)
        uPos = s[0] + (s[1] << 64)
        uNeg = s[2] + (s[3] << 64)
        v = s[4] + (s[5] << 64)
        F = s[7] - M64 if s[7] >= (1 << 63) else s[7]
        r = {
            "guard_failures": viol,
            "slot11_viol_cell": s[11],
            "uPos": uPos, "uNeg": uNeg, "v": v,
            "tv": s[6], "F_N": F, "G_N": s[8], "floor_sqrt_N": s[9],
            "divisor_cursor": s[10],
            "uPos_minus_uNeg": uPos - uNeg,
            "u_target": U_TARGET,
            "u_slack": U_TARGET - (uPos - uNeg),
            "u_holds": uPos <= uNeg + U_TARGET,
            "v_target": V_TARGET,
            "v_slack": V_TARGET - v,
            "v_holds": v <= V_TARGET,
        }
        reports[path] = r
        print("== %s" % path)
        for k in ("guard_failures", "uPos", "uNeg", "v", "tv", "F_N", "G_N",
                  "floor_sqrt_N", "divisor_cursor"):
            print("   %-16s %d" % (k, r[k]))
        print("   uPos - uNeg      %d   <=  %d ?  %s   (slack %d)"
              % (r["uPos_minus_uNeg"], U_TARGET, r["u_holds"], r["u_slack"]))
        print("   v                %d   <=  %d ?  %s   (slack %d)"
              % (v, V_TARGET, r["v_holds"], r["v_slack"]))
    if len(reports) > 1:
        vals = [tuple(sorted(r.items())) for r in reports.values()]
        print("cross-source agreement on all cells: %s"
              % all(v == vals[0] for v in vals))
    print(json.dumps(reports, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
