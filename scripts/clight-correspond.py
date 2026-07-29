#!/usr/bin/env python3
"""Structural correspondence checker: certificate C files vs clightgen .v output.

Usage:  clight-correspond.py <cert.c> <cert.v>

The acceptance suite emits certificate C files (via `lean-compcert emit-*-cert-c`)
and runs CompCert's `clightgen -normalize` on them, producing Coq .v files that
contain the formal Clight terms CompCert's proof actually starts from.  This
script strengthens translation validation beyond "clightgen succeeded": for every
emitted `l_*` certificate function it independently parses

  * the C body (the emitter's highly regular output: `uint64_t v_N;` declarations,
    one statement per line, fully parenthesized expressions, `while`/`goto`
    control flow, `return v_N;`), and
  * the Clight body in the .v file (`Definition f_l_* := {| ... fn_body := ... |}`,
    walked by an s-expression parser over `Ssequence`/`Sset`/`Ebinop`/`Swhile`/
    `Sloop`/`Slabel`/`Sgoto`/`Sreturn`/`Etempvar`/`Econst_*`/`Ecast`),

then abstracts both into the same ordered event stream -- (dest, operator,
operand shapes) per assignment, loop/label/goto structure, return operand -- and
demands they be identical (C operators mapped to Clight `Obinop` names, C `v_N`
mapped to Clight `_v_N`, literals compared modulo the operand width).

HONESTY NOTE: this is *structural* translation validation only.  It checks that
the Clight term has the same dataflow shape as the emitted C -- same assignment
count and order, same operators, same destination/operand identifiers and
literals, same loop/label structure, same return variable.  It is NOT a
semantics proof: it does not model evaluation order, integer promotion/implicit
casts (casts are deliberately erased on both sides), overflow, or memory, and it
trusts that matching shape plus CompCert's own proven pipeline gives the intended
meaning.  Known parsing limitations are listed in PARSING LIMITATIONS below.

PARSING LIMITATIONS (documented, acceptable for the emitter's regular output):
  * C parsing is line-oriented and assumes the LeanCompCert emitter's layout:
    one statement per line, braces on their own lines, fully parenthesized
    expressions.  Hand-written or reformatted C is out of scope.
  * Only the certificate fragment is understood: declarations, assignments with
    the binary operators + - * / % & | ^ << >> == != < <= > >= and unary ~ ! -,
    casts, calls, `while`, `if`/`else`, `goto`/labels, `return`.  Anything else
    is reported as a parse error rather than silently skipped.
  * Casts are erased on both sides before comparison (clightgen inserts implicit
    `Ecast`/`Econst_int ... tint` adjustments that have no C-source counterpart),
    so a translation bug that ONLY changed a cast would not be caught.
  * Literals are compared modulo 2^64 (`Econst_long`) / 2^32 (`Econst_int`),
    matching how clightgen prints wrapped signed representations.
  * A bare `Sloop` (rolled loop printed without the `Swhile` notation) is matched
    against a C `while` by structure only; its condition is compared when it
    appears in the `Swhile`/`Sfor` notational forms clightgen actually emits.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field

# C operator symbol -> Clight Ebinop constructor name.
C_TO_CLIGHT_OP = {
    "+": "Oadd", "-": "Osub", "*": "Omul", "/": "Odiv", "%": "Omod",
    "&": "Oand", "|": "Oor", "^": "Oxor", "<<": "Oshl", ">>": "Oshr",
    "==": "Oeq", "!=": "One", "<": "Olt", "<=": "Ole", ">": "Ogt", ">=": "Oge",
}
C_TO_CLIGHT_UNOP = {"~": "Onotint", "!": "Onotbool", "-": "Oneg"}
# Longest-match order for the top-level operator scan.
C_OPS = sorted(C_TO_CLIGHT_OP, key=len, reverse=True)

C_TYPE_RE = re.compile(
    r"(?:uint8_t|uint16_t|uint32_t|uint64_t|int8_t|int16_t|int32_t|int64_t"
    r"|size_t|ptrdiff_t|float|double|void)\s*\**$")


class ParseError(Exception):
    pass


@dataclass
class FuncSummary:
    """One certificate function abstracted to a comparable event stream."""
    name: str
    events: list = field(default_factory=list)  # ordered structural events
    decl_count: int = 0                         # C only; .v uses temp_count
    temp_count: int = 0

    def assignments(self):
        return [e for e in self.events if e[0] == "assign"]

    def count(self, kind):
        return sum(1 for e in self.events if e[0] == kind)


# --------------------------------------------------------------------------
# C side
# --------------------------------------------------------------------------

def c_expr(text):
    """Classify an emitter expression into a normalized descriptor.

    Descriptors: ("var", name) | ("lit", value, width) |
                 ("bin", OpName, lhs, rhs) | ("un", OpName, arg) |
                 ("call", name).  Casts are erased.
    """
    s = text.strip()
    # Strip a fully enclosing parenthesis pair.
    while s.startswith("(") and _match_paren(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    m = re.fullmatch(r"[A-Za-z_]\w*", s)
    if m:
        return ("var", s)
    m = re.fullmatch(r"UINT(8|16|32|64)_C\((\d+)\)|INT(8|16|32|64)_C\((-?\d+)\)", s)
    if m:
        width = 64 if (m.group(1) or m.group(3)) == "64" else 32
        value = int(m.group(2) if m.group(2) is not None else m.group(4))
        return ("lit", value % (1 << width), width)
    m = re.fullmatch(r"-?\d+", s)
    if m:
        return ("lit", int(s) % (1 << 32), 32)
    if s and s[0] in "~!-":
        return ("un", C_TO_CLIGHT_UNOP[s[0]], c_expr(s[1:]))
    m = re.match(r"([A-Za-z_]\w*)\(", s)
    if m and _match_paren(s, m.end() - 1) == len(s) - 1:
        return ("call", m.group(1))
    # Leftmost operand: parenthesized group, or a var/literal token.
    if s.startswith("("):
        close = _match_paren(s, 0)
        group = s[1:close].strip()
        rest = s[close + 1:].strip()
        if C_TYPE_RE.fullmatch(group):        # ((type)(expr)) -- cast: erase
            return c_expr(rest)
        left, tail = s[:close + 1], rest
    else:
        m = re.match(r"UINT\d+_C\(\d+\)|INT\d+_C\(-?\d+\)|[A-Za-z_]\w*|\d+", s)
        if not m:
            raise ParseError(f"unrecognized C expression: {text!r}")
        left, tail = m.group(0), s[m.end():].strip()
    for op in C_OPS:
        if tail.startswith(op):
            return ("bin", C_TO_CLIGHT_OP[op], c_expr(left), c_expr(tail[len(op):]))
    raise ParseError(f"unrecognized C expression: {text!r}")


def _match_paren(s, i):
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    raise ParseError(f"unbalanced parentheses in {s!r}")


def parse_c_functions(text):
    """Extract every emitted `l_*` function body from a certificate C file."""
    funcs = {}
    for m in re.finditer(r"^(?:static\s+)?\w+\s+(l_\w+)\s*\([^)]*\)\s*$",
                         text, re.M):
        name = m.group(1)
        lines = text[m.end():].lstrip("\n").split("\n")
        body, depth, taken = [], 0, 0
        for line in lines:
            taken += 1
            stripped = line.strip()
            depth += stripped.count("{") - stripped.count("}")
            body.append(stripped)
            if depth == 0 and taken > 1:
                break
        summary = FuncSummary(name)
        end = _parse_c_block(body[1:-1], 0, summary)   # drop outer { }
        if end != len(body) - 2:
            raise ParseError(f"trailing unparsed lines in {name}")
        funcs[name] = summary
    return funcs


def _parse_c_block(lines, i, out):
    """Parse statements from lines[i:] until the block's closing '}' (or end
    of input); return the index just past the consumed statements."""
    while i < len(lines):
        line = lines[i].strip()
        i += 1
        if not line or line.startswith("/*"):
            continue
        if line == "}":
            return i - 1
        if line == "{":                       # nested bare block
            i = _parse_c_braced(lines, i - 1, out)
            continue
        m = re.fullmatch(r"(?:\w+\s+)*(v_\d+)(?:\s*=\s*(.*))?;",
                         line) if re.match(r"(?:u?int\d+_t|size_t)\b", line) else None
        if m:                                  # declaration (maybe with init)
            out.decl_count += 1
            if m.group(2):
                out.events.append(("assign", m.group(1), c_expr(m.group(2))))
            continue
        m = re.fullmatch(r"(v_\d+)\s*=\s*(.*);", line)
        if m:
            out.events.append(("assign", m.group(1), c_expr(m.group(2))))
            continue
        m = re.fullmatch(r"while\s*\((.*)\)", line)
        if m:
            out.events.append(("loop", c_expr(m.group(1))))
            i = _parse_c_braced(lines, i, out)
            out.events.append(("endloop",))
            continue
        m = re.fullmatch(r"if\s*\((.*)\)", line)
        if m:
            out.events.append(("if", c_expr(m.group(1))))
            i = _parse_c_braced(lines, i, out)
            out.events.append(("else",))
            if i < len(lines) and lines[i].strip() == "else":
                i = _parse_c_braced(lines, i + 1, out)
            out.events.append(("endif",))
            continue
        m = re.fullmatch(r"goto\s+(\w+);", line)
        if m:
            out.events.append(("goto", m.group(1)))
            continue
        m = re.fullmatch(r"(\w+):", line)
        if m:
            out.events.append(("label", m.group(1)))
            continue
        m = re.fullmatch(r"return\s*(.*?);", line)
        if m:
            out.events.append(("return", c_expr(m.group(1)) if m.group(1) else None))
            continue
        m = re.fullmatch(r"(\w+)\s*\(.*\)\s*;", line)
        if m:
            out.events.append(("call", m.group(1)))
            continue
        raise ParseError(f"unrecognized C statement: {line!r}")
    return i


def _parse_c_braced(lines, i, out):
    """Parse `{ ... }` starting at lines[i] (emitter puts braces on their own
    lines); return the index just past the closing '}'."""
    if i >= len(lines) or lines[i].strip() != "{":
        got = lines[i].strip() if i < len(lines) else "<end of body>"
        raise ParseError(f"expected '{{', got {got!r}")
    close = _parse_c_block(lines, i + 1, out)
    if close >= len(lines) or lines[close].strip() != "}":
        raise ParseError("unterminated block")
    return close + 1


# --------------------------------------------------------------------------
# Clight (.v) side
# --------------------------------------------------------------------------

def sexp_parse(text):
    """Parse Coq constructor-application notation into nested lists of atoms.

    Iterative (explicit stack): certificate bodies right-nest thousands of
    `Ssequence` constructors, far beyond Python's recursion limit.
    """
    stack = [[]]
    for token in re.findall(r"[()]|[^()\s]+", text):
        if token == "(":
            stack.append([])
        elif token == ")":
            if len(stack) < 2:
                raise ParseError("unbalanced ')' in Clight term")
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ParseError("unbalanced '(' in Clight term")
    top = stack[0]
    return top[0] if len(top) == 1 else top


def v_expr(node):
    """Normalize a Clight expression term to the shared descriptor space."""
    if isinstance(node, str):
        raise ParseError(f"unexpected atom in Clight expression: {node}")
    head = node[0]
    if head == "Ecast":
        return v_expr(node[1])                      # casts erased (see docstring)
    if head == "Etempvar" or head == "Evar":
        return ("var", node[1].lstrip("_"))
    if head == "Econst_long":
        return ("lit", int(_repr_value(node[1])) % (1 << 64), 64)
    if head == "Econst_int":
        return ("lit", int(_repr_value(node[1])) % (1 << 32), 32)
    if head == "Ebinop":
        return ("bin", node[1], v_expr(node[2]), v_expr(node[3]))
    if head == "Eunop":
        return ("un", node[1], v_expr(node[2]))
    raise ParseError(f"unrecognized Clight expression head: {head}")


def _repr_value(node):
    # node = ["Int64.repr", "N"] or ["Int.repr", "N"] or ["Int.repr", ["-N"]...]
    value = node[1]
    while isinstance(value, list):                  # (Int.repr (-5)) nests once
        value = value[0]
    return value


def v_walk(root, out):
    """Walk a Clight statement term, appending normalized events.

    Iterative (explicit worklist) for the same reason as `sexp_parse`.
    Worklist items are statement nodes, or ("#emit", event) markers used to
    place endloop/else/endif after a substatement finishes.
    """
    work = [root]
    while work:
        node = work.pop()
        if isinstance(node, tuple):                 # deferred marker event
            out.events.append(node[1])
            continue
        if isinstance(node, str):
            if node in ("Sskip", "Sbreak", "Scontinue"):
                continue
            raise ParseError(f"unrecognized Clight statement atom: {node}")
        head = node[0]
        if head == "Ssequence":
            work += [node[2], node[1]]              # node[1] runs first
        elif head == "Sset":
            out.events.append(("assign", node[1].lstrip("_"), v_expr(node[2])))
        elif head in ("Swhile", "Sfor'"):
            out.events.append(("loop", v_expr(node[1])))
            work += [("#emit", ("endloop",)), node[2]]
        elif head == "Sloop":                       # rolled form: condition unknown
            out.events.append(("loop", None))
            work.append(("#emit", ("endloop",)))
            work += list(reversed(node[1:]))
        elif head == "Sifthenelse":
            out.events.append(("if", v_expr(node[1])))
            work += [("#emit", ("endif",)), node[3],
                     ("#emit", ("else",)), node[2]]
        elif head == "Slabel":
            out.events.append(("label", node[1].lstrip("_")))
            work.append(node[2])
        elif head == "Sgoto":
            out.events.append(("goto", node[1].lstrip("_")))
        elif head == "Sreturn":
            arg = node[1] if len(node) > 1 else "None"
            out.events.append(
                ("return", None if arg == "None" else v_expr(arg[1])))
        elif head == "Scall":
            callee = node[2]
            name = callee[1].lstrip("_") if isinstance(callee, list) \
                else str(callee)
            out.events.append(("call", name))
        else:
            raise ParseError(f"unrecognized Clight statement head: {head}")


def parse_v_functions(text):
    """Extract every `Definition f_l_* := {| ... |}.` Clight function."""
    funcs = {}
    for m in re.finditer(
            r"Definition\s+f_(l_\w+)\s*:=\s*\{\|(.*?)\|\}\.", text, re.S):
        name, record = m.group(1), m.group(2)
        body_m = re.search(r"fn_body\s*:=(.*)$", record, re.S)
        if not body_m:
            raise ParseError(f"no fn_body in Definition f_{name}")
        summary = FuncSummary(name)
        temps_m = re.search(r"fn_temps\s*:=(.*?);\s*fn_body", record, re.S)
        if temps_m:
            summary.temp_count = len(re.findall(r"\(_\w+,", temps_m.group(1)))
        v_walk(sexp_parse(body_m.group(1)), summary)
        funcs[name] = summary
    return funcs


# --------------------------------------------------------------------------
# Comparison and reporting
# --------------------------------------------------------------------------

def describe(d):
    if d is None:
        return "<none>"
    kind = d[0]
    if kind == "var":
        return d[1]
    if kind == "lit":
        return f"{d[1]}u{d[2]}"
    if kind == "bin":
        return f"({describe(d[2])} {d[1]} {describe(d[3])})"
    if kind == "un":
        return f"({d[1]} {describe(d[2])})"
    if kind == "call":
        return f"{d[1]}(...)"
    return repr(d)


def event_str(e):
    if e[0] == "assign":
        return f"{e[1]} := {describe(e[2])}"
    if e[0] in ("loop", "if"):
        return f"{e[0]} {describe(e[1])}"
    if e[0] in ("label", "goto", "call"):
        return f"{e[0]} {e[1]}"
    if e[0] == "return":
        return f"return {describe(e[1])}"
    return e[0]


def events_equal(a, b):
    """Exact equality, except a bare-Sloop condition (None) matches anything."""
    if a[0] == b[0] == "loop" and (a[1] is None or b[1] is None):
        return True
    return a == b


def compare(cf, vf):
    """Compare one C-side summary against one Clight-side summary.

    Returns a list of mismatch strings (empty means full correspondence).
    """
    problems = []
    ca, va = cf.assignments(), vf.assignments()
    if len(ca) != len(va):
        problems.append(f"assignment count: C has {len(ca)}, Clight has {len(va)}")
    c_ops = [e[2][1] if e[2][0] == "bin" else "move" for e in ca]
    v_ops = [e[2][1] if e[2][0] == "bin" else "move" for e in va]
    if c_ops != v_ops:
        i = next(i for i, (x, y) in enumerate(zip(c_ops, v_ops)) if x != y) \
            if any(x != y for x, y in zip(c_ops, v_ops)) else min(len(c_ops), len(v_ops))
        problems.append(
            f"operator sequence diverges at assignment #{i}: "
            f"C={c_ops[i] if i < len(c_ops) else '<end>'} "
            f"vs Clight={v_ops[i] if i < len(v_ops) else '<end>'}")
    c_dsts, v_dsts = [e[1] for e in ca], [e[1] for e in va]
    if c_dsts != v_dsts:
        i = next((i for i, (x, y) in enumerate(zip(c_dsts, v_dsts)) if x != y),
                 min(len(c_dsts), len(v_dsts)))
        problems.append(
            f"destination sequence diverges at assignment #{i}: "
            f"C={c_dsts[i] if i < len(c_dsts) else '<end>'} "
            f"vs Clight={v_dsts[i] if i < len(v_dsts) else '<end>'}")
    for kind in ("loop", "label", "goto"):
        if cf.count(kind) != vf.count(kind):
            problems.append(f"{kind} count: C has {cf.count(kind)}, "
                            f"Clight has {vf.count(kind)}")
    c_ret = [e for e in cf.events if e[0] == "return"]
    v_ret = [e for e in vf.events if e[0] == "return"]
    if [e[1] for e in c_ret] != [e[1] for e in v_ret]:
        problems.append(
            f"return mismatch: C returns {[describe(e[1]) for e in c_ret]}, "
            f"Clight returns {[describe(e[1]) for e in v_ret]}")
    # Full ordered event-stream check (covers operand kinds, literal values,
    # loop bodies, label names -- everything the summaries above may collapse).
    for i, (ce, ve) in enumerate(zip(cf.events, vf.events)):
        if not events_equal(ce, ve):
            problems.append(f"event #{i} differs:\n"
                            f"      C:      {event_str(ce)}\n"
                            f"      Clight: {event_str(ve)}")
            break
    else:
        if len(cf.events) != len(vf.events):
            problems.append(f"event count: C has {len(cf.events)}, "
                            f"Clight has {len(vf.events)}")
    return problems


def main(argv):
    if len(argv) != 3:
        print("Usage: clight-correspond.py <cert.c> <cert.v>", file=sys.stderr)
        return 2
    c_path, v_path = argv[1], argv[2]
    try:
        with open(c_path) as fh:
            c_funcs = parse_c_functions(fh.read())
        with open(v_path) as fh:
            v_funcs = parse_v_functions(fh.read())
    except (OSError, ParseError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    if not c_funcs:
        print(f"ERROR: no l_* certificate function found in {c_path}",
              file=sys.stderr)
        return 2

    failed = False
    for name, cf in c_funcs.items():
        print(f"function {name}:")
        vf = v_funcs.get(name)
        if vf is None:
            print(f"  FAIL: no Definition f_{name} in {v_path}")
            failed = True
            continue
        print(f"  C:      {len(cf.assignments())} assignments, "
              f"{cf.decl_count} declarations, {cf.count('loop')} loops, "
              f"{cf.count('label')} labels, {cf.count('goto')} gotos")
        print(f"  Clight: {len(vf.assignments())} assignments, "
              f"{vf.temp_count} temps, {vf.count('loop')} loops, "
              f"{vf.count('label')} labels, {vf.count('goto')} gotos")
        problems = compare(cf, vf)
        if problems:
            failed = True
            for p in problems:
                print(f"  FAIL: {p}")
        else:
            ops = [e[2][1] for e in cf.assignments() if e[2][0] == "bin"]
            print(f"  PASS: {len(cf.events)} structural events correspond "
                  f"({len(ops)} binary ops, "
                  f"{len(cf.assignments()) - len(ops)} moves/casts)")
    extra = set(v_funcs) - set(c_funcs)
    if extra:
        print(f"note: .v defines certificate functions absent from the C file: "
              f"{sorted(extra)}")
        failed = True
    print("RESULT:", "FAIL" if failed else "PASS")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
