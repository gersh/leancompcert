#!/usr/bin/env python3
"""Kernel-check exact AProgram C/clightgen/source correspondence.

The Lean side emits a compact, first-order ``adsl_program`` contract and the
actual rolled C.  This checker runs the pinned CompCert ``clightgen``, proves
that the complete imported Clight function is definitionally equal to the
generic array emitter compiler, and then applies the generic mutable-memory
correctness theorem.  The proof is symbolic in the loop count: it does not run
the certificate computation.
"""

from __future__ import annotations

import argparse
import fcntl
import glob
import hashlib
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time

DEFAULT_COMPCERT = os.environ.get("COMPCERT_DIR", "/home/gersh/CompCert-3.17")
SCRIPT_DIR = Path(__file__).resolve().parent
COQ_DIR = SCRIPT_DIR / "coq"

DIRECT_FILES = [
    "ClightFragmentSem.v",
    "ClightDefinedOps.v",
    "ClightDSLCompiler.v",
    "ClightRolledCompiler.v",
    "ClightEmitterCompiler.v",
    "ClightEmitterCorrect.v",
    "ClightMemorySem.v",
    "ClightFlatSem.v",
    "ClightArrayEmitterCompiler.v",
    "ClightArrayEmitterCorrect.v",
]

SOURCE_RE = re.compile(
    r"Definition\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*adsl_program\s*:=")
EMITTER_SOURCE_RE = re.compile(
    r"Definition\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*"
    r"array_emitter_source\s*:=")
FUNCTION_RE = re.compile(
    r"^\s*uint64_t\s+(l_[A-Za-z0-9_]+)\s*"
    r"\(uint64_t\s*\*\s*(v_[0-9]+)\)\s*\n\s*\{",
    re.MULTILINE,
)
DECL_RE = re.compile(
    r"(?:Lemma|Theorem)\s+([A-Za-z_][A-Za-z0-9_']*)\s*:")


class CheckError(Exception):
    pass


def compcert_flags(root: Path) -> list[str]:
    project = root / "_CoqProject"
    mappings: list[tuple[str, str, str]] = []
    if project.exists():
        tokens = project.read_text().split()
        i = 0
        while i < len(tokens):
            if tokens[i] in ("-R", "-Q") and i + 2 < len(tokens):
                mappings.append((tokens[i], tokens[i + 1], tokens[i + 2]))
                i += 3
            else:
                i += 1
    if not mappings:
        mappings = [
            ("-R", "lib", "compcert.lib"),
            ("-R", "common", "compcert.common"),
            ("-R", "aarch64", "compcert.aarch64"),
            ("-R", "backend", "compcert.backend"),
            ("-R", "cfrontend", "compcert.cfrontend"),
            ("-R", "driver", "compcert.driver"),
            ("-R", "cparser", "compcert.cparser"),
            ("-R", "export", "compcert.export"),
            ("-R", "flocq", "Flocq"),
            ("-R", "MenhirLib", "MenhirLib"),
        ]
    flags: list[str] = []
    for option, physical, logical in mappings:
        path = root / physical
        if path.is_dir():
            flags += [option, str(path), logical]
    if not flags:
        raise CheckError(f"no CompCert Coq tree found below {root}")
    return flags


def limit_address_space(memory_bytes: int):
    def apply_limit() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
    return apply_limit


def run(
    command: list[str], cwd: Path, label: str,
    timeout_seconds: float, memory_bytes: int,
) -> None:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command, cwd=cwd, capture_output=True, text=True,
            timeout=timeout_seconds,
            preexec_fn=limit_address_space(memory_bytes),
        )
    except subprocess.TimeoutExpired as exc:
        raise CheckError(
            f"{label} exceeded the {timeout_seconds:g}s timeout") from exc
    elapsed = time.monotonic() - started
    if result.returncode != 0:
        detail = result.stderr or result.stdout
        cap = memory_bytes / (1024 ** 3)
        raise CheckError(
            f"{label} failed ({elapsed:.1f}s; address-space cap {cap:g} GiB):"
            f"\n{detail}")
    print(f"  {label}: {elapsed:.1f}s")


def find_coqc(
    explicit: str | None, flags: list[str], work: Path,
    timeout_seconds: float, memory_bytes: int,
) -> str:
    candidates: list[str] = []
    if explicit:
        candidates.append(explicit)
    if os.environ.get("COQC"):
        candidates.append(os.environ["COQC"])
    candidates += ["coqc"]
    candidates += sorted(glob.glob(os.path.expanduser("~/.opam/*/bin/coqc")))
    probe = work / "CoqProbe.v"
    probe.write_text("From compcert Require Import Clight.\n")
    errors: list[str] = []
    for candidate in candidates:
        executable = shutil.which(candidate)
        if executable is None and not os.access(candidate, os.X_OK):
            errors.append(f"{candidate}: not found")
            continue
        command = executable or candidate
        try:
            result = subprocess.run(
                [command, *flags, str(probe)], capture_output=True, text=True,
                timeout=timeout_seconds,
                preexec_fn=limit_address_space(memory_bytes),
            )
        except subprocess.TimeoutExpired:
            errors.append(f"{candidate}: probe timed out")
            continue
        if result.returncode == 0:
            return command
        tail = result.stderr.strip().splitlines()
        errors.append(f"{candidate}: {tail[-1] if tail else 'failed'}")
    raise CheckError(
        "no coqc compatible with the compiled CompCert tree:\n  "
        + "\n  ".join(errors))


def isolate_record(text: str, definition: str, kind: str) -> str:
    match = re.search(
        rf"Definition\s+{re.escape(definition)}\s*:\s*{kind}\s*:=\s*"
        rf"\{{\|(.*?)\|\}}\.", text, re.DOTALL)
    if match is None:
        raise CheckError(f"cannot isolate {kind} {definition!r}")
    return match.group(1)


def choose_definition(
    text: str, pattern: re.Pattern[str], requested: str | None, kind: str,
) -> str:
    definitions = pattern.findall(text)
    if requested is None:
        if len(definitions) != 1:
            raise CheckError(
                f"contract must contain exactly one {kind}, or pass its "
                "explicit selector")
        return definitions[0]
    if requested not in definitions:
        raise CheckError(f"{kind} {requested!r} not found")
    return requested


def source_info(
    source_text: str, requested_source: str | None,
    requested_emitter: str | None,
) -> tuple[str, str, int]:
    source = choose_definition(
        source_text, SOURCE_RE, requested_source, "adsl_program")
    emitter = choose_definition(
        source_text, EMITTER_SOURCE_RE, requested_emitter,
        "array_emitter_source")
    source_record = isolate_record(source_text, source, "adsl_program")
    emitter_record = isolate_record(
        source_text, emitter, "array_emitter_source")
    source_count = re.search(r"ap_reg_count\s*:=\s*(\d+)\s*;", source_record)
    emitter_count = re.search(
        r"aes_reg_count\s*:=\s*(\d+)\s*;", emitter_record)
    if source_count is None or emitter_count is None:
        raise CheckError("source contracts need literal register counts")
    if source_count.group(1) != emitter_count.group(1):
        raise CheckError("semantic and emitter register counts disagree")
    return source, emitter, int(source_count.group(1))


def c_info(
    c_text: str, requested_function: str | None, reg_count: int,
) -> tuple[str, int]:
    functions = FUNCTION_RE.findall(c_text)
    if requested_function is None:
        if len(functions) != 1:
            raise CheckError(
                "C file must contain exactly one emitted pointer function, "
                "or pass --function")
        function, base_name = functions[0]
    else:
        matches = [item for item in functions if item[0] == requested_function]
        if len(matches) != 1:
            raise CheckError(f"C function {requested_function!r} not found")
        function, base_name = matches[0]
    counter = reg_count + 1
    base = reg_count + 2
    if base_name != f"v_{base}":
        raise CheckError(
            f"expected array parameter v_{base}, found {base_name}")
    required = ["uint8_t v_0;"]
    required += [f"uint64_t v_{i};" for i in range(1, counter + 1)]
    missing = [declaration for declaration in required if declaration not in c_text]
    if missing:
        raise CheckError(
            "C file is not in the current AProgram declaration layout; "
            f"missing {missing[0]!r}")
    guards = re.findall(
        rf"while\s*\(\(v_{counter}\s*<\s*UINT64_C\((\d+)\)\)\)",
        c_text)
    if len(guards) != 1:
        raise CheckError("expected exactly one while guard on the counter")
    return function, int(guards[0])


def coq_check_text(
    source: str, emitter: str, function: str, reg_count: int,
    loop_limit: int, wf_lemma: str, loop_relation: str,
    source_match: str, syntax_only: bool,
) -> str:
    counter = reg_count + 1
    base = reg_count + 2
    regs = "; ".join(f"Cert._v_{i}" for i in range(1, reg_count + 1))
    lines = [
        "(* Generated by scripts/clight-exact-array.py. *)",
        "From Coq Require Import List ZArith Lia.",
        "From compcert Require Import Maps Integers Values Events Memory AST Ctypes Cop Clight ClightBigstep.",
        "From Direct Require Import ClightDSLCompiler ClightRolledCompiler.",
        "From Direct Require Import ClightEmitterCompiler ClightFlatSem.",
        "From Direct Require Import ClightArrayEmitterCompiler.",
    ]
    if not syntax_only:
        lines.append(
            "From Direct Require Import ClightArrayEmitterCorrect.")
    lines += [
        "Require Import Cert Source.",
        "Import ListNotations.",
        "Local Open Scope Z_scope.",
        "",
        "Fixpoint imported_internal_functions",
        "    (ds : list (ident * globdef fundef type)) :",
        "    list (ident * function) :=",
        "  match ds with",
        "  | nil => nil",
        "  | (id, Gfun (Internal f)) :: tl =>",
        "      if Pos.eqb id Cert._main then imported_internal_functions tl",
        "      else (id, f) :: imported_internal_functions tl",
        "  | _ :: tl => imported_internal_functions tl",
        "  end.",
        "",
        "Fixpoint imported_global_variables",
        "    (ds : list (ident * globdef fundef type)) : list ident :=",
        "  match ds with",
        "  | nil => nil",
        "  | (id, Gvar _) :: tl => id :: imported_global_variables tl",
        "  | _ :: tl => imported_global_variables tl",
        "  end.",
        "",
        "Lemma exact_imported_user_definitions :",
        "  imported_internal_functions Cert.global_definitions =",
        f"    [(Cert._{function}, Cert.f_{function})] /\\",
        "  imported_global_variables Cert.global_definitions = nil.",
        "Proof. split; reflexivity. Qed.",
        "",
        "Definition imported_scalar_layout : emitter_layout := {|",
        "  el_scratch := Cert._v_0;",
        f"  el_regs := [{regs}];",
        f"  el_counter := Cert._v_{counter}",
        "|}.",
        "",
        "Definition imported_layout : array_emitter_layout := {|",
        "  ael_scalar := imported_scalar_layout;",
        f"  ael_base := Cert._v_{base}",
        "|}.",
        "",
        f"Definition imported_loop_limit : Z := {loop_limit}.",
        "",
        "Lemma exact_imported_function :",
        f"  Cert.f_{function} =",
        "  compile_array_emitted_rolled_program imported_layout",
        f"    imported_loop_limit Source.{emitter}.",
        "Proof.",
        "  apply (exact_decision_is_left_sound _",
        f"    (clight_function_eq_dec Cert.f_{function}",
        "      (compile_array_emitted_rolled_program imported_layout",
        f"        imported_loop_limit Source.{emitter}))).",
        "  vm_compute; reflexivity.",
        "Qed.",
        "",
    ]
    if syntax_only:
        return "\n".join(lines)
    lines += [
        "Lemma imported_layout_wf :",
        "  array_emitter_layout_wf imported_layout",
        f"    (aes_reg_count Source.{emitter}).",
        "Proof.",
        "  apply array_emitter_layout_wfb_sound.",
        "  vm_compute; reflexivity.",
        "Qed.",
        "",
        "Theorem exact_imported_function_preserves_denotation :",
        "  forall (w : int64) (ge : genv) (b : block) (m : mem),",
        "    flat_block_rel (PTree.empty int64) m b",
        f"      (8 * ap_array_len Source.{source}) ->",
        f"    adsl_denote Source.{source} = Some w ->",
        "    exists m',",
        "      ClightBigstep.eval_funcall function_entry2 ge m",
        f"        (Internal Cert.f_{function})",
        "        [Vptr b Ptrofs.zero] E0 m' (Vlong w).",
        "Proof.",
        "  intros w ge b m MEM DEN.",
        "  rewrite exact_imported_function.",
        "  eapply compile_array_emitted_rolled_program_correct.",
        f"  - exact Source.{source_match}.",
        "  - exact imported_layout_wf.",
        f"  - exact Source.{wf_lemma}.",
        f"  - exact Source.{loop_relation}.",
        "  - exact DEN.",
        "  - exact MEM.",
        "Qed.",
        "",
        "Print Assumptions exact_imported_function_preserves_denotation.",
        "",
    ]
    return "\n".join(lines)


def version_probe(
    command: list[str], label: str, timeout_seconds: float, memory_bytes: int,
) -> subprocess.CompletedProcess[str]:
    try:
        result = subprocess.run(
            command, capture_output=True, text=True, timeout=timeout_seconds,
            preexec_fn=limit_address_space(memory_bytes))
    except subprocess.TimeoutExpired as exc:
        raise CheckError(f"{label} timed out") from exc
    if result.returncode != 0:
        raise CheckError(
            f"{label} failed: {(result.stderr or result.stdout).strip()}")
    return result


def check(
    c_path: Path, source_path: Path, outdir: Path, compcert: Path,
    explicit_coqc: str | None, explicit_clightgen: str | None,
    requested_source: str | None, requested_emitter: str | None,
    requested_function: str | None, timeout_seconds: float,
    memory_limit_gib: float, syntax_only: bool,
    proof_cache: Path | None,
) -> None:
    if timeout_seconds <= 0 or memory_limit_gib <= 0:
        raise CheckError("timeout and memory limit must be positive")
    outdir.mkdir(parents=True, exist_ok=True)
    c_bytes = c_path.read_bytes()
    c_text = c_bytes.decode()
    source_text = source_path.read_text()
    source, emitter, reg_count = source_info(
        source_text, requested_source, requested_emitter)
    function, loop_limit = c_info(c_text, requested_function, reg_count)
    declarations = set(DECL_RE.findall(source_text))
    wf_lemma = f"{source}_wf"
    loop_relation = f"{source}_loop_relation"
    source_match = f"{emitter}_matches"
    for label, declaration in (
        ("well-formedness", wf_lemma),
        ("loop relation", loop_relation),
        ("source match", source_match),
    ):
        if declaration not in declarations:
            raise CheckError(f"contract lacks expected {label} lemma {declaration}")

    files = DIRECT_FILES if not syntax_only else [
        name for name in DIRECT_FILES
        if name not in ("ClightEmitterCorrect.v", "ClightArrayEmitterCorrect.v")
    ]
    missing = [name for name in files if not (COQ_DIR / name).exists()]
    if missing:
        raise CheckError("missing generic proof file: " + ", ".join(missing))
    shutil.copyfile(c_path, outdir / "Cert.c")
    shutil.copyfile(source_path, outdir / "Source.v")

    memory_bytes = int(memory_limit_gib * (1024 ** 3))
    flags = compcert_flags(compcert)
    coqc = find_coqc(
        explicit_coqc, flags, outdir, timeout_seconds, memory_bytes)
    clightgen = explicit_clightgen or str(compcert / "clightgen")
    clightgen = shutil.which(clightgen) or clightgen
    if not os.path.isfile(clightgen) or not os.access(clightgen, os.X_OK):
        raise CheckError(f"clightgen is not executable at {clightgen}")

    coqc_version = version_probe(
        [coqc, "--version"], "coqc version probe", timeout_seconds,
        memory_bytes)
    clight_version = version_probe(
        [clightgen, "-version"], "clightgen version probe", timeout_seconds,
        memory_bytes)
    version_file = compcert / "VERSION"
    if not version_file.is_file():
        raise CheckError(f"missing CompCert version pin {version_file}")
    expected = re.search(
        r"^version=([^\s]+)$", version_file.read_text(), re.MULTILINE)
    version_text = (clight_version.stdout or clight_version.stderr).strip()
    actual = re.search(r"\bversion\s+([^\s]+)", version_text)
    if expected is None or actual is None or expected.group(1) != actual.group(1):
        raise CheckError("clightgen and CompCert Coq tree versions do not match")
    first = coqc_version.stdout.splitlines()
    print(f"coqc: {coqc} ({first[0] if first else 'unknown'})")
    print(f"clightgen: {clightgen} ({version_text})")

    if proof_cache is None:
        direct = outdir / "Direct"
        cache_ready = None
    else:
        cache_hash = hashlib.sha256()
        cache_hash.update(str(compcert.resolve()).encode())
        cache_hash.update(coqc_version.stdout.encode())
        cache_hash.update(version_text.encode())
        cache_hash.update(str(syntax_only).encode())
        for name in files:
            cache_hash.update(name.encode())
            cache_hash.update((COQ_DIR / name).read_bytes())
        cache_entry = proof_cache / cache_hash.hexdigest()
        direct = cache_entry / "Direct"
        cache_ready = cache_entry / "READY"
    direct.mkdir(parents=True, exist_ok=True)
    local_flags = [*flags, "-Q", str(direct), "Direct"]
    run([clightgen, "-normalize", "Cert.c"], outdir,
        "clightgen -normalize", timeout_seconds, memory_bytes)

    def generic_cache_complete() -> bool:
        return (
            cache_ready is not None
            and cache_ready.is_file()
            and all((direct / name.replace(".v", ".vo")).is_file()
                    for name in files)
        )

    if proof_cache is None:
        for name in files:
            shutil.copyfile(COQ_DIR / name, direct / name)
            run([coqc, *local_flags, str(direct / name)], outdir, name[:-2],
                timeout_seconds, memory_bytes)
    else:
        lock_path = direct.parent / "LOCK"
        with lock_path.open("a+") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            if generic_cache_complete():
                print(f"  generic proof cache: hit ({direct.parent})")
            else:
                print(f"  generic proof cache: populate ({direct.parent})")
                for name in files:
                    shutil.copyfile(COQ_DIR / name, direct / name)
                    run([coqc, *local_flags, str(direct / name)], outdir,
                        name[:-2], timeout_seconds, memory_bytes)
                assert cache_ready is not None
                cache_ready.write_text("kernel-checked\n")
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
    run([coqc, *local_flags, "Source.v"], outdir,
        "Lean source contract", timeout_seconds, memory_bytes)
    run([coqc, *local_flags, "Cert.v"], outdir,
        "clightgen Clight AST", timeout_seconds, memory_bytes)
    (outdir / "ExactCheck.v").write_text(coq_check_text(
        source, emitter, function, reg_count, loop_limit, wf_lemma,
        loop_relation, source_match, syntax_only))
    run([coqc, *local_flags, "ExactCheck.v"], outdir,
        "exact full-AST proof", timeout_seconds, memory_bytes)

    print(f"  C sha256: {hashlib.sha256(c_bytes).hexdigest()}")
    print(f"  Qed: Cert.f_{function} is the exact array-emitter Clight AST")
    if not syntax_only:
        print("  Qed: that exact function preserves adsl_denote and memory")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Kernel-check exact rolled AProgram C/Clight correspondence")
    parser.add_argument("cert_c")
    parser.add_argument("source_contract")
    parser.add_argument("outdir")
    parser.add_argument("--source-def")
    parser.add_argument("--emitter-source-def")
    parser.add_argument("--function")
    parser.add_argument("--compcert", default=DEFAULT_COMPCERT)
    parser.add_argument("--clightgen")
    parser.add_argument("--coqc")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--memory-limit-gib", type=float, default=2.0)
    parser.add_argument(
        "--proof-cache", type=Path,
        help="reuse kernel-checked generic Coq modules across many shards")
    parser.add_argument("--syntax-only", action="store_true")
    args = parser.parse_args(argv[1:])
    try:
        check(
            Path(args.cert_c).resolve(),
            Path(args.source_contract).resolve(),
            Path(args.outdir).resolve(),
            Path(args.compcert).resolve(), args.coqc, args.clightgen,
            args.source_def, args.emitter_source_def, args.function,
            args.timeout, args.memory_limit_gib, args.syntax_only,
            args.proof_cache.resolve() if args.proof_cache else None)
        return 0
    except (OSError, CheckError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
