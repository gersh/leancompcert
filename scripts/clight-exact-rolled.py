#!/usr/bin/env python3
"""Prove that clightgen's full function is the exact rolled-emitter compiler.

The input source contract is the compact Coq serialization emitted from the
Lean Reflect.Program, including its explicit count-free ``emitter_source``.
This tool:

  1. runs CompCert 3.17's clightgen itself on the supplied C file;
  2. compiles that generated .v file as module Cert;
  3. instantiates the explicit scratch/register/counter identifier layout;
  4. asks Coq's kernel to prove by reflexivity that the *whole* imported
     function equals compile_emitted_rolled_program applied directly to that
     Lean-emitted count-free source.

Unlike clight-correspond[-coq].py, this does not erase casts or reduce the
function to an event stream.  Return/call-convention/parameters/locals/temp
types and order/the complete statement and expression AST are all in the
equality.  By default the generated check also derives CompCert big-step
correctness for that exact imported function; ``--syntax-only`` explicitly
requests the weaker equality-only check.
"""

from __future__ import annotations

import argparse
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
]

SOURCE_RE = re.compile(
    r"Definition\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*dsl_program\s*:=")
EMITTER_SOURCE_RE = re.compile(
    r"Definition\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*emitter_source\s*:=")
REG_COUNT_RE = re.compile(r"dp_reg_count\s*:=\s*(\d+)\s*;")
FUNCTION_RE = re.compile(
    r"^\s*uint64_t\s+(l_[A-Za-z0-9_]+)\s*\(void\)\s*\n\s*\{",
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
        toks = project.read_text().split()
        i = 0
        while i < len(toks):
            if toks[i] in ("-R", "-Q") and i + 2 < len(toks):
                mappings.append((toks[i], toks[i + 1], toks[i + 2]))
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


def find_coqc(
    explicit: str | None,
    flags: list[str],
    work: Path,
    timeout_seconds: float,
    memory_bytes: int,
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
                [command, *flags, str(probe)],
                capture_output=True,
                text=True,
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
        + "\n  ".join(errors)
    )


def source_info(
    source_text: str, requested: str | None
) -> tuple[str, int]:
    definitions = SOURCE_RE.findall(source_text)
    if requested is None:
        if len(definitions) != 1:
            raise CheckError(
                "source contract must contain exactly one dsl_program "
                "definition, or pass --source-def"
            )
        source_def = definitions[0]
    else:
        source_def = requested
        if source_def not in definitions:
            raise CheckError(f"source definition {source_def!r} not found")
    match = re.search(
        rf"Definition\s+{re.escape(source_def)}\s*:\s*dsl_program\s*:=\s*"
        rf"\{{\|(.*?)\|\}}\.",
        source_text,
        re.DOTALL,
    )
    if match is None:
        raise CheckError(f"cannot isolate dsl_program {source_def!r}")
    record = match.group(1)
    count = REG_COUNT_RE.search(record)
    if count is None:
        raise CheckError("source contract has no literal dp_reg_count")
    return source_def, int(count.group(1))


def emitter_source_info(
    source_text: str, requested: str | None
) -> tuple[str, int]:
    definitions = EMITTER_SOURCE_RE.findall(source_text)
    if requested is None:
        if len(definitions) != 1:
            raise CheckError(
                "Lean contract must contain exactly one explicit count-free "
                "emitter_source definition, or pass --emitter-source-def"
            )
        emitter_def = definitions[0]
    else:
        emitter_def = requested
        if emitter_def not in definitions:
            raise CheckError(
                f"emitter source definition {emitter_def!r} not found"
            )
    match = re.search(
        rf"Definition\s+{re.escape(emitter_def)}\s*:\s*emitter_source\s*:=\s*"
        rf"\{{\|(.*?)\|\}}\.",
        source_text,
        re.DOTALL,
    )
    if match is None:
        raise CheckError(f"cannot isolate emitter_source {emitter_def!r}")
    count = re.search(r"es_reg_count\s*:=\s*(\d+)\s*;", match.group(1))
    if count is None:
        raise CheckError("emitter_source has no literal es_reg_count")
    return emitter_def, int(count.group(1))


def function_info(c_text: str, requested: str | None) -> str:
    functions = FUNCTION_RE.findall(c_text)
    if requested is None:
        if len(functions) != 1:
            raise CheckError(
                "C file must contain exactly one emitted uint64_t l_* "
                "definition, or pass --function"
            )
        return functions[0]
    if requested not in functions:
        raise CheckError(f"C function {requested!r} not found")
    return requested


def validate_layout_spelling(c_text: str, reg_count: int) -> None:
    required = ["uint8_t v_0;"]
    required += [f"uint64_t v_{i};" for i in range(1, reg_count + 1)]
    required += [f"uint64_t v_{reg_count + 1} = UINT64_C(0);"]
    missing = [line for line in required if line not in c_text]
    if missing:
        raise CheckError(
            "C file is not in the current rolled-emitter declaration layout; "
            f"missing {missing[0]!r}"
        )


def loop_limit_info(c_text: str, reg_count: int) -> int:
    pattern = re.compile(
        rf"while\s*\(\(v_{reg_count + 1}\s*<\s*UINT64_C\((\d+)\)\)\)"
    )
    limits = pattern.findall(c_text)
    if len(limits) != 1:
        raise CheckError(
            "expected exactly one rolled while guard using the counter"
        )
    return int(limits[0])


def coq_check_text(
    source_def: str,
    function: str,
    reg_count: int,
    loop_limit: int,
    semantic: bool,
    wf_lemma: str | None,
    loop_relation: str | None,
    emitter_source_def: str,
    source_match: str | None,
) -> str:
    regs = "; ".join(f"Cert._v_{i}" for i in range(1, reg_count + 1))
    reg_defs = ", ".join(
        f"Cert._v_{i}" for i in range(1, reg_count + 1)
    )
    scratch_reg_defs = ", ".join(
        ["Cert._v_0"] + [f"Cert._v_{i}" for i in range(1, reg_count + 1)]
    )
    counter_reg_defs = ", ".join(
        [f"Cert._v_{i}" for i in range(1, reg_count + 2)]
    )
    lines = [
        "(* Generated by scripts/clight-exact-rolled.py. *)",
        "From Coq Require Import List ZArith Lia.",
        "From compcert Require Import Integers Values Events Memory AST Ctypes Cop Clight ClightBigstep.",
        "From Direct Require Import ClightDSLCompiler ClightRolledCompiler.",
        "From Direct Require Import ClightEmitterCompiler.",
    ]
    if semantic:
        lines.append("From Direct Require Import ClightEmitterCorrect.")
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
        "Definition imported_layout : emitter_layout := {|",
        "  el_scratch := Cert._v_0;",
        f"  el_regs := [{regs}];",
        f"  el_counter := Cert._v_{reg_count + 1}",
        "|}.",
        "",
        f"Definition imported_loop_limit : Z := {loop_limit}.",
        "",
        "Lemma exact_imported_function :",
        f"  Cert.f_{function} =",
        "  compile_emitted_rolled_program imported_layout imported_loop_limit",
        f"    Source.{emitter_source_def}.",
        "Proof. reflexivity. Qed.",
        "",
    ]
    if semantic:
        lines += [
            "Lemma imported_layout_wf :",
            "  emitter_layout_wf imported_layout",
            f"    (es_reg_count Source.{emitter_source_def}).",
            "Proof.",
            "  constructor.",
            "  - reflexivity.",
            f"  - change (NoDup [{regs}]).",
            f"    unfold {reg_defs}.",
            "    repeat (apply NoDup_cons; [simpl; intuition congruence | ]).",
            "    apply NoDup_nil.",
            f"  - change (~ In Cert._v_0 [{regs}]).",
            f"    unfold {scratch_reg_defs}.",
            "    simpl; intuition congruence.",
            f"  - change (~ In Cert._v_{reg_count + 1} [{regs}]).",
            f"    unfold {counter_reg_defs}.",
            "    simpl; intuition congruence.",
            f"  - change (Cert._v_0 <> Cert._v_{reg_count + 1}).",
            f"    unfold Cert._v_0, Cert._v_{reg_count + 1}; congruence.",
            "Qed.",
            "",
            "Lemma imported_source_matches :",
            f"  emitter_source_matches Source.{emitter_source_def}",
            f"    Source.{source_def}.",
            "Proof.",
            (
                f"  exact Source.{source_match}."
                if source_match
                else "  constructor; reflexivity."
            ),
            "Qed.",
            "",
            "Theorem exact_imported_function_preserves_denotation_if :",
            f"  rolled_wf Source.{source_def} ->",
            "  imported_loop_limit =",
            f"    Z.of_nat (dp_loop_count Source.{source_def}) ->",
            "  forall (w : int64) (ge : genv) (m : mem),",
            f"    dsl_denote Source.{source_def} = Some w ->",
            "    ClightBigstep.eval_funcall function_entry2 ge m",
            f"      (Internal Cert.f_{function}) nil E0 m (Vlong w).",
            "Proof.",
            "  intros WF LIMIT w ge m DEN.",
            "  rewrite exact_imported_function.",
            "  eapply compile_emitted_rolled_program_correct.",
            "  - exact imported_source_matches.",
            "  - exact imported_layout_wf.",
            "  - exact WF.",
            "  - exact LIMIT.",
            "  - exact DEN.",
            "Qed.",
            "",
        ]
        if wf_lemma and loop_relation and source_match:
            lines += [
                "Theorem exact_imported_function_preserves_denotation :",
                "  forall (w : int64) (ge : genv) (m : mem),",
                f"    dsl_denote Source.{source_def} = Some w ->",
                "    ClightBigstep.eval_funcall function_entry2 ge m",
                f"      (Internal Cert.f_{function}) nil E0 m (Vlong w).",
                "Proof.",
                "  apply exact_imported_function_preserves_denotation_if.",
                f"  - exact Source.{wf_lemma}.",
                f"  - exact Source.{loop_relation}.",
                "Qed.",
                "",
                "Print Assumptions exact_imported_function_preserves_denotation.",
                "",
            ]
        else:
            lines += [
                "Print Assumptions exact_imported_function_preserves_denotation_if.",
                "",
            ]
    return "\n".join(lines)


def run(
    command: list[str],
    cwd: Path,
    label: str,
    timeout_seconds: float,
    memory_bytes: int,
) -> None:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            preexec_fn=limit_address_space(memory_bytes),
        )
    except subprocess.TimeoutExpired as exc:
        raise CheckError(
            f"{label} exceeded the {timeout_seconds:g}s timeout"
        ) from exc
    elapsed = time.monotonic() - started
    if result.returncode != 0:
        detail = result.stderr or result.stdout
        cap = memory_bytes / (1024 ** 3)
        raise CheckError(
            f"{label} failed ({elapsed:.1f}s; address-space cap {cap:g} GiB):"
            f"\n{detail}"
        )
    print(f"  {label}: {elapsed:.1f}s")


def check(
    c_path: Path,
    source_path: Path,
    outdir: Path,
    compcert: Path,
    explicit_coqc: str | None,
    requested_source: str | None = None,
    requested_function: str | None = None,
    requested_wf_lemma: str | None = None,
    requested_loop_relation: str | None = None,
    requested_emitter_source: str | None = None,
    requested_source_match: str | None = None,
    syntax_only: bool = False,
    explicit_clightgen: str | None = None,
    timeout_seconds: float = 120.0,
    memory_limit_gib: float = 4.0,
) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    c_bytes = c_path.read_bytes()
    c_text = c_bytes.decode()
    source_text = source_path.read_text()
    source_def, source_reg_count = source_info(source_text, requested_source)
    emitter_source_def, emitter_reg_count = emitter_source_info(
        source_text, requested_emitter_source
    )
    reg_count = emitter_reg_count
    if source_reg_count != emitter_reg_count:
        raise CheckError(
            "semantic and count-free source register counts disagree"
        )
    function = function_info(c_text, requested_function)
    validate_layout_spelling(c_text, reg_count)
    loop_limit = loop_limit_info(c_text, reg_count)
    declarations = set(DECL_RE.findall(source_text))
    default_wf = f"{source_def}_rolled_wf"
    default_relation = f"{source_def}_loop_relation"
    default_source_match = f"{emitter_source_def}_matches"
    wf_lemma = requested_wf_lemma or (
        default_wf if default_wf in declarations else None
    )
    loop_relation = requested_loop_relation or (
        default_relation if default_relation in declarations else None
    )
    source_match = requested_source_match or (
        default_source_match if default_source_match in declarations else None
    )
    for label, name in (
        ("WF lemma", wf_lemma),
        ("loop relation", loop_relation),
        ("source-match lemma", source_match),
    ):
        if name is not None and name not in declarations:
            raise CheckError(f"requested {label} {name!r} is not declared")
    if source_match is None:
        raise CheckError(
            f"Lean contract must declare {default_source_match!r} (or pass "
            "--source-match); refusing an unbound count-free source"
        )

    direct = outdir / "Direct"
    direct.mkdir(exist_ok=True)
    semantic = not syntax_only
    if semantic and not (COQ_DIR / "ClightEmitterCorrect.v").exists():
        raise CheckError(
            "ClightEmitterCorrect.v is required for the default semantic "
            "check; use --syntax-only only when exact AST equality is enough"
        )
    direct_files = DIRECT_FILES + (
        ["ClightEmitterCorrect.v"] if semantic else []
    )
    missing = [name for name in direct_files if not (COQ_DIR / name).exists()]
    if missing:
        raise CheckError(
            "required generic proof file is missing: " + ", ".join(missing)
        )
    for name in direct_files:
        shutil.copyfile(COQ_DIR / name, direct / name)
    shutil.copyfile(c_path, outdir / "Cert.c")
    shutil.copyfile(source_path, outdir / "Source.v")

    if timeout_seconds <= 0 or memory_limit_gib <= 0:
        raise CheckError("timeout and memory limit must be positive")
    memory_bytes = int(memory_limit_gib * (1024 ** 3))
    flags = compcert_flags(compcert)
    coqc = find_coqc(
        explicit_coqc, flags, outdir, timeout_seconds, memory_bytes
    )
    if explicit_clightgen:
        clightgen = shutil.which(explicit_clightgen) or explicit_clightgen
    else:
        clightgen = str(compcert / "clightgen")
    if not os.path.isfile(clightgen) or not os.access(clightgen, os.X_OK):
        raise CheckError(
            f"clightgen not executable at {clightgen}; pass --clightgen "
            "to select the binary paired with this CompCert Coq tree"
        )
    local_flags = [*flags, "-Q", str(direct), "Direct"]
    def version_probe(
        command: list[str], label: str
    ) -> subprocess.CompletedProcess[str]:
        try:
            result = subprocess.run(
                command,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                preexec_fn=limit_address_space(memory_bytes),
            )
        except subprocess.TimeoutExpired as exc:
            raise CheckError(
                f"{label} exceeded the {timeout_seconds:g}s timeout"
            ) from exc
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise CheckError(f"{label} failed: {detail}")
        return result

    coqc_version = version_probe([coqc, "--version"], "coqc version probe")
    version_lines = coqc_version.stdout.splitlines()
    print(f"coqc: {coqc} ({version_lines[0] if version_lines else 'unknown'})")
    clight_version = version_probe(
        [clightgen, "-version"], "clightgen version probe"
    )
    version_text = (clight_version.stdout or clight_version.stderr).strip()
    version_file = compcert / "VERSION"
    if not version_file.is_file():
        raise CheckError(
            f"cannot pin clightgen to the CompCert tree: missing {version_file}"
        )
    expected_match = re.search(
        r"^version=([^\s]+)$", version_file.read_text(), re.MULTILINE
    )
    actual_match = re.search(r"\bversion\s+([^\s]+)", version_text)
    if expected_match is None or actual_match is None:
        raise CheckError(
            "cannot establish the clightgen/CompCert-tree version match"
        )
    expected_version = expected_match.group(1)
    actual_version = actual_match.group(1)
    if actual_version != expected_version:
        raise CheckError(
            f"clightgen reports {actual_version}, but {version_file} pins "
            f"the Coq tree to {expected_version}"
        )
    print(f"clightgen: {clightgen} ({version_text})")

    def checked_run(command: list[str], label: str) -> None:
        run(
            command, outdir, label, timeout_seconds, memory_bytes
        )

    checked_run([clightgen, "-normalize", "Cert.c"], "clightgen -normalize")
    for name in direct_files:
        checked_run([coqc, *local_flags, str(direct / name)], name[:-2])
    checked_run([coqc, *local_flags, "Source.v"], "Lean source contract")
    checked_run([coqc, *local_flags, "Cert.v"], "clightgen Clight AST")

    (outdir / "ExactCheck.v").write_text(
        coq_check_text(
            source_def,
            function,
            reg_count,
            loop_limit,
            semantic,
            wf_lemma,
            loop_relation,
            emitter_source_def,
            source_match,
        )
    )
    checked_run([coqc, *local_flags, "ExactCheck.v"], "exact full-AST proof")

    c_digest = hashlib.sha256(c_bytes).hexdigest()
    print(f"  C sha256: {c_digest}")
    print(f"  Qed: Cert.f_{function} is the exact emitter-shaped compiler AST")
    if semantic:
        print("  Qed: that exact imported function preserves dsl_denote")


SELFTEST_C = """\
#include <stdint.h>
#include <stddef.h>

extern uint64_t l_Exact_SelfTest(void);
uint64_t l_Exact_SelfTest(void)
{
    uint8_t v_0;
    uint64_t v_1;
    uint64_t v_2;
    uint64_t v_3 = UINT64_C(0);
    v_0 = 0;
    v_1 = UINT64_C(0);
    v_2 = UINT64_C(0);
    v_1 = UINT64_C(7);
    while ((v_3 < UINT64_C(3)))
    {
        v_2 = (v_1 + v_3);
        v_0 = (v_2 < UINT64_C(100));
        v_1 = ((uint64_t)(v_0));
        v_3 = (v_3 + UINT64_C(1));
    }
    return v_1;
}
"""

SELFTEST_SOURCE = """\
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Ctypes Clight.
Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler
  Direct.ClightEmitterCompiler.
Import ListNotations.
Local Open Scope Z_scope.
Definition source_selftest_loop_limit : Z := 3.
Definition source_selftest : dsl_program := {|
  dp_reg_count := 2;
  dp_loop_count := Z.to_nat source_selftest_loop_limit;
  dp_init := [Dmov 0 (Dlit 7)];
  dp_body := [Dbinop 1 Dadd (Dreg 0) Didx;
              Dbinop 0 Dlt (Dreg 1) (Dlit 100)];
  dp_epilogue := [];
  dp_output := 0
|}.
Definition emitter_source_selftest : emitter_source := {|
  es_reg_count := 2;
  es_init := [Dmov 0 (Dlit 7)];
  es_body := [Dbinop 1 Dadd (Dreg 0) Didx;
              Dbinop 0 Dlt (Dreg 1) (Dlit 100)];
  es_epilogue := [];
  es_output := 0
|}.
Lemma emitter_source_selftest_matches :
  emitter_source_matches emitter_source_selftest source_selftest.
Proof. constructor; reflexivity. Qed.
Lemma source_selftest_loop_relation :
  source_selftest_loop_limit =
    Z.of_nat (dp_loop_count source_selftest).
Proof.
  change (3%Z = Z.of_nat (Z.to_nat 3%Z)).
  symmetry. apply Z2Nat.id. lia.
Qed.
Lemma source_selftest_rolled_wf : rolled_wf source_selftest.
Proof. vm_compute; repeat constructor; lia. Qed.
"""


def self_test(
    outdir: Path, compcert: Path, explicit_coqc: str | None,
    syntax_only: bool = False,
    explicit_clightgen: str | None = None,
    timeout_seconds: float = 120.0,
    memory_limit_gib: float = 4.0,
) -> None:
    positive = outdir / "positive"
    positive.mkdir(parents=True, exist_ok=True)
    c_path = outdir / "selftest.c"
    source_path = outdir / "selftest-source.v"
    c_path.write_text(SELFTEST_C)
    source_path.write_text(SELFTEST_SOURCE)
    print("positive control:")
    check(
        c_path, source_path, positive, compcert, explicit_coqc,
        syntax_only=syntax_only,
        explicit_clightgen=explicit_clightgen,
        timeout_seconds=timeout_seconds,
        memory_limit_gib=memory_limit_gib,
    )

    negative = outdir / "negative"
    mutant = outdir / "selftest-mutant.c"
    mutant.write_text(SELFTEST_C.replace("(v_1 + v_3)", "(v_1 - v_3)", 1))
    print("negative control (C Oadd mutated to Osub):")
    try:
        check(
            mutant, source_path, negative, compcert, explicit_coqc,
            syntax_only=syntax_only,
            explicit_clightgen=explicit_clightgen,
            timeout_seconds=timeout_seconds,
            memory_limit_gib=memory_limit_gib,
        )
    except CheckError as exc:
        if "exact full-AST proof failed" not in str(exc):
            raise
        print("  rejected as expected")
    else:
        raise CheckError("negative control was incorrectly accepted")
    print("SELF-TEST RESULT: PASS")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Kernel-check exact rolled C/clightgen/source correspondence"
    )
    parser.add_argument("cert_c", nargs="?")
    parser.add_argument("source_contract", nargs="?")
    parser.add_argument("outdir", nargs="?")
    parser.add_argument("--source-def")
    parser.add_argument("--emitter-source-def")
    parser.add_argument("--function")
    parser.add_argument("--wf-lemma")
    parser.add_argument("--loop-relation")
    parser.add_argument("--source-match")
    parser.add_argument("--compcert", default=DEFAULT_COMPCERT)
    parser.add_argument("--clightgen")
    parser.add_argument("--coqc")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--memory-limit-gib", type=float, default=4.0)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--syntax-only", action="store_true",
        help="prove exact AST equality but skip the generic semantics corollary"
    )
    args = parser.parse_args(argv[1:])
    try:
        if args.self_test:
            target = args.cert_c
            if not target or args.source_contract or args.outdir:
                parser.error("--self-test takes exactly one output directory")
            self_test(
                Path(target).resolve(), Path(args.compcert).resolve(),
                args.coqc, args.syntax_only, args.clightgen,
                args.timeout, args.memory_limit_gib
            )
        else:
            if not args.cert_c or not args.source_contract or not args.outdir:
                parser.error("cert_c, source_contract, and outdir are required")
            check(
                Path(args.cert_c).resolve(),
                Path(args.source_contract).resolve(),
                Path(args.outdir).resolve(),
                Path(args.compcert).resolve(),
                args.coqc,
                requested_source=args.source_def,
                requested_function=args.function,
                requested_wf_lemma=args.wf_lemma,
                requested_loop_relation=args.loop_relation,
                requested_emitter_source=args.emitter_source_def,
                requested_source_match=args.source_match,
                syntax_only=args.syntax_only,
                explicit_clightgen=args.clightgen,
                timeout_seconds=args.timeout,
                memory_limit_gib=args.memory_limit_gib,
            )
        return 0
    except (OSError, CheckError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
