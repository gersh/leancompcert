from __future__ import annotations

import re

from .model import FailureClass


_RULES: tuple[tuple[FailureClass, tuple[str, ...]], ...] = (
    (
        FailureClass.COMMAND_LINE,
        (
            r"\bunknown (?:command line )?option\b",
            r"\bunrecognized (?:command line )?option\b",
            r"\billegal option\b",
            r"\bunknown argument\b",
            r"\bunsupported option\b",
        ),
    ),
    (
        FailureClass.ATTRIBUTE,
        (
            r"\bunknown attribute\b",
            r"\bunsupported attribute\b",
            r"__attribute__",
            r"__declspec",
        ),
    ),
    (
        FailureClass.HEADER,
        (
            r"\b(?:fatal error|error): [^:\n]+(?:\.h)?[:'\" ]+no such file",
            r"\bcannot find (?:include|header)\b",
            r"\bunsupported (?:system )?header\b",
        ),
    ),
    (
        FailureClass.RUNTIME,
        (
            r"\bundefined reference\b",
            r"\bunresolved external\b",
            r"\bunknown runtime symbol\b",
            r"\blean_[a-z0-9_]+\b.*\b(?:undefined|unresolved|missing)\b",
        ),
    ),
    (
        FailureClass.ASSEMBLER_LINKER,
        (
            r"\b(?:assembler|linker) (?:error|failed)\b",
            r"\bld(?:\.[a-z]+)?: .*error\b",
            r"\bcollect2: error\b",
            r"\brelocation .* (?:failed|truncated)\b",
        ),
    ),
    (
        FailureClass.C_SYNTAX,
        (
            r"\bsyntax error\b",
            r"\bparse error\b",
            r"\bunsupported (?:c )?(?:syntax|construct|extension)\b",
            r"\bexpected ['\"].+['\"]\b",
            r"\binitializer element is not a compile-time constant\b",
        ),
    ),
)


def classify_failure(stderr: str, stage: str) -> FailureClass:
    if stage.startswith("lean-emission"):
        return FailureClass.LEAN_EMISSION
    text = stderr.lower()
    for category, patterns in _RULES:
        if any(re.search(pattern, text, flags=re.IGNORECASE) for pattern in patterns):
            return category
    if stage.startswith("link") or stage == "run-compcert":
        return FailureClass.ASSEMBLER_LINKER
    return FailureClass.UNKNOWN


def minimize_diagnostics(text: str, limit: int = 12) -> list[str]:
    """Keep unique, useful diagnostic lines in original order."""
    selected: list[str] = []
    seen: set[str] = set()
    for raw_line in text.splitlines():
        line = " ".join(raw_line.strip().split())
        if not line or line in seen:
            continue
        if any(
            marker in line.lower()
            for marker in ("error", "warning", "unsupported", "unknown", "undefined", "fatal")
        ):
            seen.add(line)
            selected.append(line)
            if len(selected) == limit:
                break
    if not selected:
        for raw_line in text.splitlines():
            line = " ".join(raw_line.strip().split())
            if line and line not in seen:
                seen.add(line)
                selected.append(line)
                if len(selected) == limit:
                    break
    return selected
