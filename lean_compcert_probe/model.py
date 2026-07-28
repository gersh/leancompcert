from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import StrEnum
from typing import Any


class FailureClass(StrEnum):
    COMMAND_LINE = "command-line incompatibility"
    C_SYNTAX = "unsupported C syntax"
    ATTRIBUTE = "unsupported attribute"
    HEADER = "unsupported header"
    RUNTIME = "runtime dependency"
    ASSEMBLER_LINKER = "assembler or linker issue"
    TOOL_UNAVAILABLE = "tool unavailable"
    LEAN_EMISSION = "Lean C emission failure"
    UNKNOWN = "unclassified"


@dataclass(frozen=True)
class CommandResult:
    stage: str
    command: list[str]
    exit_code: int | None
    stdout: str
    stderr: str
    duration_ms: int
    classification: FailureClass | None = None

    @property
    def succeeded(self) -> bool:
        return self.exit_code == 0

    def as_dict(self) -> dict[str, Any]:
        value = asdict(self)
        if self.classification is not None:
            value["classification"] = self.classification.value
        return value


@dataclass
class ProbeReport:
    schema_version: int
    backend_version: str
    input: str
    output_directory: str
    lean_version: str | None
    lean_git_revision: str | None
    compcert_version: str | None
    compcert_target: str | None
    generated_c: list[str] = field(default_factory=list)
    rewritten_c: list[str] = field(default_factory=list)
    compcert_compiled: list[str] = field(default_factory=list)
    conventionally_compiled: list[str] = field(default_factory=list)
    reference_artifacts: list[str] = field(default_factory=list)
    external_components: list[str] = field(default_factory=list)
    commands: list[CommandResult] = field(default_factory=list)
    failures: dict[str, list[str]] = field(default_factory=dict)
    differential_match: bool | None = None
    status: str = "failed"

    def as_dict(self) -> dict[str, Any]:
        return {
            "schemaVersion": self.schema_version,
            "backendVersion": self.backend_version,
            "input": self.input,
            "outputDirectory": self.output_directory,
            "leanVersion": self.lean_version,
            "leanGitRevision": self.lean_git_revision,
            "compcertVersion": self.compcert_version,
            "compcertTarget": self.compcert_target,
            "generatedC": self.generated_c,
            "rewrittenC": self.rewritten_c,
            "compCertCompiled": self.compcert_compiled,
            "conventionallyCompiled": self.conventionally_compiled,
            "referenceArtifacts": self.reference_artifacts,
            "externalComponents": self.external_components,
            "commands": [command.as_dict() for command in self.commands],
            "failures": self.failures,
            "differentialMatch": self.differential_match,
            "status": self.status,
        }
