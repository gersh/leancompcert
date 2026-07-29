from __future__ import annotations

import os
import subprocess
import time
from pathlib import Path

from .model import CommandResult


def run_command(
    stage: str,
    command: list[str],
    cwd: Path,
    timeout: float,
    env: dict[str, str] | None = None,
) -> CommandResult:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            env=env if env is not None else os.environ.copy(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        return CommandResult(
            stage=stage,
            command=command,
            exit_code=completed.returncode,
            stdout=completed.stdout,
            stderr=completed.stderr,
            duration_ms=round((time.monotonic() - started) * 1000),
        )
    except FileNotFoundError as error:
        return CommandResult(
            stage=stage,
            command=command,
            exit_code=None,
            stdout="",
            stderr=str(error),
            duration_ms=round((time.monotonic() - started) * 1000),
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, str) else ""
        stderr = error.stderr if isinstance(error.stderr, str) else ""
        return CommandResult(
            stage=stage,
            command=command,
            exit_code=None,
            stdout=stdout,
            stderr=f"{stderr}\ncommand timed out after {timeout:g}s".strip(),
            duration_ms=round((time.monotonic() - started) * 1000),
        )
