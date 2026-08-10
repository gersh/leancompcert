#!/usr/bin/env python3
"""Split one generated 10-micro Section 4.1.3 chunk behind its old API.

Use this after a serialized 1.5 GiB build identifies an oversized shard or a
generated suffix whose single-shard footprint leaves unsafe headroom.
The two generated halves retain five kernel-decided micro traces each, while
the original module name becomes a small compatibility wrapper exporting
`state00`, `state10`, `words`, and `segment`.
"""

from pathlib import Path
import re
import sys


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: split_section413_window_chunk.py PATH/ChunkNNN.lean")

    path = Path(sys.argv[1])
    text = path.read_text()
    match = re.search(
        r"^namespace (LeanCompCert\.Ports\.Section413WindowKGenerated\."
        r"(G[12])\.(Chunk\d{3}))$",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"cannot find generated chunk namespace in {path}")
    namespace, kind, chunk = match.groups()
    if f"{chunk}A" in text or f"{chunk}B" in text:
        raise SystemExit(f"{path} already appears split")

    split_marker = "\ndef state06 :"
    split_at = text.find(split_marker)
    if split_at < 0:
        raise SystemExit(f"cannot find state06 split point in {path}")
    end_marker = f"\nend {namespace}"
    end_at = text.rfind(end_marker)
    if end_at < split_at:
        raise SystemExit(f"cannot find namespace end in {path}")

    statement_match = re.search(
        r"theorem segment :(.*?) := by", text, re.DOTALL
    )
    if statement_match is None:
        raise SystemExit(f"cannot find segment theorem in {path}")
    segment_type = statement_match.group(1).rstrip()

    a_namespace = f"{namespace}A"
    b_namespace = f"{namespace}B"
    a_text = text[:split_at].replace(namespace, a_namespace, 1).rstrip()
    a_text += f"\n\nend {a_namespace}\n"

    suffix = text[split_at + 1 : end_at].rstrip()
    b_text = (
        f"import {a_namespace}\n\n"
        f"namespace {b_namespace}\n\n"
        "open LeanCompCert.Ports.Section413Sweep\n"
        "open LeanCompCert.Ports.Section413WindowRuntime\n"
        "open LeanCompCert.Ports.Section413WindowDirectTables\n"
        f"open {a_namespace}\n\n"
        f"{suffix}\n\nend {b_namespace}\n"
    )

    wrapper = (
        f"import {b_namespace}\n\n"
        f"namespace {namespace}\n\n"
        "open LeanCompCert.Ports.Section413Sweep\n"
        "open LeanCompCert.Ports.Section413WindowRuntime\n"
        "open LeanCompCert.Ports.Section413WindowDirectTables\n\n"
        f"def state00 : KState :=\n  {a_namespace}.state00\n\n"
        f"def state10 : KState :=\n  {b_namespace}.state10\n\n"
        f"def words : List Nat :=\n  {b_namespace}.words\n\n"
        f"theorem segment :{segment_type} := by\n"
        "  simpa [state00, state10, words] using\n"
        f"    {b_namespace}.segment\n\n"
        f"end {namespace}\n"
    )

    a_path = path.with_name(f"{chunk}A.lean")
    b_path = path.with_name(f"{chunk}B.lean")
    if a_path.exists() or b_path.exists():
        raise SystemExit(f"refusing to overwrite {a_path} or {b_path}")
    a_path.write_text(a_text)
    b_path.write_text(b_text)
    path.write_text(wrapper)


if __name__ == "__main__":
    main()
