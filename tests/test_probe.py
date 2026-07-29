from __future__ import annotations

import json
import stat
import tempfile
import unittest
from pathlib import Path

from lean_compcert_probe.cli import main as probe_main
from lean_compcert_probe.probe import run_probe


def _executable(path: Path, text: str) -> Path:
    path.write_text(text, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class ProbeTests(unittest.TestCase):
    def test_successful_fixture_probe(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            source = tmp_path / "Main.lean"
            source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            fake_lean = _executable(
                tmp_path / "lean",
                """#!/bin/sh
case "$1" in
  --version) echo "Lean (version 4.test)" ;;
  -g) echo "deadbeef" ;;
  --print-prefix) echo "/opt/lean" ;;
  -c) printf '#include <stdint.h>\\nint generated(void) { return 0; }\\n' > "$2" ;;
esac
""",
            )
            fake_ccomp = _executable(
                tmp_path / "ccomp",
                """#!/bin/sh
if [ "$1" = "-version" ]; then echo "CompCert 3.test"; exit 0; fi
exit 0
""",
            )

            output = tmp_path / "report"
            report = run_probe(
                source, output, lean=str(fake_lean), ccomp=str(fake_ccomp)
            )

            self.assertEqual(report.status, "compatible")
            self.assertEqual(report.lean_version, "Lean (version 4.test)")
            self.assertEqual(report.compcert_version, "CompCert 3.test")
            self.assertIn("ccomp default", report.compcert_target or "")
            payload = json.loads((output / "report.json").read_text(encoding="utf-8"))
            self.assertEqual(payload["status"], "compatible")
            self.assertTrue((output / "report.md").is_file())

    def test_missing_compcert_is_an_incomplete_probe(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            source = tmp_path / "Main.lean"
            source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            fake_lean = _executable(
                tmp_path / "lean",
                """#!/bin/sh
case "$1" in
  --version) echo "Lean test" ;;
  -g) echo "revision" ;;
  -c) echo 'int x;' > "$2" ;;
esac
""",
            )
            report = run_probe(
                source,
                tmp_path / "out",
                lean=str(fake_lean),
                ccomp="definitely-not-installed-ccomp",
            )
            self.assertEqual(report.status, "probe-incomplete")
            self.assertIn("tool unavailable", report.failures)

    def test_cli_exit_code_distinguishes_incomplete_from_success(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            source = tmp_path / "Main.lean"
            source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            fake_lean = _executable(
                tmp_path / "lean",
                """#!/bin/sh
case "$1" in
  --version) echo "Lean test" ;;
  -g) echo "revision" ;;
  -c) echo 'int x;' > "$2" ;;
esac
""",
            )
            exit_code = probe_main(
                [
                    str(source),
                    "--output",
                    str(tmp_path / "out"),
                    "--lean",
                    str(fake_lean),
                    "--ccomp",
                    "definitely-not-installed-ccomp",
                ]
            )
            self.assertEqual(exit_code, 3)

    def test_matching_nonzero_execution_is_valid(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            source = tmp_path / "Main.lean"
            source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            fake_lean = _executable(
                tmp_path / "lean",
                """#!/bin/sh
case "$1" in
  --version) echo "Lean test" ;;
  -g) echo "revision" ;;
  --print-prefix) echo "/opt/lean" ;;
  -c) echo 'int x;' > "$2" ;;
esac
""",
            )
            fake_ccomp = _executable(
                tmp_path / "ccomp",
                """#!/bin/sh
if [ "$1" = "-version" ]; then echo "CompCert test"; fi
exit 0
""",
            )
            exits_seven = _executable(
                tmp_path / "exits-seven",
                "#!/bin/sh\necho same\nexit 7\n",
            )
            report = run_probe(
                source,
                tmp_path / "out",
                lean=str(fake_lean),
                ccomp=str(fake_ccomp),
                reference_command=str(exits_seven),
                candidate_command=str(exits_seven),
            )
            self.assertEqual(report.status, "compatible")
            self.assertTrue(report.differential_match)
            self.assertNotIn("unclassified", report.failures)

    def test_automatic_differential_pipeline(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tmp_path = Path(directory)
            source = tmp_path / "Main.lean"
            source.write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            fake_install = tmp_path / "lean-install"
            (fake_install / "bin").mkdir(parents=True)
            (fake_install / "include").mkdir()
            fake_lean = _executable(
                tmp_path / "lean",
                f"""#!/bin/sh
case "$1" in
  --version) echo "Lean test" ;;
  -g) echo "revision" ;;
  --print-prefix) echo "{fake_install}" ;;
  -c) echo 'int generated;' > "$2" ;;
esac
""",
            )
            output_writer = """output=''
previous=''
for argument in "$@"; do
  if [ "$previous" = "-o" ]; then output="$argument"; fi
  previous="$argument"
done
case "$output" in
  *.standard|*.compcert)
    printf '#!/bin/sh\\necho identical\\nexit 0\\n' > "$output"
    chmod +x "$output"
    ;;
  *) : > "$output" ;;
esac
"""
            _executable(
                fake_install / "bin" / "leanc",
                f"#!/bin/sh\n{output_writer}",
            )
            fake_ccomp = _executable(
                tmp_path / "ccomp",
                f"""#!/bin/sh
if [ "$1" = "-version" ]; then echo "CompCert test"; exit 0; fi
{output_writer}
""",
            )
            report = run_probe(
                source,
                tmp_path / "out",
                lean=str(fake_lean),
                ccomp=str(fake_ccomp),
                differential_check=True,
            )
            self.assertEqual(report.status, "compatible")
            self.assertTrue(report.differential_match)
            self.assertIn("link-reference", [step.stage for step in report.commands])
            self.assertIn("link-compcert", [step.stage for step in report.commands])
            self.assertEqual(report.reference_artifacts, ["out/Main.lean.c"])
            self.assertNotIn("out/Main.lean.c", report.conventionally_compiled)
            self.assertTrue(
                any(
                    item.endswith("runtime/adapters/atomics.c")
                    for item in report.conventionally_compiled
                )
            )


if __name__ == "__main__":
    unittest.main()
