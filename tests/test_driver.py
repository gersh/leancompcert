from __future__ import annotations

import json
import stat
import tempfile
import unittest
from pathlib import Path

from lean_compcert_driver.cli import _insert_capture_import, _validate_mode
from lean_compcert_driver.manifest import abi_manifest, runtime_hash, write_build_manifest
from lean_compcert_driver.runtime_check import check_runtime
from lean_compcert_probe.model import ProbeReport


class DriverTests(unittest.TestCase):
    def test_runtime_mode_validation(self) -> None:
        self.assertIsNone(_validate_mode("portable", "hybrid"))
        self.assertIn("selected together", _validate_mode("strict", "hybrid") or "")
        self.assertIn("not complete", _validate_mode("strict", "strict") or "")

    def test_capture_import_respects_module_header(self) -> None:
        source = "module\nimport Init\n\ndef x := 1\n"
        derived = _insert_capture_import(source)
        self.assertTrue(
            derived.startswith("module\nimport LeanCompCert.CompilerAdapter.Pass\n")
        )

    def test_check_runtime_fails_without_runtime_sources(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "empty-root"
            root.mkdir()
            fake_ccomp = root / "ccomp"
            fake_ccomp.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_ccomp.chmod(fake_ccomp.stat().st_mode | stat.S_IXUSR)
            compatible, payload = check_runtime(
                root, Path(directory) / "out", str(fake_ccomp), None, 10
            )
            self.assertFalse(compatible)
            self.assertEqual(payload["status"], "runtime-missing")

    def test_runtime_hash_requires_runtime_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                runtime_hash(Path(directory))

    def test_manifest_contains_assurance_boundary(self) -> None:
        root = Path(__file__).resolve().parents[1]
        report = ProbeReport(
            schema_version=1,
            backend_version="0.1.0",
            input="Main.lean",
            output_directory="build",
            lean_version="Lean test",
            lean_git_revision="lean-revision",
            compcert_version="CompCert test",
            compcert_target="test-target",
            status="compatible",
        )
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "manifest.json"
            write_build_manifest(
                root, report, destination, "portable", "hybrid"
            )
            payload = json.loads(destination.read_text(encoding="utf-8"))
            self.assertEqual(payload["pipeline"], "normalized-lean-c")
            self.assertIn("C-to-assembly", payload["assuranceBoundary"])
            self.assertEqual(payload["runtimeAbiHash"], runtime_hash(root))
            self.assertEqual(payload["externalObjects"], [])
            self.assertEqual(payload["referenceArtifacts"], [])
            self.assertEqual(payload["runtimeAbi"], abi_manifest(root, "Lean test"))
            self.assertTrue((destination.parent / "abi-manifest.json").is_file())


if __name__ == "__main__":
    unittest.main()
