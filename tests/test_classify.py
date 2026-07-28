import unittest

from lean_compcert_probe.classify import classify_failure, minimize_diagnostics
from lean_compcert_probe.model import FailureClass


class ClassifyTests(unittest.TestCase):
    def test_classifies_required_failure_categories(self) -> None:
        examples = {
            "ccomp: unknown option '-MMD'": FailureClass.COMMAND_LINE,
            "warning: unsupported attribute 'noreturn'": FailureClass.ATTRIBUTE,
            "fatal error: bits/foo.h: No such file": FailureClass.HEADER,
            "undefined reference to lean_alloc_ctor": FailureClass.RUNTIME,
            "linker failed: relocation truncated": FailureClass.ASSEMBLER_LINKER,
            "syntax error before '__asm__'": FailureClass.C_SYNTAX,
        }
        for diagnostic, expected in examples.items():
            with self.subTest(diagnostic=diagnostic):
                self.assertEqual(classify_failure(diagnostic, "compcert-compile"), expected)

    def test_minimizes_and_deduplicates_diagnostics(self) -> None:
        diagnostic = """
          source.c:1: error: unsupported syntax
          source.c:1: error: unsupported syntax
          irrelevant context
          source.c:2: warning: ignored attribute
        """
        self.assertEqual(
            minimize_diagnostics(diagnostic),
            [
                "source.c:1: error: unsupported syntax",
                "source.c:2: warning: ignored attribute",
            ],
        )


if __name__ == "__main__":
    unittest.main()
