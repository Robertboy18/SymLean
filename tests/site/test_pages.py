# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Compiler-backed regressions for documentation isolation and hover metadata.

Run after building CAS: python3 -m unittest discover -s tests/site -v
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "Site/Tools"))
import sitelean


class PageCompilerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT,
                                           text=True).strip()
        cls.lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                                cwd=ROOT, text=True).strip()

    def compile(self, specifications):
        cells = [sitelean.Cell("test", f"test:{i}", code, mode, **(extra[0] if extra else {}))
                 for i, (mode, code, *extra) in enumerate(specifications)]
        source = sitelean.lean_file([], cells)
        with tempfile.TemporaryDirectory() as tmp:
            runner = sitelean.LeanRunner(ROOT, self.lean, self.lean_path,
                                        Path(tmp) / "cache", Path(tmp) / "work", threads=1)
            result, _ = runner.run_one("test", source, [], cells)
        problems = sitelean.assign_messages("test", cells, result["messages"])
        sitelean.assign_hovers(cells, source, result["hovers"])
        return cells, problems + sitelean.check_cells(cells)

    def test_failed_declaration_cannot_prove_a_later_example(self):
        cells, problems = self.compile([
            ("error", "theorem failed : False := by exact True.intro"),
            ("run", "example : False := failed"),
        ])
        self.assertTrue(problems)
        self.assertTrue(any(m["severity"] == "error" for m in cells[1].messages))

    def test_successful_state_survives_expected_errors(self):
        _, problems = self.compile([
            ("run", "theorem earlier : True := True.intro"),
            ("error", "theorem failed : False := by exact True.intro"),
            ("run", "theorem later : True := earlier"),
            ("run", "example : True := later"),
        ])
        self.assertEqual(problems, [])

    def test_successful_cell_with_a_hole_is_rejected(self):
        with self.assertRaisesRegex(sitelean.CellError, "sorryAx"):
            self.compile([("run", "theorem incomplete : True := by sorry")])

    def test_compiler_types_goals_and_unicode_ranges(self):
        cells, problems = self.compile([
            ("run", "example (θ : ℝ) : θ + 0 = θ := by\n  simp"),
            ("run", "example : Real.exp 0 = 1 := by\n  simp"),
        ])
        self.assertEqual(problems, [])
        self.assertTrue(any(h["text"].startswith("θ : ℝ") for h in cells[0].hovers))
        self.assertTrue(any("Before" in h["text"] and "After\nno goals" in h["text"]
                            for h in cells[0].hovers))
        self.assertTrue(any(h["text"].startswith("Real.exp :") and "\n\n" in h["text"]
                            for h in cells[1].hovers))
        self.assertIn('data-lean-hover=', sitelean.highlight(cells[0].code, cells[0].hovers))

    def test_named_theorem_signature_and_tactic_ranges(self):
        cells, problems = self.compile([
            ("run", "theorem signature_check : ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by\n"
             "  cas\n#print axioms signature_check"),
        ])
        self.assertEqual(problems, [])
        self.assertTrue(any(h["text"].startswith("Real.exp :") for h in cells[0].hovers))
        source = cells[0].code.encode("utf-8")
        cas_terms = [h for h in cells[0].hovers if h["kind"] == "term"
                     and source[h["start"]:h["end"]] == b"cas"]
        self.assertEqual(cas_terms, [])

    def test_expected_output_is_checked(self):
        # The page compiler evaluates native certificates; a cell that misses its text is reported.
        expect = {"expect": "_native.cegaFast.ax"}
        _, problems = self.compile([
            ("run", "set_option cega.nativeCertificates true in\n"
             "theorem native_rows : ∀ i : Fin 16, (i.val : ℤ) ^ 2 < 256 := by\n  cega [fast]\n"
             "#print axioms native_rows", expect),
            ("run", "theorem kernel_rows : ∀ i : Fin 8, (i.val : ℤ) ^ 2 < 64 := by\n  cega [fast]\n"
             "#print axioms kernel_rows", expect),
        ])
        self.assertEqual(problems, ["test:1: the output does not contain '_native.cegaFast.ax'"])

    def test_query_hover_does_not_show_internal_tactic_goals(self):
        cells, problems = self.compile([("run", "#cas [derive x] (x ^ 2)")])
        self.assertEqual(problems, [])
        self.assertTrue(any(h["kind"] == "command" and "derive" in h["text"]
                            for h in cells[0].hovers))
        self.assertFalse(any(h["kind"] == "tactic" for h in cells[0].hovers))


if __name__ == "__main__":
    unittest.main()
