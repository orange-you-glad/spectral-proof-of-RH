import sys
import tempfile
from pathlib import Path
import unittest

sys.path.append(str(Path(__file__).resolve().parents[1] / "scripts"))

import validate_labels
import check_proofs
import check_structure


class ValidateLabelsTests(unittest.TestCase):
    def test_validate_labels_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tex_file = Path(tmpdir) / "thm_example.tex"
            tex_file.write_text("\\section{X}\n\\label{thm:example}\n")
            old_root = validate_labels.ROOT_DIR
            validate_labels.ROOT_DIR = tmpdir
            try:
                validate_labels.validate_labels()
            except SystemExit as e:
                self.fail(f"validate_labels exited {e}")
            finally:
                validate_labels.ROOT_DIR = old_root


class ProofCheckerTests(unittest.TestCase):
    def test_check_proofs_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            chapters = Path(tmpdir)
            section = chapters / "01_test"
            (section / "thms").mkdir(parents=True)
            (section / "proofs").mkdir(parents=True)
            (section / "lems").mkdir()
            (section / "props").mkdir()
            (section / "cors").mkdir()
            (section / "defs").mkdir()
            (section / "rems").mkdir()
            (section / "intro.tex").write_text("Intro")
            (section / "summary.tex").write_text("Summary")
            (section / "test.tex").write_text("Main")
            thm = section / "thms" / "thm_example.tex"
            thm.write_text("\\label{thm:example}")
            prf = section / "proofs" / "prf_thm_example.tex"
            prf.write_text("proof")

            old_root = check_proofs.ROOT_DIR
            check_proofs.ROOT_DIR = str(chapters)
            try:
                check_proofs.check_proofs()
            except SystemExit as e:
                self.fail(f"check_proofs exited {e}")
            finally:
                check_proofs.ROOT_DIR = old_root


class StructureCheckerTests(unittest.TestCase):
    def test_check_structure_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            chapters = Path(tmpdir)
            section = chapters / "01_test"
            (section / "thms").mkdir(parents=True)
            (section / "proofs").mkdir()
            (section / "lems").mkdir()
            (section / "props").mkdir()
            (section / "cors").mkdir()
            (section / "defs").mkdir()
            (section / "rems").mkdir()
            (section / "intro.tex").write_text("Intro")
            (section / "summary.tex").write_text("Summary")
            (section / "test.tex").write_text("Main")
            old_root = check_structure.ROOT_DIR
            check_structure.ROOT_DIR = str(chapters)
            try:
                check_structure.check_all_sections()
            except SystemExit as e:
                self.fail(f"check_structure exited {e}")
            finally:
                check_structure.ROOT_DIR = old_root


if __name__ == "__main__":
    unittest.main()
