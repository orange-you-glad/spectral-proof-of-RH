import sys
import tempfile
from pathlib import Path
import unittest

sys.path.append(str(Path(__file__).resolve().parents[1] / "scripts"))

import validate_labels


class ValidateLabelsTest(unittest.TestCase):
    def test_validate_labels_no_errors(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tex_file = Path(tmpdir) / "thm_example.tex"
            tex_file.write_text("\\section{Test}\n\\label{thm:example}\n")

            old_root = validate_labels.ROOT_DIR
            validate_labels.ROOT_DIR = tmpdir
            try:
                validate_labels.validate_labels()
            except SystemExit as e:
                self.fail(f"validate_labels exited unexpectedly: {e}")
            finally:
                validate_labels.ROOT_DIR = old_root


if __name__ == "__main__":
    unittest.main()
