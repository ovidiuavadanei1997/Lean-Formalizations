"""Regression checks for the source scanner and release checksum boundary."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_source import code, code_hash
from check_release import check, ROOT
import verify


class SourceChecks(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = 'module\n/- outer /- sorry -/ tail -/\ndef x := "-- /-"\n'
        self.assertNotIn('sorry', code(text))
        self.assertIn('"-- /-"', code(text))

    def test_comment_changes_preserve_code(self):
        self.assertEqual(code_hash('def x := 1 /- note -/'), code_hash('def x := 1'))
        self.assertNotEqual(code_hash('def x := 1'), code_hash('def x := 2'))
        self.assertNotEqual(code_hash('def x := "a b"'), code_hash('def x := "ab"'))
        self.assertNotEqual(code_hash('def x := a b'), code_hash('def x := ab'))

    def test_primed_names(self):
        self.assertEqual(code_hash("theorem f' := f /- note -/"), code_hash("theorem f' := f"))

    def test_bad_comments_fail_closed(self):
        with self.assertRaises(ValueError):
            code('module /- unfinished')

    def test_checksum_tamper_rejected(self):
        target = ROOT / 'ClockBarrier.lean'
        original = Path.read_bytes

        def altered(p):
            return original(p) + b'\n' if p == target else original(p)

        with patch.object(Path, 'read_bytes', altered):
            with self.assertRaisesRegex(ValueError, 'checksum'):
                check()

    def test_source_snapshot_passes(self):
        self.assertEqual(check()['status'], 'PASS')

    def test_symlinked_artifact_parent_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve() / 'project'
            outside = Path(tmp).resolve() / 'other'
            root.mkdir()
            outside.mkdir()
            (root / '.lake').symlink_to(outside, target_is_directory=True)
            with patch.object(verify, 'ROOT', root):
                with self.assertRaises(RuntimeError):
                    verify.require_local_directory(root / '.lake/build')

    def test_failed_rerun_overwrites_previous_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            output = root / '.verification'
            output.mkdir()
            result = output / 'result.json'
            result.write_text('{"status":"PASS"}')
            with patch.object(verify, 'ROOT', root), patch('sys.argv', ['verify.py']), \
                    patch.object(verify, 'run_checks', side_effect=RuntimeError('test failure')):
                with self.assertRaisesRegex(RuntimeError, 'test failure'):
                    verify.main()
            self.assertEqual(json.loads(result.read_text())['status'], 'FAIL')


if __name__ == '__main__':
    unittest.main()
