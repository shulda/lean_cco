import json
from pathlib import Path
import tempfile
import unittest

from verify_project_cache import inspect_metadata, invalidate, mismatched_modules


class CacheConsistencyTests(unittest.TestCase):
    def make_module(self, build, module, descriptor='0123456789abcdef.olean'):
        stem = build / 'lib/lean' / module
        stem.parent.mkdir(parents=True, exist_ok=True)
        trace = stem.with_suffix('.trace')
        trace.write_text(json.dumps({'outputs': {'o': [descriptor]}}))
        stem.with_suffix('.olean').write_bytes(b'output')
        return stem, trace

    def test_root_and_child_traces_are_both_checked(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp)
            root, _ = self.make_module(build, 'CCO')
            child, _ = self.make_module(build, 'CCO/A')
            expected, bad = inspect_metadata(build)
            self.assertEqual(set(expected), {root.with_suffix('.olean'), child.with_suffix('.olean')})
            self.assertFalse(bad)
            stale = {**expected, child.with_suffix('.olean'): 'fedcba9876543210'}
            self.assertEqual(mismatched_modules(expected, stale), {child.with_suffix('.trace')})

    def test_repair_preserves_valid_modules_and_source(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp) / '.lake/build'
            stale, trace = self.make_module(build, 'CCO/A')
            valid, _ = self.make_module(build, 'CCO/B')
            source = Path(temp) / 'CCO/A.lean'
            source.parent.mkdir(); source.write_text('source')
            ir = build / 'ir/CCO/A.c'; ir.parent.mkdir(parents=True); ir.write_text('generated')
            invalidate(build, {trace})
            self.assertFalse(stale.with_suffix('.olean').exists())
            self.assertFalse(ir.exists())
            self.assertTrue(valid.with_suffix('.olean').exists())
            self.assertEqual(source.read_text(), 'source')

    def test_missing_output_and_malformed_trace_are_invalidated(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp)
            stem, trace = self.make_module(build, 'CCO/A')
            stem.with_suffix('.olean').unlink()
            _, malformed = self.make_module(build, 'CCO/B')
            malformed.write_text('{broken')
            _, invalid = inspect_metadata(build)
            self.assertEqual(invalid, {trace, malformed})

    def test_unsupported_descriptor_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp)
            _, trace = self.make_module(build, 'CCO/A', '../../source.lean')
            _, invalid = inspect_metadata(build)
            self.assertEqual(invalid, {trace})

    def test_absent_cache_is_valid(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(inspect_metadata(Path(temp)), ({}, set()))


if __name__ == '__main__':
    unittest.main()
