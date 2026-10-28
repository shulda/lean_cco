import tempfile
from pathlib import Path
import unittest

from mathlib_cache_roots import cache_roots, imports


class CacheRootTests(unittest.TestCase):
    def test_header_comments_and_multiple_names(self):
        text = '''/- import Mathlib
        /- nested import Mathlib.Tactic -/ -/
        module
        public import CCO.A Mathlib.Data.Fintype.Basic -- import Mathlib
        import Lean.Elab.Tactic.Omega
        namespace Example
        import Mathlib.Tactic
        '''
        self.assertEqual(imports(text), [
            'CCO.A', 'Mathlib.Data.Fintype.Basic', 'Lean.Elab.Tactic.Omega'])

    def test_follows_local_edges_and_deduplicates_cycles(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'CCO').mkdir()
            (root / 'CCO.lean').write_text('import CCO.A\n')
            (root / 'CCO/A.lean').write_text('import CCO.B\nimport Mathlib.Data.Fintype.Basic\n')
            (root / 'CCO/B.lean').write_text('import CCO.A\nimport Mathlib.Tactic.Ext\n')
            external, local = cache_roots(root)
            self.assertEqual(external, ['Mathlib.Data.Fintype.Basic', 'Mathlib.Tactic.Ext'])
            self.assertEqual(local, ['CCO', 'CCO.A', 'CCO.B'])

    def test_missing_or_unrecognized_import_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'CCO.lean').write_text('import CCO.Absent\n')
            with self.assertRaisesRegex(ValueError, 'missing project module'):
                cache_roots(root)
            (root / 'CCO.lean').write_text('import Unknown.Library\n')
            with self.assertRaisesRegex(ValueError, 'unrecognized external import'):
                cache_roots(root)

    def test_unterminated_block_comment_fails(self):
        with self.assertRaisesRegex(ValueError, 'unterminated'):
            imports('/- unfinished')


if __name__ == '__main__':
    unittest.main()
