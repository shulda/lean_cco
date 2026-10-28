import json
from pathlib import Path
import tempfile
import unittest

from clear_project_cache import clear_project_artifacts
from verify_project_cache import (inspect_metadata, invalidate, mismatched_modules,
                                  mismatched_sources, source_trace_hash)


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

    def source_entry(self, project, relative='CCO.lean', imports=None):
        imports = imports if imports is not None else [{'module': 'CCO.Child', 'isMeta': False}]
        return {'source': str(project / relative), 'sourceHash': 'current-source',
                'imports': imports, 'isModule': False, 'compiledImports': imports,
                'compiledIsModule': False, 'readError': None,
                'resolvedOlean': str((project / '.lake/build/lib/lean' / relative).with_suffix('.olean'))}

    def source_trace(self, build, relative, source_hash='current-source'):
        trace = (build / 'lib/lean' / relative).with_suffix('.trace')
        trace.parent.mkdir(parents=True, exist_ok=True)
        trace.write_text(json.dumps({'inputs': [['/previous/worktree/' + relative, source_hash]]}))
        return trace

    def test_consistent_output_bytes_do_not_hide_stale_root_or_child_imports(self):
        # The observed failure: current source input, old olean header, and
        # an output descriptor which correctly describes those old bytes.
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            entries = [self.source_entry(project, rel) for rel in ['CCO.lean', 'CCO/A.lean']]
            traces = {self.source_trace(build, rel) for rel in ['CCO.lean', 'CCO/A.lean']}
            for entry in entries:
                entry['compiledImports'] = []
            self.assertEqual(set(mismatched_sources(project, build, entries)), traces)

    def test_source_change_with_unchanged_imports_requires_rebuild(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            trace = self.source_trace(build, 'CCO.lean', 'previous-source')
            entry = self.source_entry(project)
            self.assertEqual(set(mismatched_sources(project, build, [entry])), {trace})

    def test_cold_cache_allowed_only_before_complete_check(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            entry = self.source_entry(project, 'CCO/Missing.lean')
            entry['compiledImports'] = None; entry['compiledIsModule'] = None
            self.assertFalse(mismatched_sources(project, build, [entry]))
            self.assertTrue(mismatched_sources(project, build, [entry], require_complete=True))
            entry['readError'] = 'bad olean'
            self.assertTrue(mismatched_sources(project, build, [entry]))

    def test_moved_worktree_input_matches_and_import_flags_are_checked(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            trace = self.source_trace(build, 'CCO.lean')
            entry = self.source_entry(project)
            self.assertEqual(source_trace_hash(trace, Path('CCO.lean')), 'current-source')
            self.assertFalse(mismatched_sources(project, build, [entry], require_complete=True))
            entry['compiledImports'] = [{'module': 'CCO.Child', 'isMeta': True}]
            self.assertEqual(set(mismatched_sources(project, build, [entry])), {trace})

    def test_audit_resolution_cannot_shadow_checked_artifact(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            trace = self.source_trace(build, 'CCO.lean')
            entry = self.source_entry(project)
            entry['resolvedOlean'] = '/another/worktree/CCO.olean'
            self.assertEqual(set(mismatched_sources(project, build, [entry])), {trace})

    def test_same_artifact_through_valid_symlink_is_not_shadowing(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            trace = self.source_trace(build, 'CCO.lean')
            expected = trace.with_suffix('.olean')
            target = project / 'shared/CCO.olean'
            target.parent.mkdir(); target.write_bytes(b'compiled output')
            expected.symlink_to(target)
            entry = self.source_entry(project)
            # Lean reports the logical own-worktree path. Resolving either
            # that path or an equivalent alias must identify the same bytes.
            self.assertFalse(mismatched_sources(project, build, [entry], require_complete=True))
            entry['resolvedOlean'] = str(target)
            self.assertFalse(mismatched_sources(project, build, [entry], require_complete=True))
            different = project / 'other/CCO.olean'
            different.parent.mkdir(); different.write_bytes(b'different artifact')
            entry['resolvedOlean'] = str(different)
            self.assertEqual(set(mismatched_sources(project, build, [entry])), {trace})

    def test_finite_source_paths_check_bytes_behind_nested_directory_alias(self):
        with tempfile.TemporaryDirectory() as temp:
            build = Path(temp) / 'build'
            child, trace = self.make_module(build, 'CCO/Nested/Child')
            target = Path(temp) / 'shared-children'
            child.parent.rename(target)
            child.parent.symlink_to(target, target_is_directory=True)
            # A loop is harmless because only the exact source-reachable
            # trace is opened; recursive symlink following is never enabled.
            (target / 'loop').symlink_to(target, target_is_directory=True)
            omitted, _ = inspect_metadata(build)
            self.assertNotIn(child.with_suffix('.olean'), omitted)
            expected, bad = inspect_metadata(build, [trace])
            self.assertFalse(bad)
            self.assertIn(child.with_suffix('.olean'), expected)
            wrong_bytes = {path: 'fedcba9876543210' for path in expected}
            self.assertEqual(mismatched_modules(expected, wrong_bytes), {trace})

    def test_clean_fallback_preserves_sources_packages_and_alias_targets(self):
        with tempfile.TemporaryDirectory() as temp:
            project = Path(temp); build = project / '.lake/build'
            root, _ = self.make_module(build, 'CCO')
            child, _ = self.make_module(build, 'CCO/Nested/Child')
            target = project / 'shared-output'
            child.parent.rename(target)
            child.parent.symlink_to(target, target_is_directory=True)
            source = project / 'CCO/Source.lean'
            source.parent.mkdir(); source.write_text('source')
            package = project / '.lake/packages/mathlib/Keep.olean'
            package.parent.mkdir(parents=True); package.write_bytes(b'package')
            other = build / 'lib/lean/Other.olean'; other.write_bytes(b'other')
            ir = build / 'ir/CCO.c'; ir.parent.mkdir(); ir.write_bytes(b'generated')
            clear_project_artifacts(build)
            self.assertFalse(root.with_suffix('.olean').exists())
            self.assertFalse((build / 'lib/lean/CCO').exists())
            self.assertFalse(ir.exists())
            self.assertTrue((target / 'Child.olean').is_file())
            self.assertEqual(source.read_text(), 'source')
            self.assertEqual(package.read_bytes(), b'package')
            self.assertEqual(other.read_bytes(), b'other')

    def test_partial_repair_never_unlinks_files_through_directory_alias(self):
        for alias_tree in ['lib/lean', 'ir']:
            with self.subTest(alias_tree=alias_tree), tempfile.TemporaryDirectory() as temp:
                build = Path(temp) / 'build'
                child, trace = self.make_module(build, 'CCO/Nested/Child')
                ir = build / 'ir/CCO/Nested/Child.c'
                ir.parent.mkdir(parents=True); ir.write_bytes(b'IR output')
                alias = build / alias_tree / 'CCO/Nested'
                target = Path(temp) / 'shared'
                alias.rename(target)
                alias.symlink_to(target, target_is_directory=True)
                removed = invalidate(build, {trace})
                self.assertTrue(removed)
                self.assertFalse((build / 'lib/lean/CCO').exists())
                if alias_tree == 'lib/lean':
                    self.assertEqual((target / 'Child.olean').read_bytes(), b'output')
                    self.assertTrue((target / 'Child.trace').is_file())
                else:
                    self.assertEqual((target / 'Child.c').read_bytes(), b'IR output')

    def test_clear_rejects_aliased_namespace_parent_before_deleting_external_outputs(self):
        for relative in ['lib', 'lib/lean', 'ir']:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temp:
                build = Path(temp) / 'build'; build.mkdir()
                alias = build / relative
                alias.parent.mkdir(parents=True, exist_ok=True)
                target = Path(temp) / 'external'; target.mkdir()
                sentinel = target / ('lean/CCO.olean' if relative == 'lib' else 'CCO.olean')
                sentinel.parent.mkdir(parents=True, exist_ok=True)
                sentinel.write_bytes(b'external output')
                alias.symlink_to(target, target_is_directory=True)
                with self.assertRaisesRegex(ValueError, 'aliased artifact parent'):
                    clear_project_artifacts(build)
                self.assertEqual(sentinel.read_bytes(), b'external output')
                self.assertTrue(alias.is_symlink())

    def test_absent_cache_is_valid(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(inspect_metadata(Path(temp)), ({}, set()))


if __name__ == '__main__':
    unittest.main()
