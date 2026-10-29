import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from external_provider import (cache_key, check_source_blobs, materialized_provider,
                               specification)
from mathlib_cache_roots import cache_roots
from verify_external_provider import clear_provider_outputs, verify


class ExternalProviderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / 'project'
        self.provider = self.project / '.lake/packages/AllThoseEPPA'
        self.provider.mkdir(parents=True)
        (self.project / 'tools').mkdir()
        (self.provider / 'AllThoseEPPA').mkdir()
        self.dependencies = [dict(name='dep' + str(n), url='https://example.invalid/' + str(n),
                                  rev=f'{n:040x}') for n in range(9)]
        inputs = {
            'lean-toolchain': 'leanprover/lean4:v4.34.1\n',
            'lakefile.toml': 'name = "AllThoseEPPA"\n',
            'lake-manifest.json': json.dumps({'packages': self.dependencies}),
            'AllThoseEPPA/MainTheorems.lean': 'import AllThoseEPPA.Child\nimport Mathlib.Data.Fin.Basic\n',
            'AllThoseEPPA/Child.lean': 'import Mathlib.Data.Set.Basic\n',
        }
        for relative, contents in inputs.items():
            (self.provider / relative).write_text(contents)
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'pinned provider fixture')
        self.config = {
            'schema_version': 1, 'package': 'AllThoseEPPA', 'namespace': 'AllThoseEPPA',
            'module': 'AllThoseEPPA.MainTheorems', 'source_modules': 2,
            'commit': self.git('rev-parse', 'HEAD'), 'tree': self.git('rev-parse', 'HEAD^{tree}'),
            'url': 'https://example.invalid/AllThoseEPPA.git',
            'input_sha256': {name: hashlib.sha256((self.provider / name).read_bytes()).hexdigest()
                             for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']},
            'dependencies': self.dependencies,
        }
        self.write_config()
        (self.project / 'lean-toolchain').write_text(inputs['lean-toolchain'])
        (self.project / 'lakefile.toml').write_text('name = "CCO"\n')
        self.receiving = {'packages': self.dependencies + [dict(
            name='AllThoseEPPA', url=self.config['url'], rev=self.config['commit'],
            inputRev=self.config['commit'], type='git')]}
        self.write_receiving()
        (self.project / 'CCO.lean').write_text('import AllThoseEPPA.MainTheorems\n')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.provider, text=True,
                                       stderr=subprocess.DEVNULL).strip()

    def write_config(self):
        (self.project / 'tools/external_provider.json').write_text(json.dumps(self.config))

    def write_receiving(self):
        (self.project / 'lake-manifest.json').write_text(json.dumps(self.receiving))

    def test_exact_binding_accepts_matching_configuration(self):
        config, source = materialized_provider(self.project)
        self.assertEqual(source, self.provider)
        self.assertEqual(config['commit'], self.git('rev-parse', 'HEAD'))

    def test_unknown_namespace_and_unpinned_provider_are_rejected(self):
        self.config['namespace'] = 'Mathlib'
        self.write_config()
        with self.assertRaisesRegex(ValueError, 'Unsupported'):
            specification(self.project)
        self.config['namespace'] = 'AllThoseEPPA'
        self.config['commit'] = 'main'
        self.write_config()
        with self.assertRaisesRegex(ValueError, 'exact source'):
            specification(self.project)

    def test_wrong_commit_or_tree_are_rejected(self):
        original = copy.deepcopy(self.config)
        for field in ('commit', 'tree'):
            with self.subTest(field=field):
                self.config = copy.deepcopy(original)
                self.config[field] = 'f' * 40
                self.write_config()
                with self.assertRaisesRegex(ValueError, field + ' mismatch'):
                    materialized_provider(self.project)

    def test_incompatible_toolchain_and_configuration_hash_are_rejected(self):
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        with self.assertRaisesRegex(ValueError, 'toolchain is incompatible'):
            materialized_provider(self.project)
        (self.project / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        self.config['input_sha256']['lakefile.toml'] = 'f' * 64
        self.write_config()
        with self.assertRaisesRegex(ValueError, 'configuration/toolchain/manifest changed'):
            materialized_provider(self.project)

    def test_changed_shared_pin_or_provider_requirement_is_rejected(self):
        self.receiving['packages'][0]['rev'] = 'f' * 40
        self.write_receiving()
        with self.assertRaisesRegex(ValueError, 'shared dependency pin'):
            materialized_provider(self.project)
        self.receiving['packages'][0]['rev'] = f'{0:040x}'
        self.receiving['packages'][-1]['inputRev'] = 'main'
        self.write_receiving()
        with self.assertRaisesRegex(ValueError, 'exact external provider'):
            materialized_provider(self.project)

    def test_actual_git_blob_check_catches_assume_unchanged_source(self):
        source = self.provider / 'AllThoseEPPA/Child.lean'
        self.git('update-index', '--assume-unchanged', 'AllThoseEPPA/Child.lean')
        source.write_text('import Mathlib\n')
        self.assertFalse(self.git('status', '--porcelain', '--untracked-files=no'))
        materialized_provider(self.project)  # Git status alone is insufficient.
        with self.assertRaisesRegex(ValueError, 'pinned Git blob'):
            check_source_blobs(self.provider, [source])

    def test_dependency_key_ignores_cco_body_but_binds_manifest_config_and_platform(self):
        before, _ = cache_key(self.project, 'Linux', 'X64')
        (self.project / 'CCO.lean').write_text('-- unrelated new CCO theorem\n')
        self.assertEqual(cache_key(self.project, 'Linux', 'X64')[0], before)
        self.assertNotEqual(cache_key(self.project, 'Linux', 'ARM64')[0], before)
        (self.project / 'lakefile.toml').write_text('name = "CCO"\n# changed options\n')
        self.assertNotEqual(cache_key(self.project, 'Linux', 'X64')[0], before)

    def test_walker_follows_registered_provider_and_keeps_cco_count_separate(self):
        roots, cco = cache_roots(self.project)
        self.assertEqual(roots, ['Mathlib.Data.Fin.Basic', 'Mathlib.Data.Set.Basic'])
        self.assertEqual(cco, ['CCO'])
        (self.project / 'CCO.lean').write_text('import Mathlib.Data.Fin.Basic\n')
        self.assertEqual(cache_roots(self.project)[0], ['Mathlib.Data.Fin.Basic'])
        self.assertEqual(cache_roots(self.project, include_provider=True)[0], roots)

    def test_missing_or_unregistered_provider_fails_closed(self):
        shutil.rmtree(self.provider)
        with self.assertRaisesRegex(ValueError, 'Materialize'):
            cache_roots(self.project)
        (self.project / 'tools/external_provider.json').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing explicit'):
            cache_roots(self.project)

    def compiled_fixture(self):
        build = self.provider / '.lake/build'
        entries, hashes = [], []
        for relative in ('AllThoseEPPA/MainTheorems.lean', 'AllThoseEPPA/Child.lean'):
            stem = (build / 'lib/lean' / relative).with_suffix('')
            stem.parent.mkdir(parents=True, exist_ok=True)
            stem.with_suffix('.olean').write_bytes(b'compiled fixture')
            stem.with_suffix('.trace').write_text(json.dumps({
                'inputs': [[relative, 'current-source']],
                'outputs': {'o': ['0123456789abcdef.olean']}}))
            imports = [{'module': 'Init', 'isMeta': False}]
            entries.append(dict(source=str(self.provider / relative), sourceHash='current-source',
                                imports=imports, isModule=False, compiledImports=imports,
                                compiledIsModule=False, readError=None,
                                resolvedOlean=str(stem.with_suffix('.olean'))))
            hashes.append([str(stem.with_suffix('.olean')), '0123456789abcdef'])
        return build, entries, hashes

    def test_guard_checks_complete_provider_without_claiming_cco_modules(self):
        _, entries, hashes = self.compiled_fixture()
        output = io.StringIO()
        with patch('verify_external_provider.run_json', side_effect=[entries, hashes]), contextlib.redirect_stdout(output):
            self.assertEqual(verify(self.project, True), {'invalidated': 0, 'modules': 2, 'parts': 2})
        self.assertIn('External provider cache consistent: 2 olean part(s), 2 current source', output.getvalue())
        self.assertNotIn('Project cache consistent', output.getvalue())

    def test_guard_rejects_stale_headers_sources_bytes_and_shadowed_artifacts(self):
        _, entries, hashes = self.compiled_fixture()
        cases = [
            ('compiledImports', [], 'compiled imports'),
            ('sourceHash', 'new-but-unbuilt-source', 'source input hash'),
            ('resolvedOlean', '/another/provider/Child.olean', 'search path'),
            ('compiledImports', None, 'missing/unreadable'),
        ]
        for field, changed, message in cases:
            with self.subTest(field=field, changed=changed):
                altered = copy.deepcopy(entries)
                altered[0][field] = changed
                with patch('verify_external_provider.run_json', side_effect=[altered, hashes]):
                    with self.assertRaisesRegex(ValueError, message):
                        verify(self.project, True)
        altered = copy.deepcopy(hashes)
        altered[0][1] = 'f' * 16
        with patch('verify_external_provider.run_json', side_effect=[entries, altered]):
            with self.assertRaisesRegex(ValueError, 'artifact bytes'):
                verify(self.project, True)
        with patch('verify_external_provider.run_json', return_value=entries[:1]):
            with self.assertRaisesRegex(ValueError, 'source-closure count'):
                verify(self.project, True)

    def test_repair_only_removes_private_provider_outputs(self):
        build, entries, hashes = self.compiled_fixture()
        untouched = build / 'lib/lean/CCO.olean'
        untouched.write_bytes(b'other project')
        ir = build / 'ir/AllThoseEPPA/Child.c'
        ir.parent.mkdir(parents=True); ir.write_bytes(b'native output')
        hashes[0][1] = 'f' * 16
        with patch('verify_external_provider.run_json', side_effect=[entries, hashes]), contextlib.redirect_stdout(io.StringIO()):
            self.assertGreater(verify(self.project, True, repair=True)['invalidated'], 0)
        self.assertFalse((build / 'lib/lean/AllThoseEPPA').exists())
        self.assertFalse(ir.exists())
        self.assertEqual(untouched.read_bytes(), b'other project')
        self.assertFalse(self.git('status', '--porcelain', '--untracked-files=no'))

    def test_repair_rejects_aliased_artifact_parents_before_any_deletion(self):
        build = self.provider / '.lake/build'
        lib = build / 'lib/lean'
        lib.parent.mkdir(parents=True)
        outside = Path(self.temp.name) / 'outside'; outside.mkdir()
        sentinel = outside / 'AllThoseEPPA.olean'; sentinel.write_bytes(b'keep external')
        lib.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'aliased provider artifact parent'):
            clear_provider_outputs(self.project, build, 'AllThoseEPPA')
        self.assertEqual(sentinel.read_bytes(), b'keep external')


if __name__ == '__main__':
    unittest.main()
