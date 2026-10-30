"""Security/identity regressions for the independently pinned path provider."""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from ramsey_provider import cache_key, materialized_provider
from verify_ramsey_provider import clear_provider_outputs


class RamseyProviderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / 'project'
        self.project.mkdir()
        original = Path(__file__).resolve().parents[1]
        self.provider = self.project / 'vendor/ramsey'
        shutil.copytree(original / 'vendor/ramsey', self.provider, ignore=shutil.ignore_patterns('.lake'))
        (self.project / 'tools').mkdir()
        for name in ('ramsey_provider.json', 'ramsey_provider.py', 'verify_ramsey_provider.py',
                     'ramsey_provider_metadata.lean'):
            shutil.copyfile(original / 'tools' / name, self.project / 'tools' / name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
            shutil.copyfile(original / name, self.project / name)
        self.git('init', '-q')
        self.git('config', 'user.email', 'cache-test@example.invalid')
        self.git('config', 'user.name', 'Cache regression')
        self.git('add', '.')
        self.git('commit', '-qm', 'Exact original provider fixture')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.project, text=True,
                                       stderr=subprocess.STDOUT).strip()

    def test_exact_subtree_and_dependency_entries(self):
        config, provider = materialized_provider(self.project)
        self.assertEqual(provider, self.provider)
        self.assertEqual(config['source_modules'], 106)

    def test_hidden_source_change_cannot_reuse_pinned_identity(self):
        relative = 'vendor/ramsey/PartiteConstruction/Structure/Basic.lean'
        self.git('update-index', '--assume-unchanged', relative)
        with (self.project / relative).open('a') as output:
            output.write('\n-- hidden tracked source edit\n')
        self.assertEqual(self.git('status', '--porcelain'), '')
        with self.assertRaisesRegex(ValueError, 'pinned Git blob'):
            materialized_provider(self.project)

    def test_existing_dependency_change_is_rejected(self):
        path = self.project / 'lake-manifest.json'
        data = json.loads(path.read_text())
        data['packages'][0]['rev'] = '0' * 40
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'existing receiving dependency'):
            materialized_provider(self.project)

    def test_untracked_source_is_rejected(self):
        (self.provider / 'CCORamsey/Unexpected.lean').parent.mkdir()
        (self.provider / 'CCORamsey/Unexpected.lean').write_text('theorem unexpected : True := trivial\n')
        with self.assertRaisesRegex(ValueError, 'extra/missing'):
            materialized_provider(self.project)

    def test_source_alias_is_rejected(self):
        outside = self.project.parent / 'outside-provider'
        self.provider.rename(outside)
        self.provider.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'physical vendor'):
            materialized_provider(self.project)

    def test_cache_key_excludes_unrelated_cco_commit(self):
        before = cache_key(self.project, 'Linux', 'X64')[0]
        (self.project / 'UnrelatedCCO.txt').write_text('A theorem checkpoint changes independently.\n')
        self.git('add', 'UnrelatedCCO.txt')
        self.git('commit', '-qm', 'Independent CCO checkpoint')
        self.assertEqual(cache_key(self.project, 'Linux', 'X64')[0], before)

    def test_cache_key_binds_platform_and_configuration(self):
        before = cache_key(self.project, 'Linux', 'X64')[0]
        self.assertNotEqual(cache_key(self.project, 'Linux', 'ARM64')[0], before)
        with (self.project / 'lake-manifest.json').open('a') as output:
            output.write('\n')
        self.assertNotEqual(cache_key(self.project, 'Linux', 'X64')[0], before)

    def test_invalidation_refuses_shared_build_alias(self):
        build = self.provider / '.lake/build'
        build.parent.mkdir()
        outside = self.project.parent / 'shared-build'
        outside.mkdir()
        sentinel = outside / 'keep'; sentinel.write_text('shared dependency output')
        build.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'aliased/shared'):
            clear_provider_outputs(self.provider, build)
        self.assertEqual(sentinel.read_text(), 'shared dependency output')

    def test_namespace_alias_is_unlinked_without_following(self):
        build = self.provider / '.lake/build'
        lib = build / 'lib/lean'; ir = build / 'ir'
        lib.mkdir(parents=True); ir.mkdir(parents=True)
        outside = self.project.parent / 'shared-namespace'; outside.mkdir()
        sentinel = outside / 'keep.olean'; sentinel.write_bytes(b'keep dependency bytes')
        (lib / 'PartiteConstruction').symlink_to(outside, target_is_directory=True)
        clear_provider_outputs(self.provider, build)
        self.assertFalse((lib / 'PartiteConstruction').exists())
        self.assertEqual(sentinel.read_bytes(), b'keep dependency bytes')


if __name__ == '__main__':
    unittest.main()
