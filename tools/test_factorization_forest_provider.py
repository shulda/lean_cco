"""Identity, closure, licensed-cache and archive regressions for finite forests."""
from __future__ import annotations

import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from audit_factorization_forest import audit, ALLOW
from factorization_forest_provider import (DISTRIBUTION, GUARDS, cache_key, materialized_provider,
    prepare_distribution, verify_distribution)
from mathlib_cache_roots import cache_roots
from package_verified_build import package
from restore_verified_build import BUILD_DIRS, validate_tar
from verify_factorization_forest_provider import clear_provider_outputs, inspect_forest_traces
from verify_project_cache import inspect_metadata


class ForestProviderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / 'project'
        self.project.mkdir()
        self.original = Path(__file__).resolve().parents[1]
        self.provider = self.project / 'vendor/factorization-forest'
        shutil.copytree(self.original / 'vendor/factorization-forest', self.provider,
                        ignore=shutil.ignore_patterns('.lake'))
        (self.project / 'tools').mkdir()
        for name in set(GUARDS) | {'factorization_forest_provider.json'}:
            shutil.copyfile(self.original / 'tools' / name, self.project / 'tools' / name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'CCO.lean'):
            shutil.copyfile(self.original / name, self.project / name)
        self.git('init', '-q')
        self.git('config', 'user.email', 'forest-test@example.invalid')
        self.git('config', 'user.name', 'Forest regression')
        self.git('add', '.')
        self.git('commit', '-qm', 'Exact finite forest fixture')

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.project, text=True,
                                       stderr=subprocess.STDOUT).strip()

    def test_exact_fourteen_file_closure_and_original_pin(self):
        config, provider = materialized_provider(self.project)
        self.assertEqual(provider, self.provider)
        self.assertEqual(config['source_modules'], 14)
        self.assertEqual(config['commit'], '0acb244aaa913c32eeeff48e939cb5df469a3f70')

    def test_assume_unchanged_source_and_license_edits_are_rejected(self):
        for relative in ('AlgebraicAutomata/FactorizationForest/Tree.lean', 'LICENSE'):
            with self.subTest(relative=relative):
                path = self.provider / relative
                original = path.read_bytes()
                self.git('update-index', '--assume-unchanged', 'vendor/factorization-forest/' + relative)
                path.write_bytes(original + b'\n-- hidden edit\n')
                self.assertEqual(self.git('status', '--porcelain'), '')
                with self.assertRaisesRegex(ValueError, 'pinned Git blob'):
                    materialized_provider(self.project)
                path.write_bytes(original)

    def test_untracked_provider_source_is_rejected(self):
        (self.provider / 'AlgebraicAutomata/Extra.lean').write_text('theorem extra : True := trivial\n')
        with self.assertRaisesRegex(ValueError, 'extra/missing'):
            materialized_provider(self.project)

    def test_receiving_pins_and_original_compiler_options_are_required(self):
        path = self.project / 'lakefile.toml'
        path.write_text(path.read_text().replace('maxSynthPendingDepth = 3', 'maxSynthPendingDepth = 4'))
        with self.assertRaisesRegex(ValueError, 'compiler options'):
            materialized_provider(self.project)
        shutil.copyfile(self.original / 'lakefile.toml', path)
        path = self.project / 'lake-manifest.json'
        data = json.loads(path.read_text()); data['packages'][0]['rev'] = '0' * 40
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'receiving dependency'):
            materialized_provider(self.project)

    def test_source_directory_alias_is_rejected(self):
        path = self.provider / 'AlgebraicAutomata/FactorizationForest'
        target = self.project.parent / 'shared-source'
        path.rename(target); path.symlink_to(target, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Missing/aliased'):
            materialized_provider(self.project)

    def test_actual_provider_edges_supply_all_sixteen_mathlib_roots(self):
        (self.project / 'CCO').mkdir()
        (self.project / 'CCO/ForestFixture.lean').write_text(
            'import AlgebraicAutomata.FactorizationForest.Tree\n')
        roots, modules = cache_roots(self.project, root='CCO.ForestFixture')
        self.assertEqual(len(roots), 16)
        self.assertIn('Mathlib.Algebra.Group.Idempotent', roots)
        self.assertNotIn('Mathlib', roots)
        self.assertNotIn('Mathlib.Tactic', roots)
        self.assertEqual(modules, ['CCO.ForestFixture'])

    def test_key_excludes_cco_commit_but_binds_platform_options_and_guards(self):
        first = cache_key(self.project, 'Linux', 'X64')[0]
        (self.project / 'Unrelated.lean').write_text('-- unrelated CCO checkpoint\n')
        self.git('add', 'Unrelated.lean'); self.git('commit', '-qm', 'Unrelated CCO checkpoint')
        self.assertEqual(cache_key(self.project, 'Linux', 'X64')[0], first)
        self.assertNotEqual(cache_key(self.project, 'Linux', 'ARM64')[0], first)
        with (self.project / 'lakefile.toml').open('a') as f:
            f.write('\n# independent receiving configuration change\n')
        second = cache_key(self.project, 'Linux', 'X64')[0]
        self.assertNotEqual(second, first)
        with (self.project / 'tools/verify_project_cache.py').open('a') as f:
            f.write('\n# compiled guard revision\n')
        self.assertNotEqual(cache_key(self.project, 'Linux', 'X64')[0], second)

    def test_distribution_has_full_license_provenance_and_every_modified_source(self):
        (self.project / '.lake').mkdir()
        prepare_distribution(self.project)
        verify_distribution(self.project)
        distribution = self.project / DISTRIBUTION
        self.assertEqual((distribution / 'LICENSE').read_bytes(), (self.provider / 'LICENSE').read_bytes())
        self.assertEqual((distribution / 'PROVENANCE.json').read_bytes(),
                         (self.provider / 'PROVENANCE.json').read_bytes())
        self.assertEqual(len(list((distribution / 'AlgebraicAutomata').rglob('*.lean'))), 14)
        (distribution / 'LICENSE').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing/aliased'):
            verify_distribution(self.project)

    def test_trace_requires_receiving_compiler_original_options_and_native_outputs(self):
        config = materialized_provider(self.project)[0]
        build = self.project / '.lake/build'
        trace = build / 'lib/lean/AlgebraicAutomata/Test.trace'
        trace.parent.mkdir(parents=True)
        options = {'maxSynthPendingDepth': 3, 'autoImplicit': False}
        inputs = [[config['compiler_trace'], 'compiler-hash'],
                  ['Module.name: AlgebraicAutomata.Test', 'name-hash'],
                  ['Package.id?: (some CCO)', 'package-hash'],
                  ['Module.leanArgs: #[]', 'arguments-hash'],
                  ['options', [['-DmaxSynthPendingDepth=3', 'option-hash'],
                               ['-DautoImplicit=false', 'option-hash']]]]
        outputs = {key: '0' * 16 + '.' + suffix for key, suffix in
                   [('i', 'ilean'), ('r', 'ir'), ('rs', 'ir.sig'), ('c', 'c')]}
        data = {'inputs': inputs, 'outputs': outputs, 'synthetic': False, 'schemaVersion': '2025-09-10'}
        for suffix in ('ilean', 'ir', 'ir.sig'):
            trace.with_suffix('.' + suffix).write_bytes(b'compiled fixture')
        native = build / 'ir/AlgebraicAutomata/Test.c'; native.parent.mkdir(parents=True)
        native.write_bytes(b'compiled native fixture')
        trace.write_text(json.dumps(data))
        expected, errors = inspect_forest_traces(build, [trace], config, options)
        self.assertEqual(errors, {})
        self.assertEqual(len(expected), 4)
        self.assertIn(native, expected)
        native.unlink()
        self.assertIn('missing forest C/IR/editor output',
                      inspect_forest_traces(build, [trace], config, options)[1][trace])
        native.write_bytes(b'compiled native fixture')
        inputs[-1][1][0][0] = '-DmaxSynthPendingDepth=4'
        trace.write_text(json.dumps(data))
        self.assertIn('compiler options changed',
                      inspect_forest_traces(build, [trace], config, options)[1][trace])
        inputs[0][0] = 'Lean 4.35.0-rc3, commit foreign'
        trace.write_text(json.dumps(data))
        self.assertIn('compiler pin changed',
                      inspect_forest_traces(build, [trace], config, options)[1][trace])

    def test_provider_guard_does_not_hash_or_invalidate_cco_traces(self):
        build = self.project / '.lake/build'
        cco = build / 'lib/lean/CCO'; cco.mkdir(parents=True)
        (cco / 'Current.trace').write_text('bad unrelated CCO metadata')
        forest = build / 'lib/lean/AlgebraicAutomata'; forest.mkdir()
        trace = forest / 'Current.trace'; trace.write_text('bad forest metadata')
        _, invalid = inspect_metadata(build, namespaces=('AlgebraicAutomata',))
        self.assertEqual(invalid, {trace})
        clear_provider_outputs(self.project)
        self.assertTrue((cco / 'Current.trace').is_file())
        self.assertFalse(forest.exists())

    def test_invalidation_refuses_shared_build_and_unlinks_namespace_alias(self):
        shared = self.project.parent / 'shared-build'; shared.mkdir()
        sentinel = shared / 'keep'; sentinel.write_text('shared output')
        build = self.project / '.lake/build'; build.parent.mkdir()
        build.symlink_to(shared, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'aliased/shared'):
            clear_provider_outputs(self.project)
        self.assertEqual(sentinel.read_text(), 'shared output')
        build.unlink(); lib = build / 'lib/lean'; lib.mkdir(parents=True)
        (lib / 'AlgebraicAutomata').symlink_to(shared, target_is_directory=True)
        clear_provider_outputs(self.project)
        self.assertFalse((lib / 'AlgebraicAutomata').exists())
        self.assertTrue(sentinel.is_file())

    def fixture_archive(self):
        for relative in BUILD_DIRS:
            if relative == DISTRIBUTION:
                continue
            folder = self.project / relative; folder.mkdir(parents=True)
            (folder / 'fixture.trace').write_text('compilation seed, not proof')
        prepare_distribution(self.project)
        bundle = self.project.parent / 'bundle'
        package(self.project, bundle)
        artifact = self.project.parent / 'build.zip'
        with zipfile.ZipFile(artifact, 'w') as archive:
            for path in bundle.iterdir():
                archive.write(path, path.name)
        return artifact, bundle

    def test_binary_export_contains_all_provider_license_and_source_notices(self):
        _, bundle = self.fixture_archive()
        with tarfile.open(bundle / 'build.tar.gz') as archive:
            members = validate_tar(archive)
            names = {member.name for member in members}
            self.assertIn(DISTRIBUTION + '/LICENSE', names)
            self.assertIn(DISTRIBUTION + '/PROVENANCE.json', names)
            self.assertEqual(archive.extractfile(DISTRIBUTION + '/LICENSE').read(),
                             (self.provider / 'LICENSE').read_bytes())
            self.assertEqual(sum(name.startswith(DISTRIBUTION + '/AlgebraicAutomata/')
                                 and name.endswith('.lean') for name in names), 14)

    def test_actual_restore_validates_exact_inputs_and_preserves_sources(self):
        artifact, _ = self.fixture_archive()
        head = self.git('rev-parse', 'HEAD')
        command = ['python3', str(self.original / 'tools/restore_verified_build.py'),
                   '--project', str(self.project), '--zip', str(artifact),
                   '--expected-checkout-sha', head, '--expected-project-head', head,
                   '--stage', str(self.project / '.lake/restore-fixture'), '--restore']
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(json.loads(result.stdout)['restored'])
        self.assertEqual(self.git('status', '--porcelain', '--untracked-files=no'), '')
        verify_distribution(self.project)

    def test_restore_rejects_missing_binary_license_before_any_replacement(self):
        _, bundle = self.fixture_archive()
        payload = self.project.parent / 'unlicensed.tar.gz'
        with tarfile.open(bundle / 'build.tar.gz') as original, tarfile.open(payload, 'w:gz') as edited:
            for member in original.getmembers():
                if member.name == DISTRIBUTION + '/LICENSE':
                    continue
                edited.addfile(member, original.extractfile(member) if member.isfile() else None)
        artifact = self.project.parent / 'unlicensed.zip'
        with zipfile.ZipFile(artifact, 'w') as archive:
            archive.write(payload, 'build.tar.gz')
            for name in ('checkout-sha.txt', 'input-sha256.txt'):
                archive.write(bundle / name, name)
        head = self.git('rev-parse', 'HEAD')
        sentinel = self.project / '.lake/build/keep'; sentinel.write_text('own output')
        result = subprocess.run(['python3', str(self.original / 'tools/restore_verified_build.py'),
            '--project', str(self.project), '--zip', str(artifact), '--expected-checkout-sha', head,
            '--expected-project-head', head, '--stage', str(self.project / '.lake/reject-fixture'),
            '--restore'], text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('LICENSE', result.stderr)
        self.assertEqual(sentinel.read_text(), 'own output')

    def test_archive_rejects_traversal_source_and_escaping_link_members(self):
        for name, link in [('../source.lean', None), ('CCO.lean', None),
                           ('.lake/build/escape', '/tmp/foreign')]:
            with self.subTest(name=name):
                buffer = io.BytesIO()
                with tarfile.open(fileobj=buffer, mode='w') as archive:
                    item = tarfile.TarInfo(name)
                    if link:
                        item.type = tarfile.SYMTYPE; item.linkname = link
                    archive.addfile(item)
                buffer.seek(0)
                with tarfile.open(fileobj=buffer, mode='r') as archive, self.assertRaises(ValueError):
                    validate_tar(archive)

    def test_audit_uses_module_origin_root_exact_import_and_all_791_declarations(self):
        config = materialized_provider(self.project)[0]
        report = {'ok': True, 'audited': 791, 'root': 'AlgebraicAutomata', 'allowed': ALLOW,
                  'axiomsUsed': ALLOW, 'violations': []}
        result = subprocess.CompletedProcess([], 0, json.dumps(report), '')
        with patch('audit_factorization_forest.verify'), patch(
                'audit_factorization_forest.materialized_provider', return_value=(config, self.provider)), patch(
                'audit_factorization_forest.subprocess.run',
                                                               return_value=result) as run:
            audit(self.project, Path('/pinned/axiom-audit'))
            command = run.call_args.args[0]
            self.assertEqual(command[3:], ['--root', 'AlgebraicAutomata', '--modules', config['module'],
                                           '--allow', ','.join(ALLOW), '--json'])
            report['audited'] = 790; result.stdout = json.dumps(report)
            with self.assertRaisesRegex(ValueError, 'all 791'):
                audit(self.project, Path('/pinned/axiom-audit'))


if __name__ == '__main__':
    unittest.main()
