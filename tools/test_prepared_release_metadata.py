"""Source IDs and the additional unbound forest provider retain exact provenance."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

import build_formalization_module as module
import build_formalization_handoff as handoff


class PreparedReleaseTests(unittest.TestCase):
    def test_catalogue_ids_and_aliases_reject_ambiguous_declarations(self):
            first = {'id': 'result-one', 'labels': ['alias-one', 'result-one']}
            second = {'id': 'result-two', 'labels': ['alias-two']}
            resolved = module.catalogue_references([first, second])
            self.assertIs(resolved['result-one'], first)
            self.assertIs(resolved['alias-one'], first)
            self.assertIs(resolved['result-two'], second)
            self.assertNotIn('unknown', resolved)
            for collision in [
                    {'id': 'result-one', 'labels': []},
                    {'id': 'result-two', 'labels': ['alias-one']},
                    {'id': 'alias-one', 'labels': []},
                    {'id': 'result-two', 'labels': ['result-one']}]:
                with self.subTest(collision=collision), self.assertRaisesRegex(ValueError, 'Ambiguous catalogue'):
                    module.catalogue_references([first, collision])

    def test_unlabelled_source_result_resolves_by_exact_catalogue_id(self):
            ident = 'unlabelled:sections/ramsey_ap_from_clones.tex:corollary:1'
            decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
            declaration = next(d for d in decls['declarations'] if d['id'] == ident)
            self.assertEqual(declaration['labels'], [])
            source = declaration['file']
            data = (module.ROOT / source).read_bytes()
            config = {
                'id': 'catalogue_id_fixture',
                'source_commit': decls['summary']['source_commit'],
                'source_files': [{'file': source, 'git_blob': module.blob_sha(data)}],
                'source_result_files': [], 'additional_result_exports': [ident],
                'assumptions': [], 'definitions': [],
                'claims': [{'id': 'C01', 'name': 'Fixture source reference',
                            'scope': 'typed', 'status': 'HUMAN_PROOF_EXPANDED',
                            'source_labels': [ident], 'notes': 'P01', 'depends_on': []}],
                'exports': [{'source_label': ident, 'claims': ['C01']}],
                'tasks': [{'id': 'T01', 'name': 'Fixture task', 'claims': ['C01'],
                           'depends_on': [], 'status': 'NOT_STARTED_IN_LEAN',
                           'acceptance': 'Fixture only.'}],
                'scope': 'Reference resolution fixture; no mathematical proof asserted.',
                'controls': [], 'article_feedback': [],
            }
            with tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                (root / source).parent.mkdir(parents=True)
                (root / source).write_bytes(data)
                notes = root / 'formalization/catalogue_id_fixture/PROOF_NOTES.md'
                notes.parent.mkdir(parents=True)
                notes.write_text('## P01: Reference resolution fixture\n')
                validated = module.validate(root, config, decls)
                self.assertIs(validated[1][ident], declaration)
                rendered = module.render(config, *validated)
                self.assertIn(f'[`{ident}`](../../{source}#L{declaration["line"]})', rendered)
                missing = ident.rsplit(':', 1)[0] + ':999'
                bad = deepcopy(config)
                bad['additional_result_exports'] = [missing]
                bad['exports'][0]['source_label'] = missing
                with self.assertRaisesRegex(ValueError, 'Unknown selected additional result'):
                    module.validate(root, bad, decls)
                bad = deepcopy(config)
                bad['exports'] = []
                with self.assertRaisesRegex(ValueError, 'incomplete or duplicated'):
                    module.validate(root, bad, decls)

    def test_forest_citation_and_global_declaration_remain_exact_and_unbound(self):
        original = json.loads((module.ROOT / 'formalization/old_idempotent_forest/module.json').read_text())
        module.validate_external_providers(original)
        changes = [
            ('source_version', 'latest'), ('theorem', 'Theorem 99'),
            ('source_url', 'https://example.org/forest'),
            ('status', 'COMPILED'),
        ]
        for key, value in changes:
            bad = deepcopy(original)
            bad['external_providers'][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                module.validate_external_providers(bad)
        for key, value in [('commit', 'main'), ('mathlib_commit', ''),
                           ('declarations', ['not a declaration']), ('bridge_status', 'COMPILED')]:
            bad = deepcopy(original)
            bad['external_providers'][0]['lean_reference'][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                module.validate_external_providers(bad)

    def test_handoff_carries_forest_licensing_plan_and_all_module_controls(self):
        files, manifest = handoff.collect(handoff.ROOT)
        self.assertIn('formalization/FACTORIZATION_FOREST_PROVIDER.md', files)
        for config in manifest['modules']:
            path = 'formalization/' + config['id'] + '/module.json'
            control = json.loads(files[path]).get('control_script', 'tools/check_raw_exact_controls.py')
            self.assertIn(control, files)
            self.assertEqual(manifest['verification'].count('python ' + control), 1)
