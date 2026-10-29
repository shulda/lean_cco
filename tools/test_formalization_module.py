"""Provenance/graph failures must not silently leave a module marked current."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

import build_formalization_module as module


class ModuleTests(unittest.TestCase):
    def _safe_import_fixture(self):
        config = json.loads((module.ROOT / 'formalization/safe_readings/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        return config, decls

    def _validate_with_strong_provider(self, config, declarations, provider):
        path = module.ROOT / 'formalization/strong_selectors/module.json'
        original = module.Path.read_text
        def read_text(file, *args, **kwargs):
            return json.dumps(provider) if file == path else original(file, *args, **kwargs)
        with patch.object(module.Path, 'read_text', new=read_text):
            return module.validate(module.ROOT, config, declarations)

    def test_internal_support_is_visible_without_broadening_the_export(self):
        config, decls = self._safe_import_fixture()
        order, labels, raw = module.validate(module.ROOT, config, decls)
        text = module.render(config, order, labels, raw)
        provider = json.loads((module.ROOT / 'formalization/strong_selectors/module.json').read_text())
        for item in config['imports']:
            if 'provider_support_claims' in item:
                exported = next(e for e in provider['exports'] if e['source_label'] == item['source_label'])
                self.assertTrue(set(item['provider_claims']) <= set(exported['claims']))
                self.assertFalse(set(item['provider_support_claims']) & set(item['provider_claims']))
                self.assertIn(item['id'] + ' internal proof support', text)
                self.assertIn(item['provider_support_usage'], text)
        self.assertIn('not additional\nnumbered exports or consequences of the named theorem statement', text)

    def test_internal_support_rejects_unexported_or_invalid_selected_claims(self):
        config, decls = self._safe_import_fixture()
        for selected in [None, [], ['C08', 'C08'], ['C01'], ['C99'], 'C08']:
            bad = deepcopy(config)
            next(i for i in bad['imports'] if i['id'] == 'I04')['provider_claims'] = selected
            with self.subTest(selected=selected), self.assertRaisesRegex(ValueError, 'selected export'):
                module.validate(module.ROOT, bad, decls)

    def test_internal_support_is_strict_proved_transitive_claim_support(self):
        config, decls = self._safe_import_fixture()
        for support in [None, [], ['C01', 'C01'], ['C08'], ['C26'], ['A01'], ['C99'], 'C01']:
            bad = deepcopy(config)
            next(i for i in bad['imports'] if i['id'] == 'I04')['provider_support_claims'] = support
            with self.subTest(support=support), self.assertRaisesRegex(ValueError, 'Internal proof support'):
                module.validate(module.ROOT, bad, decls)

    def test_internal_support_requires_usage_and_cannot_inherit_a_provider(self):
        config, decls = self._safe_import_fixture()
        for usage in [None, '', '  ', []]:
            bad = deepcopy(config)
            next(i for i in bad['imports'] if i['id'] == 'I04')['provider_support_usage'] = usage
            with self.subTest(usage=usage), self.assertRaises(ValueError):
                module.validate(module.ROOT, bad, decls)
        for before in [True, False]:
            bad = deepcopy(config)
            unbound = deepcopy(next(i for i in bad['imports'] if i['id'] == 'I04'))
            unbound.update(id='I13', provider_module=None)
            bad['imports'].insert(0 if before else len(bad['imports']), unbound)
            with self.subTest(before=before), self.assertRaisesRegex(ValueError, 'pinned provider'):
                module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(i for i in bad['imports'] if i['id'] == 'I04').pop('provider_support_claims')
        with self.assertRaises(ValueError):
            module.validate(module.ROOT, bad, decls)

    def test_internal_support_rejects_graph_status_and_export_provenance_failures(self):
        config, decls = self._safe_import_fixture()
        provider = json.loads((module.ROOT / 'formalization/strong_selectors/module.json').read_text())
        variants = []
        for deps in [[], ['C08'], ['C99']]:
            bad = deepcopy(provider)
            next(c for c in bad['claims'] if c['id'] == 'C08')['depends_on'] = deps
            variants.append(bad)
        bad = deepcopy(provider)
        next(c for c in bad['claims'] if c['id'] == 'C01')['status'] = 'LEAN_PROVED'
        variants.append(bad)
        bad = deepcopy(provider)
        bad['source_commit'] = '0' * 40
        variants.append(bad)
        bad = deepcopy(provider)
        bad['exports'].append(deepcopy(next(e for e in bad['exports']
            if e['source_label'] == 'lem:typed-exact-products')))
        variants.append(bad)
        bad = deepcopy(provider)
        bad['source_files'][0]['git_blob'] = '0' * 40
        variants.append(bad)
        for i, bad in enumerate(variants):
            with self.subTest(variant=i), self.assertRaises(ValueError):
                self._validate_with_strong_provider(config, decls, bad)

    def test_direct_owner_closure_keeps_countability_and_normalization_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/direct_owner_closure/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 1)
        for claim, forbidden in [('C05', 'A08'), ('C08', 'I07'), ('C18', 'C24'), ('C22', 'A05')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(forbidden)
            with self.subTest(claim=claim, forbidden=forbidden), self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, decls)

    def _mi_import_fixture(self):
        config = json.loads((module.ROOT / 'formalization/mi_geometry/module.json').read_text())
        declarations = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        return config, declarations

    def _validate_with_acl_provider(self, config, declarations, provider):
        path = module.ROOT / 'formalization/acl_owner_geometry/module.json'
        original = module.Path.read_text
        def read_text(file, *args, **kwargs):
            return json.dumps(provider) if file == path else original(file, *args, **kwargs)
        with patch.object(module.Path, 'read_text', new=read_text):
            return module.validate(module.ROOT, config, declarations)

    def test_imported_auxiliary_equation_has_actual_source_link(self):
        config, declarations = self._mi_import_fixture()
        order, labels, raw = module.validate(module.ROOT, config, declarations)
        imported = labels['eq:acf-closure-pullback']
        self.assertEqual(imported['kind'], 'equation')
        self.assertEqual(imported['file'], 'sections/rooted_acf_geometry.tex')
        anchor = '\\label{eq:acf-closure-pullback}'
        self.assertEqual(imported['line'], raw[imported['file']].count(
            '\n', 0, raw[imported['file']].index(anchor)) + 1)
        self.assertEqual(module.render(config, order, labels, raw),
            (module.ROOT / 'formalization/mi_geometry/README.md').read_text())

    def test_auxiliary_import_requires_explicit_exported_support(self):
        config, declarations = self._mi_import_fixture()
        for support in [None, [], ['C01'], ['C33'], ['C21', 'C21']]:
            bad = deepcopy(config)
            next(i for i in bad['imports'] if i['id'] == 'I18')['provider_claims'] = support
            with self.subTest(support=support), self.assertRaisesRegex(ValueError, 'support claims'):
                module.validate(module.ROOT, bad, declarations)

    def test_auxiliary_provider_binding_cannot_be_inherited_from_an_earlier_import(self):
        config, declarations = self._mi_import_fixture()
        unbound = deepcopy(next(i for i in config['imports'] if i['id'] == 'I18'))
        unbound.update(id='I19', provider_module=None)
        unbound.pop('provider_claims')
        for before in [False, True]:
            bad = deepcopy(config)
            bad['imports'].insert(0 if before else len(bad['imports']), deepcopy(unbound))
            with self.subTest(unbound_before_valid=before), self.assertRaisesRegex(
                    ValueError, 'Unknown imported source without pinned auxiliary provider'):
                module.validate(module.ROOT, bad, declarations)
        for key, value in [('source_label', 'eq:missing'), ('provider_module', None)]:
            bad = deepcopy(config)
            next(i for i in bad['imports'] if i['id'] == 'I18')[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'Unknown imported source'):
                module.validate(module.ROOT, bad, declarations)

    def test_auxiliary_import_binds_both_source_fingerprints_and_literal_anchor(self):
        config, declarations = self._mi_import_fixture()
        provider = json.loads((module.ROOT / 'formalization/acl_owner_geometry/module.json').read_text())
        variants = []
        bad = deepcopy(provider)
        bad['source_commit'] = '0' * 40
        variants.append(bad)
        bad = deepcopy(provider)
        next(s for s in bad['source_files'] if s['file'] == 'sections/rooted_acf_geometry.tex')['git_blob'] = '0' * 40
        variants.append(bad)
        for source in [
                {'file': 'sections/global_correspondence.tex', 'anchor': '\\label{eq:acf-closure-pullback}'},
                {'file': 'sections/rooted_acf_geometry.tex', 'anchor': 'eq:acf-closure-pullback'}]:
            bad = deepcopy(provider)
            next(e for e in bad['auxiliary_exports'] if e['source_label'] == 'eq:acf-closure-pullback')['source'] = source
            variants.append(bad)
        for index, bad in enumerate(variants):
            with self.subTest(variant=index), self.assertRaises(ValueError):
                self._validate_with_acl_provider(config, declarations, bad)

    def test_auxiliary_import_rejects_ambiguous_exports_and_fabricated_provider_claims(self):
        config, declarations = self._mi_import_fixture()
        provider = json.loads((module.ROOT / 'formalization/acl_owner_geometry/module.json').read_text())
        export = next(e for e in provider['auxiliary_exports'] if e['source_label'] == 'eq:acf-closure-pullback')
        variants = []
        for destination in ['exports', 'auxiliary_exports']:
            bad = deepcopy(provider)
            bad[destination].append(deepcopy(export))
            variants.append(bad)
        bad = deepcopy(provider)
        next(e for e in bad['auxiliary_exports'] if e['source_label'] == export['source_label'])['claims'] = ['C99']
        variants.append(bad)
        bad = deepcopy(provider)
        bad['source_files'].append(deepcopy(next(s for s in bad['source_files'] if s['file'] == export['source']['file'])))
        variants.append(bad)
        for index, bad in enumerate(variants):
            with self.subTest(variant=index), self.assertRaises(ValueError):
                self._validate_with_acl_provider(config, declarations, bad)

    def test_owner_action_scope_and_premise_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/owner_action/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 6)
        self.assertEqual(config['additional_result_exports'], ['lem:acf-point-homogeneity'])
        for claim, forbidden in [('C03', 'I02'), ('C04', 'A07'),
                                 ('C12', 'A03'), ('C17', 'A05'),
                                 ('C19', 'C13'), ('C21', 'A14'), ('C24', 'A13')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(forbidden)
            with self.subTest(claim=claim, forbidden=forbidden):
                with self.assertRaisesRegex(ValueError, 'firewall'):
                    module.validate(module.ROOT, bad, decls)

    def test_unknown_dependency(self):
        with self.assertRaisesRegex(ValueError, 'Unknown'):
            module.topological_order([{'id': 'A', 'depends_on': ['missing']}])

    def test_cycle(self):
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            module.topological_order([{'id': 'A', 'depends_on': ['B']},
                                      {'id': 'B', 'depends_on': ['A']}])

    def test_valid_order_and_duplicate(self):
        self.assertEqual(module.topological_order([{'id': 'B', 'depends_on': ['A']},
                                                  {'id': 'A'}]), ['A', 'B'])
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            module.topological_order([{'id': 'A'}, {'id': 'A'}])

    def test_changed_source_and_missing_export(self):
        config = json.loads((module.ROOT / module.MODULE / 'module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        bad = deepcopy(config)
        bad['source_files'][0]['git_blob'] = '0' * 40
        with self.assertRaisesRegex(ValueError, 'Source changed'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        bad['exports'].pop()
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)

    def test_unknown_claim_and_lean_status(self):
        config = json.loads((module.ROOT / module.MODULE / 'module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        bad = deepcopy(config)
        bad['exports'][0]['claims'] = ['fake']
        with self.assertRaisesRegex(ValueError, 'export proof'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        bad['claims'][0]['status'] = 'LEAN_PROVED'
        with self.assertRaisesRegex(ValueError, 'Unexpected proof status'):
            module.validate(module.ROOT, bad, decls)

    def test_task_ownership_respects_claim_graph(self):
        config = json.loads((module.ROOT / module.MODULE / 'module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        bad = deepcopy(config)
        # An acyclic task graph alone would miss this unavailable quotient import.
        tasks = {t['id']: t for t in bad['tasks']}
        tasks['T06']['claims'].remove('C18')
        tasks['T02']['claims'].append('C18')
        with self.assertRaisesRegex(ValueError, 'misses a claim provider'):
            module.validate(module.ROOT, bad, decls)

    def test_second_module_has_independent_export_and_task_coverage(self):
        path = module.ROOT / 'formalization/strong_selectors/module.json'
        config = json.loads(path.read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 15)
        bad = deepcopy(config)
        tasks = {t['id']: t for t in bad['tasks']}
        tasks['T04']['depends_on'] = ['T01']
        with self.assertRaisesRegex(ValueError, 'misses a claim provider'):
            module.validate(module.ROOT, bad, decls)

    def test_parity_hasse_coverage_and_exact_helly_firewall(self):
        config = json.loads((module.ROOT / 'formalization/parity_hasse/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 7)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C13')['depends_on'].append('I01')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C23')['depends_on'].append('C19')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)

    def test_exact_crt_auxiliary_equations_and_scope_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/exact_crt/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 5)
        self.assertEqual(len(config['auxiliary_exports']), 2)
        bad = deepcopy(config)
        bad['auxiliary_exports'][0]['source']['anchor'] = '\\label{missing}'
        with self.assertRaisesRegex(ValueError, 'source anchor'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C03')['depends_on'].append('I02')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C20')['depends_on'].append('D10')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)

    def test_canonical_hull_selected_provider_and_noncircular_globalisation(self):
        config = json.loads((module.ROOT / 'formalization/canonical_hull/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 19)
        self.assertEqual(config['additional_result_exports'], ['lem:fibreCCO'])
        bad = deepcopy(config)
        bad['additional_result_exports'] = []
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        bad['additional_result_exports'] = ['missing']
        with self.assertRaisesRegex(ValueError, 'selected additional'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C21')['depends_on'].append('C17')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)

    def test_sir_imports_and_independent_boundary_branches(self):
        config = json.loads((module.ROOT / 'formalization/sir/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 8)
        bad = deepcopy(config)
        bad['imports'][0]['source_label'] = 'missing'
        with self.assertRaisesRegex(ValueError, 'Unknown imported source'):
            module.validate(module.ROOT, bad, decls)
        bad = deepcopy(config)
        next(c for c in bad['claims'] if c['id'] == 'C19')['depends_on'].append('I02')
        with self.assertRaisesRegex(ValueError, 'firewall'):
            module.validate(module.ROOT, bad, decls)

    def test_real_closure_scope_and_terminal_provider_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/real_closure/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 8)
        bad = deepcopy(config)
        bad['additional_result_exports'].pop()
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)
        for claim, provider in [('C20', 'I06'), ('C26', 'I05'), ('C10', 'C08')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(provider)
            with self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, decls)

    def test_finite_packet_source_coverage_and_elementary_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/finite_packets/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 8)
        self.assertEqual(len(config['auxiliary_exports']), 4)
        bad = deepcopy(config)
        bad['exports'].pop()
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)
        for claim, provider in [('C17', 'C12'), ('C20', 'I02'), ('C27', 'I01'), ('C19', 'A05')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(provider)
            with self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, decls)

    def test_rigid_groupoid_selected_providers_and_phase_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/rigid_groupoid/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 9)
        self.assertEqual(len(config['auxiliary_exports']), 4)
        bad = deepcopy(config)
        bad['additional_result_exports'].pop()
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)
        for claim, provider in [('C19', 'I01'), ('C27', 'C24'), ('C30', 'A07'), ('C04', 'A05')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(provider)
            with self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, decls)

    def test_finite_kernel_selected_coverage_and_projection_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/finite_kernel/module.json').read_text())
        decls = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())
        module.validate(module.ROOT, config, decls)
        self.assertEqual(len(config['exports']), 5)
        self.assertEqual(len(config['auxiliary_exports']), 8)
        bad = deepcopy(config)
        bad['additional_result_exports'].pop()
        with self.assertRaisesRegex(ValueError, 'export map'):
            module.validate(module.ROOT, bad, decls)
        for claim, provider in [('C04', 'A04'), ('C13', 'C08'), ('C17', 'A02'), ('C20', 'A07')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(provider)
            with self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, decls)


if __name__ == '__main__':
    unittest.main()
