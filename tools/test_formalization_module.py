"""Provenance/graph failures must not silently leave a module marked current."""
from copy import deepcopy
import json
import unittest

import build_formalization_module as module


class ModuleTests(unittest.TestCase):
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
