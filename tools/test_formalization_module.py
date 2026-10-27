"""Provenance/graph failures must not silently leave a module marked current."""
from copy import deepcopy
import json
import unittest

import build_formalization_module as module


class ModuleTests(unittest.TestCase):
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


if __name__ == '__main__':
    unittest.main()
