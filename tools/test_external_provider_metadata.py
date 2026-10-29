"""Published theorem inputs stay versioned, visible and locally unbound."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

import build_formalization_handoff as handoff
import build_formalization_module as module


class ExternalProviderTests(unittest.TestCase):
    def setUp(self):
        self.config = json.loads((module.ROOT / 'formalization/hkn_reservoir/module.json').read_text())
        self.declarations = json.loads((module.ROOT / 'catalogue/declarations.json').read_text())

    def test_published_inputs_are_visible_and_not_local_claims(self):
        order, labels, raw = module.validate(module.ROOT, self.config, self.declarations)
        text = module.render(self.config, order, labels, raw)
        claims = {c['id'] for c in self.config['claims']}
        for provider in self.config['external_providers']:
            self.assertIn(provider['id'], order)
            self.assertNotIn(provider['id'], claims)
            self.assertIn(provider['source_url'], text)
            self.assertIn(provider['status'], text)
            for declaration in provider['lean_reference']['declarations']:
                self.assertIn(declaration, text)
        self.assertIn('not new local proof claims or compiled CCO imports', text)
        self.assertIn('remains a receiving-project obligation', text)

    def test_external_status_cannot_claim_a_compiled_local_bridge(self):
        for status in [None, '', 'LEAN_PROVED', 'HUMAN_PROOF_EXPANDED', 'COMPILED']:
            bad = deepcopy(self.config)
            bad['external_providers'][0]['status'] = status
            with self.subTest(status=status), self.assertRaisesRegex(ValueError, 'bridge obligation'):
                module.validate(module.ROOT, bad, self.declarations)

    def test_external_theorems_require_version_and_precise_source(self):
        for key, value in [('source_version', ''), ('source_version', '1902.03855'),
                           ('theorem', ''), ('theorem', []), ('statement', ''),
                           ('name', ''), ('id', 'C01')]:
            bad = deepcopy(self.config)
            bad['external_providers'][0][key] = value
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, 'precise contract'):
                module.validate(module.ROOT, bad, self.declarations)
        for url in ['', 'http://arxiv.org/html/1902.03855v4',
                    'https://arxiv.org/html/1902.03855v3', 'https://example.org/1902.03855v4']:
            bad = deepcopy(self.config)
            bad['external_providers'][0]['source_url'] = url
            with self.subTest(url=url), self.assertRaisesRegex(ValueError, 'primary source'):
                module.validate(module.ROOT, bad, self.declarations)

    def test_existing_lean_reference_is_pinned_safe_and_unbound(self):
        variants = [('repository', '../outside'), ('commit', 'main'),
                    ('mathlib_commit', ''), ('module', '../Other'),
                    ('source_file', '../MainTheorems.lean'), ('lean_version', 'latest'),
                    ('bridge_status', 'COMPILED'), ('declarations', []),
                    ('declarations', ['Unqualified']), ('declarations', ['A.B', 'A.B'])]
        for key, value in variants:
            bad = deepcopy(self.config)
            bad['external_providers'][0]['lean_reference'][key] = value
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, 'pinned.*bridge'):
                module.validate(module.ROOT, bad, self.declarations)

    def test_external_nodes_keep_duplicate_cycle_and_dependency_guards(self):
        bad = deepcopy(self.config)
        bad['external_providers'].append(deepcopy(bad['external_providers'][0]))
        with self.assertRaisesRegex(ValueError, 'Duplicate module node'):
            module.validate(module.ROOT, bad, self.declarations)
        for dependency in ['MISSING', 'C22']:
            bad = deepcopy(self.config)
            bad['external_providers'][0]['depends_on'].append(dependency)
            with self.subTest(dependency=dependency), self.assertRaisesRegex(ValueError, 'Unknown|Cyclic'):
                module.validate(module.ROOT, bad, self.declarations)

    def test_external_node_cannot_be_exported_as_a_local_claim(self):
        bad = deepcopy(self.config)
        bad['exports'][0]['claims'].append('E01')
        with self.assertRaisesRegex(ValueError, 'export proof claims'):
            module.validate(module.ROOT, bad, self.declarations)
        for providers in [None, {}, ['E01']]:
            bad = deepcopy(self.config)
            bad['external_providers'] = providers
            with self.subTest(providers=providers), self.assertRaises(ValueError):
                module.validate(module.ROOT, bad, self.declarations)

    def test_external_providers_survive_handoff_with_exact_pending_pins(self):
        _, manifest = handoff.collect(handoff.ROOT)
        providers = manifest['external_providers']
        self.assertEqual(providers, [dict(module='hkn_reservoir', **p)
                                     for p in self.config['external_providers']])
        self.assertEqual(len(providers), 2)
        self.assertTrue(all(p['lean_reference']['bridge_status'] == 'NOT_BOUND_TO_CCO_ENCODING'
                            for p in providers))
        self.assertEqual(next(m for m in manifest['modules'] if m['id'] == 'hkn_reservoir')
                         ['external_providers'], self.config['external_providers'])

    def test_catalogued_equation_alias_keeps_pinned_auxiliary_binding(self):
        _, labels, raw = module.validate(module.ROOT, self.config, self.declarations)
        # The immutable catalogue attaches this equation label to its lemma.
        self.assertEqual(labels['eq:packet-matrix']['id'], 'lem:packet-origins')
        self.assertIn('\\label{eq:packet-matrix}', raw[labels['eq:packet-matrix']['file']])
        unbound = deepcopy(next(i for i in self.config['imports'] if i['id'] == 'I09'))
        unbound.update(id='I11', provider_module=None)
        unbound.pop('provider_claims')
        for before in [True, False]:
            bad = deepcopy(self.config)
            bad['imports'].insert(0 if before else len(bad['imports']), deepcopy(unbound))
            with self.subTest(before=before), self.assertRaisesRegex(ValueError, 'pinned auxiliary provider'):
                module.validate(module.ROOT, bad, self.declarations)

    def test_catalogued_equation_alias_cannot_escape_source_or_claim_guards(self):
        path = module.ROOT / 'formalization/owner_transversal/module.json'
        provider = json.loads(path.read_text())
        original = module.Path.read_text
        variants = []
        for key, value in [('source_commit', '0' * 40)]:
            bad = deepcopy(provider)
            bad[key] = value
            variants.append(bad)
        bad = deepcopy(provider)
        next(s for s in bad['source_files'] if s['file'] == 'sections/hkn_packet_reservoir.tex')['git_blob'] = '0' * 40
        variants.append(bad)
        for key, value in [('source', {'file': 'sections/hkn_packet_reservoir.tex', 'anchor': 'eq:packet-matrix'}),
                           ('claims', ['C99'])]:
            bad = deepcopy(provider)
            next(e for e in bad['auxiliary_exports'] if e['source_label'] == 'eq:packet-matrix')[key] = value
            variants.append(bad)
        for destination in ['exports', 'auxiliary_exports']:
            bad = deepcopy(provider)
            bad[destination].append(deepcopy(next(e for e in bad['auxiliary_exports']
                if e['source_label'] == 'eq:packet-matrix')))
            variants.append(bad)
        for index, bad in enumerate(variants):
            def read_text(file, *args, **kwargs):
                return json.dumps(bad) if file == path else original(file, *args, **kwargs)
            with self.subTest(variant=index), patch.object(module.Path, 'read_text', new=read_text), \
                    self.assertRaises(ValueError):
                module.validate(module.ROOT, self.config, self.declarations)

    def test_terminal_powers_keep_graph_sap_and_full_nr2_firewalls(self):
        config = json.loads((module.ROOT / 'formalization/terminal_powers/module.json').read_text())
        module.validate(module.ROOT, config, self.declarations)
        self.assertFalse(config.get('external_providers'))
        self.assertEqual(next(i for i in config['imports'] if i['id'] == 'I02')['provider_claims'], ['C25', 'C26'])
        for claim, forbidden in [('C06', 'A02'), ('C01', 'A03'), ('C18', 'I02'), ('C20', 'I01')]:
            bad = deepcopy(config)
            next(c for c in bad['claims'] if c['id'] == claim)['depends_on'].append(forbidden)
            with self.subTest(claim=claim, forbidden=forbidden), self.assertRaisesRegex(ValueError, 'firewall'):
                module.validate(module.ROOT, bad, self.declarations)


if __name__ == '__main__':
    unittest.main()
