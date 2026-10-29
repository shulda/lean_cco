"""Additive registry deployment preserves the existing live queue and its gates."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import coordination_queue as q
from test_coordination_queue import LEGACY_B001, SUMMARY, ci, independence


class RegistryPromotionTests(unittest.TestCase):
    def setUp(self):
        directory = q.ROOT / q.DIRECTORY
        self.old_registry = json.loads((directory / 'BOARD.json').read_text())
        self.old_policy = json.loads((directory / 'AUTONOMY.json').read_text())
        self.state = {
            'schema_version': 1, 'protocol_version': 3, 'revision': 20,
            'policy_revision': self.old_policy['revision'],
            'source_commit': self.old_registry['source_commit'],
            'packages': {row['id']: {'state': 'AVAILABLE', 'owner_project_id': None}
                         for row in self.old_registry['packages']},
            'integration_lock': None,
            'history': [{'revision': 20, 'event': 'previous-event',
                         'details': {'preserved_history': ['original', 'WIP']}}],
            'infrastructure_integrations': [{'preserved_previous_integration': True}],
            'extra_provenance': {'original_heads': ['1' * 40, '2' * 40]},
        }
        self.state['packages']['B001'] = deepcopy(LEGACY_B001)
        # A valid, non-legacy acceptance must be preserved just as exactly as B001.
        self.state = self.old_step(self.state, 'claim', package_id='B002',
                                   base_main_sha='a' * 40, base_ci=ci())
        self.state = self.old_step(self.state, 'submit', package_id='B002',
                                   head_sha='b' * 40, ci=ci('b' * 40), pr_number=3,
                                   report_path=f'{q.DIRECTORY}/submissions/B002.md')
        self.state = self.old_step(self.state, 'review', actor='independent_review',
                                   package_id='B002', head_sha='b' * 40,
                                   independence=independence())
        self.state = self.old_step(self.state, 'approve', actor='independent_review',
                                   package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        self.state = self.old_step(self.state, 'start_integration', package_id='B002',
                                   head_sha='b' * 40, base_main_sha='a' * 40,
                                   head_contains_main=True, ci=ci('b' * 40))
        self.state = self.old_step(self.state, 'accept', package_id='B002',
                                   integration_commit='c' * 40, main_ci=ci('c' * 40))
        self.state['packages']['B002']['handoff_history'] = [
            {'head_sha': '8' * 40, 'last_green_checkpoint': {'head_sha': '7' * 40}}]
        self.unlocked = deepcopy(self.state)
        self.registry = deepcopy(self.old_registry)
        new_rows = []
        for ident, dependencies in [('B900', ['B001']), ('B901', ['B900'])]:
            row = deepcopy(self.old_registry['packages'][-1])
            row.update(id=ident, name=f'Test {ident}', state='PLANNED',
                       owner_project_id=None, accepted_commit=None,
                       depends_on=dependencies,
                       spec_file=f'formalization/coordination/packages/{ident}.md',
                       claims={'test_geometry': ['C01']})
            new_rows.append(row)
        self.registry['packages'].extend(new_rows)
        self.policy = deepcopy(self.old_policy)
        self.policy['revision'] += 1
        self.policy['released_packages'].extend(['B900', 'B901'])
        self.manifest = q.registry_promotion_manifest(
            self.old_registry, self.old_policy, self.registry, self.policy)
        self.state = self.old_step(
            self.state, 'start_infrastructure', head_sha='d' * 40,
            base_main_sha='c' * 40, head_contains_main=True, ci=ci('d' * 40),
            pr_number=26, author_actor_ids=['root', '/root/registry_promotion'],
            original_author_project_ids=[], registry_promotion=self.manifest,
            review={'actor_id': 'independent_review', 'head_sha': 'd' * 40,
                    'approved': True, 'summary': SUMMARY,
                    'independence': independence()})
        self.data = {'actor_id': 'root', 'package_ids': ['B900', 'B901'],
                     'head_sha': 'd' * 40,
                     'integration_commit': 'e' * 40, 'main_ci': ci('e' * 40, run=27)}

    def old_step(self, state, event, actor='root', **data):
        return q.transition(self.old_registry, self.old_policy, state, 3, event,
                            {'actor_id': actor, **data})

    def promote(self, **overrides):
        values = {'previous_registry': self.old_registry, 'previous_policy': self.old_policy,
                  'registry': self.registry, 'policy': self.policy, 'state': self.state,
                  'project': 3, 'data': self.data}
        values.update(overrides)
        return q.promote_registry(**values)

    def manifest_for(self, registry=None, policy=None):
        return q.registry_promotion_manifest(
            self.old_registry, self.old_policy,
            self.registry if registry is None else registry,
            self.policy if policy is None else policy)

    def test_atomic_promotion_preserves_every_existing_record_and_history(self):
        original = deepcopy((self.old_registry, self.old_policy, self.registry,
                             self.policy, self.state, self.data))
        result = self.promote()
        self.assertEqual((self.old_registry, self.old_policy, self.registry,
                          self.policy, self.state, self.data), original)
        self.assertEqual(result['revision'], self.state['revision'] + 1)
        self.assertEqual(result['policy_revision'], self.policy['revision'])
        self.assertEqual(result['history'][:-1], self.state['history'])
        self.assertEqual(result['history'][-1]['event'], 'promote_registry')
        self.assertEqual(result['extra_provenance'], self.state['extra_provenance'])
        for ident, record in self.state['packages'].items():
            self.assertEqual(result['packages'][ident], record, ident)
        for ident in ['B900', 'B901']:
            self.assertEqual(result['packages'][ident],
                             {'state': 'AVAILABLE', 'owner_project_id': None})
        self.assertIsNone(result['integration_lock'])
        self.assertEqual(result['infrastructure_integrations'][:-1],
                         self.state['infrastructure_integrations'])
        finished = result['infrastructure_integrations'][-1]
        for key, value in self.state['integration_lock'].items():
            self.assertEqual(finished[key], value, key)
        self.assertEqual(finished['integration_commit'], self.data['integration_commit'])
        self.assertEqual(finished['main_ci'], self.data['main_ci'])
        q.validate_state(self.registry, self.policy, result)

    def test_old_catalogue_rows_cannot_be_edited_removed_or_reordered(self):
        variants = []
        edited = deepcopy(self.registry)
        edited['packages'][1]['depends_on'] = []
        variants.append(edited)
        removed = deepcopy(self.registry)
        del removed['packages'][1]
        variants.append(removed)
        reordered = deepcopy(self.registry)
        reordered['packages'][0:2] = reversed(reordered['packages'][0:2])
        variants.append(reordered)
        for registry in variants:
            with self.subTest(registry=registry['packages'][0]['id']):
                with self.assertRaises(ValueError):
                    self.manifest_for(registry=registry)

    def test_catalogue_source_and_unrelated_metadata_cannot_change(self):
        for key, value in [('source_commit', 'f' * 40),
                           ('public_repository', 'other/repository'),
                           ('projects', [])]:
            registry = deepcopy(self.registry)
            registry[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.manifest_for(registry=registry)

    def test_policy_only_appends_new_release_ids_and_one_revision(self):
        variants = []
        changed_roles = deepcopy(self.policy)
        changed_roles['actors']['root']['roles'].append('review')
        variants.append(changed_roles)
        changed_limit = deepcopy(self.policy)
        changed_limit['maximum_active_batches'] = 4
        variants.append(changed_limit)
        dropped_release = deepcopy(self.policy)
        dropped_release['released_packages'].remove('B002')
        variants.append(dropped_release)
        reordered_release = deepcopy(self.policy)
        reordered_release['released_packages'][0:2] = reversed(
            reordered_release['released_packages'][0:2])
        variants.append(reordered_release)
        for revision in [self.old_policy['revision'], self.old_policy['revision'] + 2]:
            changed_revision = deepcopy(self.policy)
            changed_revision['revision'] = revision
            variants.append(changed_revision)
        for policy in variants:
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                self.manifest_for(policy=policy)

    def test_new_catalogue_must_be_nonempty_unique_and_match_release_ids(self):
        for mutate in [
                lambda registry, policy, data: registry['packages'].append(
                    deepcopy(registry['packages'][-1])),
                lambda registry, policy, data: policy['released_packages'].append('B901'),
                lambda registry, policy, data: policy['released_packages'].remove('B901'),
                lambda registry, policy, data: data.update(package_ids=['B900']),
                lambda registry, policy, data: data.update(package_ids=['B900', 'B900']),
                lambda registry, policy, data: data.update(package_ids=[]),
        ]:
            registry, policy, data = deepcopy((self.registry, self.policy, self.data))
            mutate(registry, policy, data)
            with self.subTest(data=data), self.assertRaises(ValueError):
                if data == self.data:
                    self.manifest_for(registry=registry, policy=policy)
                else:
                    self.promote(registry=registry, policy=policy, data=data)
        with self.assertRaises(ValueError):
            self.promote(registry=deepcopy(self.old_registry),
                         policy=deepcopy(self.old_policy), data={**self.data, 'package_ids': []})

    def test_new_dependency_graph_rejects_unknown_self_and_indirect_cycles(self):
        for dependencies in [['B999'], ['B900'], ['B901']]:
            registry = deepcopy(self.registry)
            registry['packages'][-2]['depends_on'] = dependencies
            with self.subTest(dependencies=dependencies), self.assertRaises(ValueError):
                self.manifest_for(registry=registry)

    def test_new_rows_are_prepared_contracts_without_preassigned_claims(self):
        for key, value in [('state', 'ACCEPTED'), ('owner_project_id', 3),
                           ('accepted_commit', 'e' * 40), ('contract_revision', 0),
                           ('name', ''), ('scope', ''), ('claims', {}),
                           ('spec_file', 'formalization/coordination/packages/B999.md')]:
            registry = deepcopy(self.registry)
            registry['packages'][-1][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.manifest_for(registry=registry)

    def test_promotion_requires_valid_reviewed_infrastructure_lock(self):
        mutations = [
            lambda state: state.update(integration_lock=None),
            lambda state: state['integration_lock'].update(kind='package'),
            lambda state: state['integration_lock'].update(head_sha='bad'),
            lambda state: state['integration_lock']['review'].update(approved=False),
            lambda state: state['integration_lock']['review'].update(head_sha='f' * 40),
            lambda state: state['integration_lock']['ci'].update(axiom_audit='not_run'),
        ]
        for mutate in mutations:
            state = deepcopy(self.state)
            mutate(state)
            with self.subTest(state=state['integration_lock']), self.assertRaises(ValueError):
                self.promote(state=state)

    def test_promotion_is_bound_to_the_reviewed_snapshots_and_head(self):
        with self.assertRaises(ValueError):
            self.promote(data={**self.data, 'head_sha': 'f' * 40})
        for key in ['previous_registry_sha256', 'previous_policy_sha256',
                    'registry_sha256', 'policy_sha256']:
            state = deepcopy(self.state)
            state['integration_lock']['registry_promotion'][key] = '0' * 64
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.promote(state=state)
        # A different but internally append-only snapshot pair cannot replace
        # the actual pair committed when the reviewed integration was locked.
        old_registry, registry = deepcopy((self.old_registry, self.registry))
        old_registry['packages'][1]['scope'] += ' substituted'
        registry['packages'][1]['scope'] += ' substituted'
        with self.assertRaises(ValueError):
            self.promote(previous_registry=old_registry, registry=registry)

    def test_promotion_lock_cannot_be_finished_without_adding_the_registry(self):
        with self.assertRaises(ValueError):
            self.old_step(self.state, 'finish_infrastructure',
                          integration_commit='e' * 40, main_ci=ci('e' * 40))

    def test_promotion_is_only_for_coordinate_integrator_and_same_lock_holder(self):
        for actor, project in [('independent_review', 3), ('legacy-project-2', 3),
                               ('root', 2)]:
            with self.subTest(actor=actor, project=project), self.assertRaises(ValueError):
                self.promote(project=project, data={**self.data, 'actor_id': actor})
        policy = deepcopy(self.old_policy)
        policy['actors']['another_coordinator'] = {
            'identity': '/root/another_coordinator',
            'roles': ['coordinate', 'integrate'], 'historical_author_projects': []}
        new_policy = deepcopy(policy)
        new_policy['revision'] += 1
        new_policy['released_packages'].extend(['B900', 'B901'])
        with self.assertRaises(ValueError):
            self.promote(previous_policy=policy, policy=new_policy,
                         data={**self.data, 'actor_id': 'another_coordinator'})

    def test_promotion_waits_for_actual_resulting_main_successful_audit(self):
        variants = [
            {**self.data, 'integration_commit': 'bad'},
            {**self.data, 'main_ci': ci('d' * 40)},
            {**self.data, 'main_ci': {**ci('e' * 40), 'conclusion': 'failure'}},
            {**self.data, 'main_ci': {**ci('e' * 40), 'axiom_audit': 'not_run'}},
            {**self.data, 'main_ci': {**ci('e' * 40), 'run_id': 0}},
            {key: value for key, value in self.data.items() if key != 'main_ci'},
        ]
        for data in variants:
            with self.subTest(data=data), self.assertRaises(ValueError):
                self.promote(data=data)
        self.assertIsNotNone(self.state['integration_lock'])

    def test_old_invalid_state_is_not_repaired_by_registry_promotion(self):
        for mutate in [
                lambda state: state.update(source_commit='f' * 40),
                lambda state: state.update(policy_revision=999),
                lambda state: state['packages']['B001'].update(accepted_commit='f' * 40),
                lambda state: state['packages']['B002']['review'].update(approved=False),
                lambda state: state['packages'].pop('B003'),
        ]:
            state = deepcopy(self.state)
            mutate(state)
            with self.subTest(state=state['revision']), self.assertRaises(ValueError):
                self.promote(state=state)

    def test_active_claim_prevents_registry_deployment(self):
        active = self.old_step(self.unlocked, 'claim', package_id='B003',
                               base_main_sha='c' * 40, base_ci=ci('c' * 40))
        q.validate_state(self.old_registry, self.old_policy, active)
        lock = self.state['integration_lock']
        with self.assertRaises(ValueError):
            self.old_step(active, 'start_infrastructure', head_sha=lock['head_sha'],
                          base_main_sha=lock['base_main_sha'], head_contains_main=True,
                          ci=lock['ci'], pr_number=lock['pr_number'],
                          author_actor_ids=lock['author_actor_ids'],
                          original_author_project_ids=lock['original_author_project_ids'],
                          review=lock['review'], registry_promotion=self.manifest)
        active['integration_lock'] = deepcopy(self.state['integration_lock'])
        with self.assertRaises(ValueError):
            self.promote(state=active)

    def test_normal_events_and_validation_still_reject_registry_mismatch(self):
        with self.assertRaises(ValueError):
            q.validate_state(self.registry, self.policy, self.state)
        with self.assertRaises(ValueError):
            q.transition(self.registry, self.policy, self.state, 3, 'finish_infrastructure',
                         self.data)

    def test_stale_cas_cannot_publish_or_replay_registry_additions(self):
        proposed = self.promote()
        q.compare_and_swap('observed-parent', 'observed-parent', self.state, proposed)
        with self.assertRaises(ValueError):
            q.compare_and_swap('different-parent', 'observed-parent', self.state, proposed)
        with self.assertRaises(ValueError):
            self.promote(state=proposed)

    def test_new_dependencies_are_unavailable_until_accepted(self):
        result = self.promote()
        available = q.available(self.registry, self.policy, result)
        self.assertIn('B900', available)
        self.assertNotIn('B901', available)
        with self.assertRaises(ValueError):
            q.transition(self.registry, self.policy, result, 3, 'claim',
                         {'actor_id': 'root', 'package_id': 'B901',
                          'base_main_sha': 'e' * 40, 'base_ci': ci('e' * 40)})

    def test_cli_requires_both_previous_snapshots_and_preserves_output_on_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            values = {'old-registry': self.old_registry, 'old-policy': self.old_policy,
                      'registry': self.registry, 'policy': self.policy,
                      'state': self.state, 'data': self.data}
            for name, value in values.items():
                (directory / f'{name}.json').write_text(json.dumps(value))
            output = directory / 'proposed.json'
            command = [sys.executable, str(q.ROOT / 'tools/coordination_queue.py'),
                       '--state', str(directory / 'state.json'),
                       '--registry', str(directory / 'registry.json'),
                       '--policy', str(directory / 'policy.json'),
                       '--project', '3', '--actor', 'root', '--event', 'promote_registry',
                       '--data', str(directory / 'data.json'), '--output', str(output)]
            for flags in [[], ['--previous-registry', str(directory / 'old-registry.json')]]:
                output.write_text('preserved-output')
                failure = subprocess.run(command + flags, capture_output=True, text=True)
                self.assertNotEqual(failure.returncode, 0)
                self.assertEqual(output.read_text(), 'preserved-output')
            successful = subprocess.run(command + [
                '--previous-registry', str(directory / 'old-registry.json'),
                '--previous-policy', str(directory / 'old-policy.json')],
                capture_output=True, text=True)
            self.assertEqual(successful.returncode, 0, successful.stderr)
            self.assertEqual(json.loads(output.read_text()), self.promote())


if __name__ == '__main__':
    unittest.main()
