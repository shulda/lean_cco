"""Fresh reviewer recovery preserves claims and cannot bootstrap wider powers."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import coordination_queue as q
from test_coordination_queue import LEGACY_B001, SUMMARY, ci, independence


NEW = ['independent_review_recovery', 'reviewer_recovery_control']
CONTROL = NEW[1]


class ReviewerRecoveryTests(unittest.TestCase):
    def setUp(self):
        directory = q.ROOT / q.DIRECTORY
        self.registry = json.loads((directory / 'BOARD.json').read_text())
        self.policy = json.loads((directory / 'AUTONOMY.json').read_text())
        self.old_policy = deepcopy(self.policy)
        for actor in NEW:
            del self.old_policy['actors'][actor]
        self.old_policy['revision'] -= 1
        self.state = {
            'schema_version': 1, 'protocol_version': 3, 'revision': 20,
            'policy_revision': self.old_policy['revision'],
            'source_commit': self.registry['source_commit'],
            'packages': {row['id']: {'state': 'AVAILABLE', 'owner_project_id': None}
                         for row in self.registry['packages']},
            'integration_lock': None, 'extra_provenance': {'original_heads': ['8' * 40]},
            'history': [{'revision': 20, 'event': 'previous-event', 'details': {'WIP': True}}],
            'infrastructure_integrations': [{'preserved_previous_integration': True}],
        }
        self.state['packages']['B001'] = deepcopy(LEGACY_B001)
        self.state = self.step(self.state, 'claim', package_id='B002',
                               base_main_sha='a' * 40, base_ci=ci())
        self.state = self.step(self.state, 'submit', package_id='B002',
                               head_sha='b' * 40, ci=ci('b' * 40), pr_number=3,
                               report_path=f'{q.DIRECTORY}/submissions/B002.md')
        self.state = self.step(self.state, 'review', actor='independent_review',
                               package_id='B002', head_sha='b' * 40, independence=independence())
        self.state = self.step(self.state, 'approve', actor='independent_review',
                               package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        self.state = self.step(self.state, 'start_integration', package_id='B002',
                               head_sha='b' * 40, base_main_sha='a' * 40,
                               head_contains_main=True, ci=ci('b' * 40))
        self.state = self.step(self.state, 'accept', package_id='B002',
                               integration_commit='c' * 40, main_ci=ci('c' * 40))
        self.state = self.step(self.state, 'claim', package_id='B003',
                               base_main_sha='c' * 40, base_ci=ci('c' * 40))
        self.state['packages']['B003']['handoff_history'] = [
            {'head_sha': '8' * 40, 'last_green_checkpoint': {'head_sha': '7' * 40}}]
        self.manifest = self.make_manifest()
        proof = independence()
        proof['identity'] = '/root/' + CONTROL
        self.start = dict(head_sha='d' * 40, base_main_sha='c' * 40,
                          pr_number=63, head_contains_main=True, ci=ci('d' * 40),
                          author_actor_ids=['root', '/root/reviewer_recovery_protocol'],
                          original_author_project_ids=[], reviewer_recovery=self.manifest,
                          unavailable_reviewer={
                              'actor_id': 'independent_review', 'identity': '/root/independent_review',
                              'reason': 'The registered agent failed twice because its inherited model is unsupported by the runtime; a retry of the same actual identity failed too.',
                              'report_path': f'{q.DIRECTORY}/reports/reviewer-runtime-failure.md'},
                          review={'actor_id': CONTROL, 'head_sha': 'd' * 40,
                                  'approved': True, 'summary': SUMMARY, 'independence': proof})
        self.finish = {'actor_id': 'root', 'head_sha': 'd' * 40,
                       'integration_commit': 'e' * 40, 'main_ci': ci('e' * 40, run=27)}

    def step(self, state, event, actor='root', **data):
        return q.transition(self.registry, self.old_policy, state, 3, event,
                            {'actor_id': actor, **data})

    def make_manifest(self, registry=None, policy=None):
        return q.reviewer_recovery_manifest(self.registry, self.old_policy,
                                            self.registry if registry is None else registry,
                                            self.policy if policy is None else policy,
                                            'independent_review', CONTROL)

    def locked(self, **overrides):
        return self.step(self.state, 'start_infrastructure', **{**deepcopy(self.start), **overrides})

    def promote(self, state=None, **overrides):
        values = dict(previous_registry=self.registry, previous_policy=self.old_policy,
                      registry=self.registry, policy=self.policy,
                      state=self.locked() if state is None else state, project=3, data=self.finish)
        values.update(overrides)
        return q.promote_reviewer(**values)

    def test_recovery_preserves_active_and_both_kinds_of_accepted_records_exactly(self):
        original = deepcopy((self.state, self.policy, self.old_policy, self.registry))
        locked = self.locked()
        self.assertEqual(locked['packages'], self.state['packages'])
        result = self.promote(locked)
        self.assertEqual((self.state, self.policy, self.old_policy, self.registry), original)
        self.assertEqual(result['packages'], self.state['packages'])
        self.assertEqual(result['history'][:-1], locked['history'])
        self.assertEqual(result['extra_provenance'], self.state['extra_provenance'])
        self.assertEqual(result['infrastructure_integrations'][:-1],
                         locked['infrastructure_integrations'])
        self.assertEqual(result['infrastructure_integrations'][-1]['reviewer_recovery'], self.manifest)
        self.assertEqual(result['policy_revision'], self.policy['revision'])
        self.assertEqual(result['revision'], locked['revision'] + 1)
        self.assertIsNone(result['integration_lock'])
        q.validate_state(self.registry, self.policy, result)

    def test_new_reader_can_review_active_batch_only_after_promotion(self):
        submitted = self.step(self.state, 'submit', package_id='B003', head_sha='f' * 40,
                              ci=ci('f' * 40), pr_number=4,
                              report_path=f'{q.DIRECTORY}/submissions/B003.md')
        data = {'actor_id': NEW[0], 'package_id': 'B003', 'head_sha': 'f' * 40,
                'independence': {**independence(), 'identity': '/root/' + NEW[0]}}
        with self.assertRaises(ValueError):
            q.transition(self.registry, self.old_policy, submitted, 3, 'review', data)
        locked = self.step(submitted, 'start_infrastructure', **self.start)
        promoted = self.promote(locked)
        reviewed = q.transition(self.registry, self.policy, promoted, 3, 'review', data)
        self.assertEqual(reviewed['packages']['B003']['review']['actor_id'], NEW[0])
        self.assertFalse(reviewed['packages']['B003']['review']['approved'])

    def test_no_old_actor_rename_removal_or_extra_permissions(self):
        for mutation in ['rename', 'remove', 'root-review', 'new-implement', 'new-coordinate', 'history']:
            policy = deepcopy(self.policy)
            if mutation == 'rename':
                policy['actors']['independent_review']['identity'] = '/root/renamed'
            elif mutation == 'remove':
                del policy['actors']['independent_review']
            elif mutation == 'root-review':
                policy['actors']['root']['roles'].append('review')
            elif mutation == 'history':
                policy['actors'][NEW[0]]['historical_author_projects'] = [2]
            else:
                policy['actors'][NEW[0]]['roles'].append(mutation.split('-')[1])
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.make_manifest(policy=policy)

    def test_no_changes_to_other_policy_or_catalogue_fields(self):
        for field, value in [('maximum_active_batches', 4), ('source_commit', '0' * 40),
                             ('released_packages', []), ('review_requires_non_author', False),
                             ('legacy_accepted_records', {})]:
            policy = deepcopy(self.policy)
            policy[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.make_manifest(policy=policy)
        for field, value in [('source_commit', '0' * 40), ('revision', 99), ('packages', [])]:
            registry = deepcopy(self.registry)
            registry[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.make_manifest(registry=registry)

    def test_revision_exactly_once_and_fresh_distinct_identities(self):
        for revision in [self.old_policy['revision'], self.policy['revision'] + 1, True]:
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                self.make_manifest(policy={**self.policy, 'revision': revision})
        policy = deepcopy(self.policy)
        policy['actors'][NEW[0]]['identity'] = '/root/independent_review'
        with self.assertRaisesRegex(ValueError, 'aliases'):
            self.make_manifest(policy=policy)
        with self.assertRaisesRegex(ValueError, 'genuinely new'):
            q.reviewer_recovery_manifest(self.registry, self.old_policy, self.registry,
                                         self.policy, 'independent_review', 'independent_review')
        with self.assertRaisesRegex(ValueError, 'unavailable'):
            q.reviewer_recovery_manifest(self.registry, self.old_policy, self.registry,
                                         self.policy, 'root', CONTROL)

    def test_manifest_tampering_and_unbound_policy_rejected(self):
        for key in ['previous_registry_sha256', 'previous_policy_sha256', 'registry_sha256', 'policy_sha256']:
            manifest = deepcopy(self.manifest)
            manifest[key] = '0' * 64
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.locked(reviewer_recovery=manifest)
        manifest = deepcopy(self.manifest)
        manifest['new_actors']['root'] = deepcopy(self.policy['actors'][NEW[0]])
        with self.assertRaises(ValueError):
            self.locked(reviewer_recovery=manifest)
        manifest = deepcopy(self.manifest)
        del manifest['policy_sha256']
        with self.assertRaises(ValueError):
            self.locked(reviewer_recovery=manifest)

    def test_actual_new_reader_identity_and_substantive_approval_required(self):
        for key, value in [('actor_id', 'independent_review'), ('head_sha', '0' * 40),
                           ('approved', False), ('summary', 'green')]:
            review = deepcopy(self.start['review'])
            review[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.locked(review=review)
        other = deepcopy(self.start['review'])
        other['actor_id'] = NEW[0]
        other['independence']['identity'] = '/root/' + NEW[0]
        with self.assertRaisesRegex(ValueError, 'manifest-bound'):
            self.locked(review=other)
        for key, value in [('identity', '/root/independent_review'), ('non_author', False),
                           ('summary', 'different ID'), ('report_path', 'tmp/review.md')]:
            review = deepcopy(self.start['review'])
            review['independence'][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.locked(review=review)

    def test_either_new_reader_authorship_in_infra_or_active_batch_rejected(self):
        for actor in NEW:
            for label in [actor, '/root/' + actor]:
                with self.subTest(actor=actor, label=label), self.assertRaises(ValueError):
                    self.locked(author_actor_ids=['root', label])
                state = deepcopy(self.state)
                state['packages']['B003']['author_actor_ids'].append(label)
                with self.subTest(actor=actor, label=label), self.assertRaises(ValueError):
                    self.step(state, 'start_infrastructure', **self.start)

    def test_unavailability_evidence_is_exact_and_durable(self):
        for key, value in [('actor_id', 'root'), ('identity', '/root/renamed'),
                           ('reason', 'unavailable'), ('report_path', '/tmp/failure.md')]:
            missing = deepcopy(self.start['unavailable_reviewer'])
            missing[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.locked(unavailable_reviewer=missing)
        with self.assertRaises(ValueError):
            self.locked(unavailable_reviewer=None)

    def test_no_active_review_or_approval_reuse(self):
        submitted = self.step(self.state, 'submit', package_id='B003', head_sha='f' * 40,
                              ci=ci('f' * 40), pr_number=4,
                              report_path=f'{q.DIRECTORY}/submissions/B003.md')
        reviewed = self.step(submitted, 'review', actor='independent_review',
                             package_id='B003', head_sha='f' * 40, independence=independence())
        with self.assertRaisesRegex(ValueError, 'without review'):
            self.step(reviewed, 'start_infrastructure', **self.start)

    def test_same_lock_failed_main_and_premerge_cancellation(self):
        locked = self.locked()
        with self.assertRaisesRegex(ValueError, 'lock'):
            self.step(locked, 'start_infrastructure', **self.start)
        with self.assertRaisesRegex(ValueError, 'failed merged-main'):
            self.step(locked, 'cancel_infrastructure', pr_not_merged=False)
        with self.assertRaisesRegex(ValueError, 'promote_reviewer'):
            self.step(locked, 'finish_infrastructure', integration_commit='e' * 40,
                       main_ci=ci('e' * 40))
        failed = deepcopy(self.finish)
        failed['main_ci']['conclusion'] = 'failure'
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            self.promote(locked, data=failed)
        self.assertIsNotNone(locked['integration_lock'])
        canceled = self.step(locked, 'cancel_infrastructure', pr_not_merged=True)
        self.assertEqual(canceled['policy_revision'], self.old_policy['revision'])
        self.assertEqual(canceled['packages'], self.state['packages'])
        self.assertIsNone(canceled['integration_lock'])

    def test_no_normal_revision_relaxation_or_wrong_snapshot_completion(self):
        locked = self.locked()
        with self.assertRaisesRegex(ValueError, 'revision mismatch'):
            q.validate_state(self.registry, self.policy, locked)
        for key, value in [('head_sha', '0' * 40), ('integration_commit', None),
                           ('main_ci', ci('0' * 40))]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.promote(locked, data={**self.finish, key: value})
        policy = deepcopy(self.policy)
        policy['actors'][NEW[0]]['identity'] = '/root/other-fresh-identity'
        with self.assertRaisesRegex(ValueError, 'complete reviewed'):
            self.promote(locked, policy=policy)
        with self.assertRaisesRegex(ValueError, 'lock holder'):
            self.promote(self.state)

    def test_no_registry_promotion_combination_or_normal_claim_under_lock(self):
        with self.assertRaisesRegex(ValueError, 'separate'):
            self.locked(registry_promotion={})
        with self.assertRaisesRegex(ValueError, 'lock'):
            self.step(self.locked(), 'claim', package_id='B006',
                       base_main_sha='c' * 40, base_ci=ci('c' * 40))

    def test_cli_requires_snapshots_and_preserves_claims(self):
        with tempfile.TemporaryDirectory() as folder:
            paths = {}
            for name, data in [('state', self.locked()), ('registry', self.registry),
                               ('policy', self.policy), ('old-policy', self.old_policy),
                               ('data', self.finish)]:
                path = Path(folder) / (name + '.json')
                path.write_text(json.dumps(data))
                paths[name] = str(path)
            output = Path(folder) / 'output.json'
            command = [sys.executable, str(q.ROOT / 'tools/coordination_queue.py'),
                       '--state', paths['state'], '--registry', paths['registry'],
                       '--policy', paths['policy'], '--project', '3', '--actor', 'root',
                       '--event', 'promote_reviewer', '--data', paths['data'], '--output', str(output)]
            rejected = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('explicit previous public', rejected.stderr)
            self.assertFalse(output.exists())
            result = subprocess.run(command + ['--previous-registry', paths['registry'],
                                              '--previous-policy', paths['old-policy']],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            proposed = json.loads(output.read_text())
            self.assertEqual(proposed['packages'], self.state['packages'])
            self.assertFalse(json.loads(result.stdout)['published'])


if __name__ == '__main__':
    unittest.main()
