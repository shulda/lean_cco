"""Work-team queue: authorship, capacity, exact heads, CAS and integration."""
from copy import deepcopy
import json
import unittest
import coordination_queue as q


def ci(head='a' * 40, run=1):
    return {'run_id': run, 'head_sha': head, 'conclusion': 'success', 'axiom_audit': 'allowlist'}


def independence():
    return {'identity': '/root/independent_review', 'non_author': True,
            'summary': 'Fresh review-only agent did not write or direct any code of this package, including the original projects work; actual provenance checked.',
            'report_path': 'formalization/coordination/reviews/test.md'}


LEGACY_B001 = {'state': 'ACCEPTED', 'owner_project_id': 1, 'head_sha': 'a1a709a0807fa59e7422ee79e95816c7ecd1fd45', 'pr_number': 1, 'accepted_commit': '34b7f1b055788dcf1c134f07fd6a89c123189a82', 'main_ci': {'run_id': 40533022306, 'head_sha': '34b7f1b055788dcf1c134f07fd6a89c123189a82', 'conclusion': 'success', 'axiom_audit': 'allowlist'}, 'review': {'project_id': 0, 'head_sha': 'a1a709a0807fa59e7422ee79e95816c7ecd1fd45', 'approved': True, 'summary': 'Preparation project checked the actual source quantifiers, all RAW/STRONG providers, finite-span consumer and exact-head plus integrated-main build/axiom audits.'}}


SUMMARY = 'Checked pinned source quantifiers and actual signatures, every provider discharge, root imports, meaningful consumer and exact-head CI/audit.'


class QueueTests(unittest.TestCase):
    def setUp(self):
        d = q.ROOT / q.DIRECTORY
        self.registry = json.loads((d / 'BOARD.json').read_text())
        self.policy = json.loads((d / 'AUTONOMY.json').read_text())
        self.legacy = {'schema_version': 1, 'protocol_version': 2, 'revision': 3,
                       'source_commit': self.registry['source_commit'],
                       'packages': {p['id']: {'state': 'AVAILABLE', 'owner_project_id': None}
                                    for p in self.registry['packages']},
                       'integration_lock': None,
                       'history': [{'revision': 2, 'project_id': 1, 'event': 'claim', 'package_id': 'B002'},
                                   {'revision': 3, 'project_id': 2, 'event': 'claim', 'package_id': 'B003'}]}
        self.legacy['packages']['B001'] = deepcopy(LEGACY_B001)
        for i, owner in [('B002', 1), ('B003', 2)]:
            self.legacy['packages'][i].update(state='IN_PROGRESS', owner_project_id=owner,
                                             claim_revision=owner + 1,
                                             base_main_sha='a' * 40, base_ci=ci())
        self.state = deepcopy(self.legacy)
        self.state['protocol_version'] = 3
        self.state['policy_revision'] = self.policy['revision']
        for ident, package in self.state['packages'].items():
            if ident != 'B001':
                package.clear()
                package.update(state='AVAILABLE', owner_project_id=None)

    def step(self, state, event, actor='root', **data):
        return q.transition(self.registry, self.policy, state, 3, event, {'actor_id': actor, **data})

    def claim(self, state=None, package='B002'):
        return self.step(self.state if state is None else state, 'claim',
                         package_id=package, base_main_sha='a' * 40, base_ci=ci())

    def submit(self, state, package='B002', head='b' * 40):
        return self.step(state, 'submit', package_id=package, head_sha=head, ci=ci(head), pr_number=3,
                         report_path=f'{q.DIRECTORY}/submissions/{package}.md')

    def reviewed(self):
        s = self.submit(self.claim())
        return self.step(s, 'review', actor='independent_review', package_id='B002', head_sha='b' * 40,
                         independence=independence())

    def approved(self):
        return self.step(self.reviewed(), 'approve', actor='independent_review', package_id='B002',
                         head_sha='b' * 40, summary=SUMMARY)

    def integrating(self):
        return self.step(self.approved(), 'start_integration', package_id='B002', head_sha='b' * 40,
                         base_main_sha='a' * 40, head_contains_main=True, ci=ci('b' * 40))

    def test_two_batches_same_team_and_completion_priority(self):
        s = self.claim()
        self.assertEqual(q.next_action(self.registry, self.policy, s, 3, 'root')['optional_second_claim'], 'B003')
        s = self.claim(s, 'B003')
        self.assertEqual(len(q.active_packages(s)), 2)
        self.assertEqual(q.next_action(self.registry, self.policy, s, 3, 'root')['action'], 'resume')
        with self.assertRaisesRegex(ValueError, 'Two active'):
            self.claim(s, 'B006')

    def test_submission_and_blocker_still_occupy_slots(self):
        s = self.claim(self.claim(), 'B003')
        s = self.submit(s)
        s = self.step(s, 'block', package_id='B003', reason='Concrete unresolved proof')
        self.assertEqual(len(q.active_packages(s)), 2)
        with self.assertRaisesRegex(ValueError, 'Two active'):
            self.claim(s, 'B006')

    def test_claim_lowest_and_no_speculative_mutation(self):
        s = self.claim()
        self.assertEqual(self.state['packages']['B002']['state'], 'AVAILABLE')
        with self.assertRaisesRegex(ValueError, 'lowest'):
            self.claim(package='B003')
        self.assertEqual(s['packages']['B002']['owner_project_id'], 3)

    def test_cas_loser_reloads(self):
        one, two = self.claim(), self.claim()
        q.compare_and_swap('old', 'old', self.state, one)
        with self.assertRaisesRegex(ValueError, 'Stale'):
            q.compare_and_swap('new', 'old', one, two)
        self.assertEqual(self.claim(one, 'B003')['revision'], one['revision'] + 1)

    def test_unaccepted_sibling_is_never_dependency(self):
        s = self.submit(self.claim(self.claim(), 'B003'), package='B003')
        self.assertNotIn('B004', q.available(self.registry, self.policy, s))

    def test_old_projects_stopped_and_root_cannot_self_review(self):
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            q.transition(self.registry, self.policy, self.state, 2, 'claim',
                         {'actor_id': 'legacy-project-2', 'package_id': 'B002'})
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            self.step(self.submit(self.claim()), 'review', package_id='B002', head_sha='b' * 40,
                      independence=independence())

    def test_different_role_is_not_independence(self):
        s = self.submit(self.claim())
        s['packages']['B002']['author_actor_ids'].append('independent_review')
        with self.assertRaisesRegex(ValueError, 'eligible'):
            self.step(s, 'review', actor='independent_review', package_id='B002', head_sha='b' * 40,
                      independence=independence())
        s['packages']['B002']['author_actor_ids'].remove('independent_review')
        self.policy['actors']['independent_review']['historical_author_projects'] = [1]
        s['packages']['B002']['original_author_project_ids'] = [1]
        with self.assertRaisesRegex(ValueError, 'eligible'):
            self.step(s, 'review', actor='independent_review', package_id='B002', head_sha='b' * 40,
                      independence=independence())

    def test_identity_alias_and_missing_independence_rejected(self):
        self.policy['actors']['independent_review']['identity'] = '/root'
        with self.assertRaisesRegex(ValueError, 'aliases'):
            q.validate_policy(self.registry, self.policy)
        self.policy['actors']['independent_review']['identity'] = '/root/independent_review'
        with self.assertRaisesRegex(ValueError, 'actual non-author'):
            self.step(self.submit(self.claim()), 'review', actor='independent_review', package_id='B002',
                      head_sha='b' * 40, independence={})

    def test_control_role_cannot_write_implementation(self):
        with self.assertRaisesRegex(ValueError, 'cannot implement'):
            self.step(self.claim(), 'record_authorship', package_id='B002', author_actor_ids=['independent_review'])

    def test_source_review_exact_head_and_ci(self):
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            self.step(self.claim(), 'submit', package_id='B002', head_sha='b' * 40, ci=ci('c' * 40),
                      pr_number=3, report_path=f'{q.DIRECTORY}/submissions/B002.md')
        with self.assertRaisesRegex(ValueError, 'head mismatch'):
            self.step(self.reviewed(), 'approve', actor='independent_review', package_id='B002',
                      head_sha='c' * 40, summary=SUMMARY)

    def test_changed_head_invalidates_review(self):
        s = self.submit(self.approved(), head='d' * 40)
        self.assertNotIn('review', s['packages']['B002'])
        s = self.step(self.approved(), 'refresh_review', actor='independent_review', package_id='B002',
                      head_sha='d' * 40, ci=ci('d' * 40))
        self.assertFalse(s['packages']['B002']['review']['approved'])

    def test_coordinator_automatic_integration_after_independent_review(self):
        s = self.integrating()
        self.assertEqual(s['integration_lock']['actor_id'], 'root')
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            self.step(s, 'accept', package_id='B002', integration_commit='c' * 40, main_ci=ci('b' * 40))
        s = self.step(s, 'accept', package_id='B002', integration_commit='c' * 40, main_ci=ci('c' * 40))
        self.assertEqual(s['packages']['B002']['state'], 'ACCEPTED')
        self.assertIsNone(s['integration_lock'])

    def test_green_submission_does_not_accept(self):
        with self.assertRaisesRegex(ValueError, 'locked integrator'):
            self.step(self.submit(self.claim()), 'accept', package_id='B002', integration_commit='c' * 40,
                      main_ci=ci('c' * 40))

    def test_lock_ancestry_and_failed_main(self):
        with self.assertRaisesRegex(ValueError, 'current main'):
            self.step(self.approved(), 'start_integration', package_id='B002', head_sha='b' * 40,
                      base_main_sha='a' * 40, head_contains_main=False, ci=ci('b' * 40))
        s = self.integrating()
        with self.assertRaisesRegex(ValueError, 'lock'):
            self.claim(s, 'B003')
        s = self.step(s, 'block', package_id='B002', reason='Merged main failed CI')
        self.assertIsNotNone(s['integration_lock'])
        with self.assertRaisesRegex(ValueError, 'failed merged-main'):
            self.step(s, 'cancel_integration', package_id='B002', pr_not_merged=False)
        s = self.step(s, 'cancel_integration', package_id='B002', pr_not_merged=True)
        self.assertFalse(s['packages']['B002']['review']['approved'])

    def test_repair_precedes_resume_and_claim(self):
        s = self.step(self.reviewed(), 'request_changes', actor='independent_review', package_id='B002',
                      head_sha='b' * 40, summary=SUMMARY)
        self.assertEqual(q.next_action(self.registry, self.policy, s, 3, 'root')['action'], 'repair')
        with self.assertRaisesRegex(ValueError, 'Repairs'):
            self.claim(s, 'B003')
        s = self.step(s, 'repair', package_id='B002', base_main_sha='a' * 40, base_ci=ci())
        self.assertEqual(s['packages']['B002']['state'], 'IN_PROGRESS')

    def third(self, state):
        return self.step(state, 'claim_third', package_id='B006', base_main_sha='a' * 40, base_ci=ci(),
                         independent_active_work=True, summary=SUMMARY,
                         implementation_actor_id='/root/b006', active_work_items=['CCO/B006.lean'],
                         independence_report_path='formalization/coordination/reports/third-B006.md',
                         existing_batches=[{'package_id': i, 'head_sha': 'a' * 40,
                                            'work_items': [f'CCO/{i}.lean'],
                                            'implementation_actor_ids': [f'/root/{i}']} for i in ['B002', 'B003']])

    def test_third_requires_concrete_current_independent_active_work(self):
        s = self.claim(self.claim(), 'B003')
        with self.assertRaisesRegex(ValueError, 'anchored report'):
            self.step(s, 'claim_third', package_id='B006', base_main_sha='a' * 40, base_ci=ci())
        third = self.third(s)
        self.assertEqual(len(q.active_packages(third)), 3)
        self.assertIn('existing_batches', third['third_batch_exception'])
        with self.assertRaisesRegex(ValueError, 'Two active'):
            self.claim(third, 'B017')
        corrupted = deepcopy(third)
        corrupted.pop('third_batch_exception')
        with self.assertRaisesRegex(ValueError, 'Third batch'):
            q.validate_state(self.registry, self.policy, corrupted)

    def transfer(self, ident, owner):
        return {'package_id': ident, 'previous_owner_project_id': owner,
                'branch': 'project1/B002-raw-exact' if owner == 1 else 'p2-b003-strong-exact',
                'pr_number': 2 + owner, 'head_sha': str(owner) * 40,
                'observed_ci': {'head_sha': str(owner) * 40, 'run_id': 5, 'conclusion': 'failure'},
                'last_green_checkpoint': {'head_sha': 'a' * 40, 'ci': ci()}}

    def test_checkpoint_preserves_work_state_claim_authorship_and_last_green(self):
        s = self.step(self.legacy, 'handoff', previous_projects_stopped=True,
                      transfers=[self.transfer('B002', 1), self.transfer('B003', 2)])
        old = deepcopy(s['packages']['B002'])
        for conclusion in ['failure', 'success']:
            s = self.step(s, 'checkpoint', package_id='B002', head_sha='d' * 40, pr_number=3,
                          observed_ci={'head_sha': 'd' * 40, 'run_id': 123, 'conclusion': conclusion})
            p = s['packages']['B002']
            self.assertEqual(p['state'], 'IN_PROGRESS')
            self.assertEqual(p['head_sha'], 'd' * 40)
            self.assertEqual(p['observed_ci']['conclusion'], conclusion)
            for key in ['claim_revision', 'base_main_sha', 'base_ci', 'author_actor_ids',
                        'original_author_project_ids', 'handoff_history', 'last_green_checkpoint', 'branch']:
                self.assertEqual(p[key], old[key])
        self.assertEqual(s['history'][-1]['event'], 'checkpoint')
        self.assertEqual(len(q.active_packages(s)), 2)

    def test_checkpoint_rejects_nonowner_or_leased_work_and_wrong_pr_or_ci(self):
        for state in [self.submit(self.claim()), self.reviewed(), self.integrating()]:
            with self.assertRaisesRegex(ValueError, 'unleased IN_PROGRESS'):
                self.step(state, 'checkpoint', package_id='B002', head_sha='d' * 40, pr_number=3,
                          observed_ci={'head_sha': 'd' * 40, 'run_id': 123, 'conclusion': 'failure'})
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            q.transition(self.registry, self.policy, self.claim(), 2, 'checkpoint',
                         {'actor_id': 'root', 'package_id': 'B002'})
        s = self.step(self.claim(), 'checkpoint', package_id='B002', head_sha='d' * 40, pr_number=3,
                      observed_ci={'head_sha': 'd' * 40, 'run_id': 123, 'conclusion': 'failure'})
        with self.assertRaisesRegex(ValueError, 'preserves the existing WIP PR'):
            self.step(s, 'checkpoint', package_id='B002', head_sha='d' * 40, pr_number=99,
                      observed_ci={'head_sha': 'd' * 40, 'run_id': 123, 'conclusion': 'failure'})
        for observed in [{'head_sha': 'c' * 40, 'run_id': 123, 'conclusion': 'failure'},
                         {'head_sha': 'd' * 40, 'run_id': 123, 'conclusion': 'pending'}]:
            with self.assertRaisesRegex(ValueError, 'exact WIP head'):
                self.step(s, 'checkpoint', package_id='B002', head_sha='d' * 40, pr_number=3,
                          observed_ci=observed)

    def test_atomic_handoff_preserves_claim_history_wip_and_original_authorship(self):
        s = self.step(self.legacy, 'handoff', previous_projects_stopped=True,
                      transfers=[self.transfer('B002', 1), self.transfer('B003', 2)])
        self.assertEqual(s['protocol_version'], 3)
        self.assertEqual(s['history'][:-1], self.legacy['history'])
        for ident, owner in [('B002', 1), ('B003', 2)]:
            p = s['packages'][ident]
            self.assertEqual(p['owner_project_id'], 3)
            self.assertEqual(p['claim_revision'], self.legacy['packages'][ident]['claim_revision'])
            self.assertEqual(p['original_author_project_ids'], [owner])
            self.assertIn(f'legacy-project-{owner}', p['author_actor_ids'])
            self.assertEqual(p['observed_ci']['conclusion'], 'failure')
            self.assertEqual(p['head_sha'], str(owner) * 40)
        with self.assertRaisesRegex(ValueError, 'atomically'):
            self.step(self.legacy, 'handoff', previous_projects_stopped=True, transfers=[self.transfer('B002', 1)])
        with self.assertRaisesRegex(ValueError, 'Old live state'):
            self.claim(self.legacy)

    def infra(self, state):
        return self.step(state, 'start_infrastructure', head_sha='b' * 40, base_main_sha='a' * 40,
                         pr_number=5, head_contains_main=True, ci=ci('b' * 40), author_actor_ids=['root'],
                         review={'actor_id': 'independent_review', 'head_sha': 'b' * 40,
                                 'approved': True, 'summary': SUMMARY, 'independence': independence()})

    def test_infrastructure_uses_same_lock_before_and_after_handoff(self):
        for initial in [self.legacy, self.state]:
            s = self.infra(initial)
            with self.assertRaisesRegex(ValueError, 'lock'):
                self.infra(s)
            with self.assertRaisesRegex(ValueError, 'failed merged-main'):
                self.step(s, 'cancel_infrastructure', pr_not_merged=False)
            s = self.step(s, 'finish_infrastructure', integration_commit='c' * 40, main_ci=ci('c' * 40))
            self.assertIsNone(s['integration_lock'])
            self.assertEqual(s['infrastructure_integrations'][0]['pr_number'], 5)

    def test_legacy_acceptance_exemption_is_immutable_and_narrow(self):
        s = deepcopy(self.state)
        s['packages']['B001']['review']['summary'] = 'Changed old approval'
        with self.assertRaisesRegex(ValueError, 'Immutable legacy'):
            q.validate_state(self.registry, self.policy, s)
        s['packages']['B001'].pop('review')
        with self.assertRaisesRegex(ValueError, 'Immutable legacy'):
            q.validate_state(self.registry, self.policy, s)

    def test_direct_acceptance_without_review_is_invalid(self):
        s = self.claim()
        s['packages']['B002'].update(state='ACCEPTED', accepted_commit='c' * 40, main_ci=ci('c' * 40))
        with self.assertRaisesRegex(ValueError, 'Acceptance needs approved'):
            q.validate_state(self.registry, self.policy, s)
        s = self.step(self.integrating(), 'accept', package_id='B002',
                      integration_commit='c' * 40, main_ci=ci('c' * 40))
        s['packages']['B002'].pop('ci')
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            q.validate_state(self.registry, self.policy, s)

    def test_state_policy_revision_and_lock_actor_are_validated(self):
        s = deepcopy(self.state)
        s['policy_revision'] -= 1
        with self.assertRaisesRegex(ValueError, 'revision mismatch'):
            q.validate_state(self.registry, self.policy, s)
        s = self.integrating()
        s['integration_lock']['actor_id'] = 'legacy-project-2'
        with self.assertRaisesRegex(ValueError, 'lock mismatch'):
            q.validate_state(self.registry, self.policy, s)


if __name__ == '__main__':
    unittest.main()
