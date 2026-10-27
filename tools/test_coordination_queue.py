"""Queue safety: races, priority, accepted dependencies, peer review and CI pins."""
from copy import deepcopy
import json
from pathlib import Path
import unittest

import coordination_queue as q


def ci(head='a' * 40, run=1):
    return {'run_id': run, 'head_sha': head, 'conclusion': 'success', 'axiom_audit': 'allowlist'}


class QueueTests(unittest.TestCase):
    def setUp(self):
        d = q.ROOT / q.DIRECTORY
        self.registry = json.loads((d / 'BOARD.json').read_text())
        self.policy = json.loads((d / 'AUTONOMY.json').read_text())
        self.state = {'schema_version': 1, 'protocol_version': 2, 'revision': 1,
                      'source_commit': self.registry['source_commit'],
                      'packages': {p['id']: {'state': 'AVAILABLE', 'owner_project_id': None}
                                   for p in self.registry['packages']},
                      'integration_lock': None, 'history': []}
        self.state['packages']['B001'].update(state='ACCEPTED', owner_project_id=1,
                                             accepted_commit='a' * 40, main_ci=ci())

    def step(self, state, project, event, **data):
        return q.transition(self.registry, self.policy, state, project, event, data)

    def claim(self, state=None, project=1, package='B002'):
        return self.step(self.state if state is None else state, project, 'claim',
                         package_id=package, base_main_sha='a' * 40, base_ci=ci())

    def submit(self, state, project=1, package='B002', head='b' * 40):
        return self.step(state, project, 'submit', package_id=package, head_sha=head,
                         ci=ci(head), pr_number=2,
                         report_path=f'{q.DIRECTORY}/submissions/{package}.md')

    def approved(self):
        s = self.submit(self.claim())
        s = self.step(s, 2, 'review', package_id='B002', head_sha='b' * 40)
        return self.step(s, 2, 'approve', package_id='B002', head_sha='b' * 40,
                         summary='Checked actual source quantifiers, all providers, consumer and exact-head CI.')

    def integrating(self):
        return self.step(self.approved(), 2, 'start_integration', package_id='B002',
                         head_sha='b' * 40, base_main_sha='a' * 40,
                         head_contains_main=True, ci=ci('b' * 40))

    def test_lowest_claim_and_no_speculative_state_mutation(self):
        result = self.claim()
        self.assertEqual(result['packages']['B002']['state'], 'IN_PROGRESS')
        self.assertEqual(self.state['packages']['B002']['state'], 'AVAILABLE')
        with self.assertRaisesRegex(ValueError, 'lowest'):
            self.claim(package='B003')

    def test_two_same_parent_claims_cannot_both_publish(self):
        one = self.claim(project=1)
        two = self.claim(project=2)
        self.assertEqual(one['packages']['B002']['owner_project_id'], 1)
        self.assertEqual(two['packages']['B002']['owner_project_id'], 2)
        published = q.compare_and_swap('old', 'old', self.state, one)
        with self.assertRaisesRegex(ValueError, 'Stale'):
            q.compare_and_swap('new', 'old', published, two)
        retry = self.claim(published, project=2, package='B003')
        self.assertEqual(retry['packages']['B002']['owner_project_id'], 1)
        self.assertEqual(retry['packages']['B003']['owner_project_id'], 2)

    def test_dependency_must_be_accepted_not_merely_submitted(self):
        s = self.claim(project=1)
        s = self.claim(s, project=2, package='B003')
        s = self.submit(s, project=2, package='B003')
        self.assertNotIn('B004', q.available(self.registry, self.policy, s))
        s['packages']['B003'].update(state='ACCEPTED', accepted_commit='c' * 40,
                                     main_ci=ci('c' * 40))
        self.assertIn('B004', q.available(self.registry, self.policy, s))

    def test_one_in_progress_and_submission_releases_slot(self):
        s = self.claim()
        with self.assertRaisesRegex(ValueError, 'resume'):
            self.claim(s, package='B003')
        s = self.submit(s)
        s = self.claim(s, package='B003')
        self.assertEqual(s['packages']['B002']['state'], 'SUBMITTED')
        self.assertEqual(s['packages']['B003']['state'], 'IN_PROGRESS')

    def test_foreign_review_has_idle_priority(self):
        s = self.submit(self.claim())
        self.assertEqual(q.next_action(self.registry, self.policy, s, 2),
                         {'action': 'review', 'package_id': 'B002'})
        with self.assertRaisesRegex(ValueError, 'lowest'):
            self.claim(s, project=2, package='B003')

    def test_foreign_review_unblocks_dependencies_at_next_checkpoint(self):
        s = self.claim()
        s = self.claim(s, project=2, package='B003')
        s = self.submit(s)
        self.assertEqual(q.next_action(self.registry, self.policy, s, 2),
                         {'action': 'review', 'package_id': 'B002'})
        s = self.step(s, 2, 'review', package_id='B002', head_sha='b' * 40)
        self.assertEqual(q.next_action(self.registry, self.policy, s, 2)['action'], 'resume_review')

    def test_self_review_rejected(self):
        s = self.submit(self.claim())
        with self.assertRaisesRegex(ValueError, 'own package'):
            self.step(s, 1, 'review', package_id='B002', head_sha='b' * 40)

    def test_pr_success_alone_never_accepts(self):
        s = self.submit(self.claim())
        with self.assertRaisesRegex(ValueError, 'locked reviewer'):
            self.step(s, 2, 'accept', package_id='B002', integration_commit='c' * 40,
                      main_ci=ci('c' * 40))

    def test_submission_ci_pins_exact_head(self):
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            self.step(self.claim(), 1, 'submit', package_id='B002', head_sha='b' * 40,
                      ci=ci('c' * 40), pr_number=2,
                      report_path=f'{q.DIRECTORY}/submissions/B002.md')

    def test_review_and_main_ci_bind_exact_commits(self):
        s = self.integrating()
        with self.assertRaisesRegex(ValueError, 'exact-head'):
            self.step(s, 2, 'accept', package_id='B002', integration_commit='c' * 40,
                      main_ci=ci('b' * 40))
        accepted = self.step(s, 2, 'accept', package_id='B002', integration_commit='c' * 40,
                             main_ci=ci('c' * 40))
        self.assertEqual(accepted['packages']['B002']['state'], 'ACCEPTED')
        self.assertIsNone(accepted['integration_lock'])

    def test_changed_submission_invalidates_review(self):
        s = self.approved()
        s = self.submit(s, head='d' * 40)
        self.assertNotIn('review', s['packages']['B002'])
        self.assertEqual(s['packages']['B002']['state'], 'SUBMITTED')

    def test_reviewer_base_update_clears_approval(self):
        s = self.step(self.approved(), 2, 'refresh_review', package_id='B002',
                      head_sha='d' * 40, ci=ci('d' * 40))
        self.assertFalse(s['packages']['B002']['review']['approved'])
        with self.assertRaisesRegex(ValueError, 'Approved'):
            self.step(s, 2, 'start_integration', package_id='B002', head_sha='d' * 40,
                      base_main_sha='a' * 40, head_contains_main=True, ci=ci('d' * 40))

    def test_integration_lock_blocks_new_claims(self):
        with self.assertRaisesRegex(ValueError, 'lowest'):
            self.claim(self.integrating(), project=1, package='B003')

    def test_integration_needs_current_main_in_reviewed_head(self):
        with self.assertRaisesRegex(ValueError, 'current main'):
            self.step(self.approved(), 2, 'start_integration', package_id='B002',
                      head_sha='b' * 40, base_main_sha='a' * 40,
                      head_contains_main=False, ci=ci('b' * 40))

    def test_failed_integration_retains_lock(self):
        s = self.step(self.integrating(), 2, 'block', package_id='B002', reason='Merged main CI failed')
        self.assertEqual(s['packages']['B002']['state'], 'INTEGRATING')
        self.assertIsNotNone(s['integration_lock'])
        with self.assertRaisesRegex(ValueError, 'failed merged-main'):
            self.step(s, 2, 'cancel_integration', package_id='B002', pr_not_merged=False)

    def test_premerge_cancellation_requires_fresh_review(self):
        s = self.step(self.integrating(), 2, 'cancel_integration', package_id='B002', pr_not_merged=True)
        self.assertIsNone(s['integration_lock'])
        self.assertFalse(s['packages']['B002']['review']['approved'])

    def test_whitelist_and_registration_are_authoritative(self):
        p = deepcopy(self.policy)
        p['released_packages'].remove('B002')
        self.assertEqual(q.next_action(self.registry, p, self.state, 1)['package_id'], 'B003')
        with self.assertRaisesRegex(ValueError, 'not registered'):
            q.next_action(self.registry, self.policy, self.state, 3)

    def test_unaccepted_shared_core_releases_no_downstream(self):
        s = deepcopy(self.state)
        s['packages']['B001'].update(state='IN_PROGRESS', owner_project_id=1)
        self.assertEqual(q.available(self.registry, self.policy, s), [])

    def test_repair_preserves_owner_and_obeys_priority(self):
        s = self.approved()
        s = self.step(s, 2, 'request_changes', package_id='B002', head_sha='b' * 40,
                      summary='A source premise is still an uninstantiated provider; repair the actual source wrapper.')
        self.assertEqual(q.next_action(self.registry, self.policy, s, 1)['action'], 'repair')
        s = self.step(s, 1, 'repair', package_id='B002', base_main_sha='a' * 40, base_ci=ci())
        self.assertEqual(s['packages']['B002']['owner_project_id'], 1)
        self.assertEqual(s['packages']['B002']['state'], 'IN_PROGRESS')


if __name__ == '__main__':
    unittest.main()
