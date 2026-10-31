import json
import unittest
from copy import deepcopy

import coordination_queue as q
import coordination_profiles as p
from test_coordination_queue import ci, independence, SUMMARY


class ExecutionProfilesTests(unittest.TestCase):
    def setUp(self):
        from test_coordination_queue import QueueTests
        fixture = QueueTests()
        fixture.setUp()
        self.registry, self.policy, self.state = deepcopy((
            fixture.registry, fixture.policy, fixture.state))
        self.state.update(execution_mode='chat', claims_paused=False)

    def step(self, state, event, worker=1, **data):
        return q.transition(self.registry, self.policy, state, worker + 3, event,
                            {'actor_id': f'chat-{worker}', **data})

    def claim(self, state=None, worker=1):
        state = self.state if state is None else state
        candidate = q.available(self.registry, self.policy, state)[0]
        return self.step(state, 'claim', worker, package_id=candidate,
                         base_main_sha='a' * 40, base_ci=ci())

    def submit(self, state, ident='B002', worker=1, head='b' * 40):
        return self.step(state, 'submit', worker, package_id=ident, head_sha=head,
                         ci=ci(head), pr_number=70,
                         report_path=f'{q.DIRECTORY}/submissions/{ident}.md')

    def review(self, state, ident='B002', worker=2):
        actual = self.policy['actors'][f'chat-{worker}']['identity']
        return self.step(state, 'review', worker, package_id=ident,
                         head_sha=state['packages'][ident]['head_sha'],
                         independence={**independence(), 'identity': actual})

    def approved(self):
        return self.step(self.review(self.submit(self.claim())), 'approve', 2,
                         package_id='B002', head_sha='b' * 40, summary=SUMMARY)

    def mode_data(self, **extra):
        return dict(user_authorized=True, summary=SUMMARY, base_main_sha='a' * 40,
                    base_ci=ci(), **extra)

    def pause(self, state):
        return self.step(state, 'pause_claims', **self.mode_data())

    def transfer(self, state, ident, owner=3):
        item = state['packages'][ident]
        return {'package_id': ident, 'previous_owner_project_id': item['owner_project_id'],
                'new_owner_project_id': owner,
                'head_sha': item.get('head_sha', item['base_main_sha']),
                'pr_number': item.get('pr_number'), 'branch': item.get('branch')}

    def test_three_independent_projects_and_no_second_reservation(self):
        state = self.claim(self.claim(self.claim(), 2), 3)
        self.assertEqual([state['packages'][i]['owner_project_id']
                          for i in q.active_packages(state)], [4, 5, 6])
        self.assertNotIn('third_batch_exception', state)
        with self.assertRaises(ValueError):
            self.claim(state)
        before = deepcopy(state)
        with self.assertRaises(ValueError):
            self.step(state, 'claim_third', package_id=q.available(
                self.registry, self.policy, state)[0], base_main_sha='a' * 40, base_ci=ci())
        self.assertEqual(state, before)

    def test_stopped_and_other_projects_cannot_impersonate_or_claim(self):
        for project, actor in [(1, 'chat-1'), (2, 'legacy-project-2'),
                               (3, 'chat-1'), (5, 'chat-1'), (4, 'root')]:
            with self.subTest(project=project, actor=actor), self.assertRaises(ValueError):
                q.transition(self.registry, self.policy, self.state, project, 'claim',
                    {'actor_id': actor, 'package_id': 'B002',
                     'base_main_sha': 'a' * 40, 'base_ci': ci()})
        inactive = deepcopy(self.state)
        inactive['execution_mode'] = 'work'
        self.assertEqual(q.next_action(self.registry, self.policy, inactive, 4, 'chat-1')['action'], 'wait')

    def test_parallel_worker_does_not_resume_or_repair_someone_elses_proof(self):
        state = self.claim()
        self.assertEqual(q.next_action(self.registry, self.policy, state, 5, 'chat-2'),
                         {'action': 'claim', 'package_id': 'B003'})
        for event, data in [
            ('checkpoint', dict(head_sha='b' * 40, pr_number=70,
                                observed_ci={**ci('b' * 40), 'conclusion': 'failure'})),
            ('submit', dict(head_sha='b' * 40, pr_number=70, ci=ci('b' * 40),
                           report_path=f'{q.DIRECTORY}/submissions/B002.md')),
            ('record_authorship', dict(author_actor_ids=['chat-2'])),
            ('block', dict(reason='cannot steal another project')),
            ('repair', dict(base_main_sha='a' * 40, base_ci=ci())),
        ]:
            with self.subTest(event=event), self.assertRaises(ValueError):
                self.step(state, event, 2, package_id='B002', **data)

    def test_cross_review_is_actual_package_independence_not_a_role_label(self):
        state = self.submit(self.claim())
        with self.assertRaises(ValueError):
            self.review(state, worker=1)
        state = self.claim()
        state = self.step(state, 'record_authorship', package_id='B002',
                          author_actor_ids=['chat-2'])
        state = self.submit(state)
        with self.assertRaises(ValueError):
            self.review(state)
        self.assertEqual(self.review(state, worker=3)['packages']['B002']['review']['project_id'], 6)
        aliased = deepcopy(self.policy)
        aliased['actors']['chat-3']['identity'] = aliased['actors']['chat-2']['identity']
        with self.assertRaises(ValueError):
            q.validate_policy(self.registry, aliased)

    def test_historical_authorship_and_changed_heads_block_reused_approval(self):
        state = self.approved()
        changed = self.submit(state, head='c' * 40)
        self.assertNotIn('review', changed['packages']['B002'])
        with self.assertRaises(ValueError):
            self.step(changed, 'start_integration', package_id='B002', head_sha='c' * 40,
                      base_main_sha='a' * 40, head_contains_main=True, ci=ci('c' * 40))
        state = self.submit(self.claim())
        state['packages']['B002']['original_author_project_ids'].append(5)
        with self.assertRaises(ValueError):
            self.review(state)

    def test_review_priority_while_own_batch_uses_its_slot(self):
        state = self.claim(self.claim(), 2)
        state = self.submit(state)
        self.assertEqual(q.next_action(self.registry, self.policy, state, 5, 'chat-2'),
                         {'action': 'review', 'package_id': 'B002'})
        state = self.review(state)
        self.assertEqual(q.next_action(self.registry, self.policy, state, 5, 'chat-2')['action'], 'resume_review')
        state = self.step(state, 'approve', 2, package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        state = self.step(state, 'start_integration', package_id='B002', head_sha='b' * 40,
                          base_main_sha='a' * 40, head_contains_main=True, ci=ci('b' * 40))
        self.assertEqual(q.next_action(self.registry, self.policy, state, 5, 'chat-2')['action'], 'resume')
        self.assertEqual(q.next_action(self.registry, self.policy, state, 4, 'chat-1')['action'], 'finish_integration')

    def test_exact_head_and_actual_main_gate_single_integration_lock(self):
        state = self.approved()
        with self.assertRaises(ValueError):
            self.step(state, 'accept', package_id='B002', integration_commit='c' * 40, main_ci=ci('c' * 40))
        state = self.step(state, 'start_integration', package_id='B002', head_sha='b' * 40,
                          base_main_sha='a' * 40, head_contains_main=True, ci=ci('b' * 40))
        for bad in [ci('d' * 40), {**ci('c' * 40), 'conclusion': 'failure'},
                    {**ci('c' * 40), 'axiom_audit': 'not_run'}]:
            with self.subTest(ci=bad), self.assertRaises(ValueError):
                self.step(state, 'accept', package_id='B002', integration_commit='c' * 40, main_ci=bad)
        self.assertIsNotNone(state['integration_lock'])
        result = self.step(state, 'accept', package_id='B002', integration_commit='c' * 40, main_ci=ci('c' * 40))
        self.assertEqual(result['packages']['B002']['owner_project_id'], 4)
        self.assertEqual(result['packages']['B002']['state'], 'ACCEPTED')
        self.assertIsNone(result['integration_lock'])

    def test_author_waiting_for_own_main_ci_can_lease_a_real_foreign_review(self):
        state = self.claim(self.claim(), 2)
        state = self.review(self.submit(state))
        state = self.step(state, 'approve', 2, package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        state = self.submit(state, ident='B003', worker=2, head='c' * 40)
        state = self.step(state, 'start_integration', package_id='B002', head_sha='b' * 40,
                          base_main_sha='a' * 40, head_contains_main=True, ci=ci('b' * 40))
        next_step = q.next_action(self.registry, self.policy, state, 4, 'chat-1')
        self.assertEqual(next_step['optional_review_while_ci_pending'], 'B003')
        result = self.review(state, ident='B003', worker=1)
        self.assertEqual(result['integration_lock'], state['integration_lock'])
        self.assertEqual(result['packages']['B003']['review']['actor_id'], 'chat-1')

    def test_foreign_integration_does_not_block_an_already_owned_repair(self):
        state = self.claim(self.claim(), 2)
        state = self.review(self.submit(state))
        state = self.step(state, 'approve', 2, package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        state = self.review(self.submit(state, ident='B003', worker=2, head='c' * 40), ident='B003', worker=3)
        state = self.step(state, 'request_changes', 3, package_id='B003', head_sha='c' * 40, summary=SUMMARY)
        state = self.step(state, 'start_integration', package_id='B002', head_sha='b' * 40,
                          base_main_sha='a' * 40, head_contains_main=True, ci=ci('b' * 40))
        self.assertEqual(q.next_action(self.registry, self.policy, state, 5, 'chat-2')['action'], 'repair')
        repaired = self.step(state, 'repair', 2, package_id='B003', base_main_sha='a' * 40, base_ci=ci())
        self.assertEqual(repaired['packages']['B003']['state'], 'IN_PROGRESS')
        self.assertEqual(repaired['integration_lock'], state['integration_lock'])

    def test_repair_and_blockers_do_not_release_a_chat_slot(self):
        state = self.step(self.review(self.submit(self.claim())), 'request_changes', 2,
                          package_id='B002', head_sha='b' * 40, summary=SUMMARY)
        self.assertEqual(q.next_action(self.registry, self.policy, state, 4, 'chat-1')['action'], 'repair')
        with self.assertRaises(ValueError):
            self.claim(state, 3)
        state = self.step(state, 'repair', package_id='B002', base_main_sha='a' * 40, base_ci=ci())
        state = self.step(state, 'block', package_id='B002', reason='actual mathematical issue')
        with self.assertRaises(ValueError):
            self.claim(state)
        self.assertEqual(q.next_action(self.registry, self.policy, state, 4, 'chat-1')['action'], 'blocked')

    def test_clean_roundtrip_preserves_every_accepted_record_and_history(self):
        original = deepcopy(self.state)
        work = self.step(original, 'switch_mode', **self.mode_data(target_mode='work'))
        chat = q.transition(self.registry, self.policy, work, 3, 'switch_mode',
            {'actor_id': 'root', **self.mode_data(target_mode='chat')})
        self.assertEqual(chat['packages'], original['packages'])
        self.assertEqual(chat['history'][:len(original['history'])], original['history'])
        self.assertEqual(chat['revision'], original['revision'] + 2)
        self.assertEqual(chat['execution_mode'], 'chat')
        self.assertEqual(chat['policy_revision'], original['policy_revision'])

    def test_pause_stops_new_claims_but_preserves_in_progress_checkpoint(self):
        state = self.pause(self.claim())
        with self.assertRaises(ValueError):
            self.claim(state, 2)
        result = self.step(state, 'checkpoint', package_id='B002', head_sha='b' * 40,
                           pr_number=70, observed_ci={**ci('b' * 40), 'conclusion': 'failure'})
        self.assertEqual(result['packages']['B002']['observed_ci']['conclusion'], 'failure')

    def test_failed_wip_handover_preserves_history_authorship_and_latest_work(self):
        state = self.step(self.claim(), 'checkpoint', package_id='B002', head_sha='b' * 40,
                          pr_number=70, observed_ci={**ci('b' * 40), 'conclusion': 'failure'})
        state['packages']['B002']['last_green_checkpoint'] = {'head_sha': 'a' * 40, 'ci': ci()}
        state = self.pause(state)
        old = deepcopy(state['packages']['B002'])
        result = self.step(state, 'handover_mode', **self.mode_data(target_mode='work',
            previous_workers_stopped=True, transfers=[self.transfer(state, 'B002')]))
        item = result['packages']['B002']
        for key in ['claim_revision', 'base_main_sha', 'base_ci', 'branch', 'head_sha',
                    'pr_number', 'observed_ci', 'last_green_checkpoint', 'original_author_project_ids']:
            self.assertEqual(item[key], old[key], key)
        self.assertEqual(item['handover_history'][-1]['previous_record'], old)
        self.assertEqual(set(item['author_actor_ids']), {'chat-1', 'root'})
        self.assertEqual(item['owner_project_id'], 3)
        self.assertEqual(result['packages']['B001'], state['packages']['B001'])
        self.assertEqual(result['history'][:-1], state['history'])

    def test_handover_clears_review_without_reusing_author_as_reviewer(self):
        state = self.pause(self.approved())
        result = self.step(state, 'handover_mode', **self.mode_data(target_mode='work',
            previous_workers_stopped=True, transfers=[self.transfer(state, 'B002')]))
        item = result['packages']['B002']
        self.assertNotIn('review', item)
        self.assertTrue(item['handover_history'][-1]['previous_record']['review']['approved'])
        # The old review was retained as history, never silently reused.
        self.assertEqual(item['state'], 'IN_PROGRESS')

    def test_handover_rejects_running_workers_missing_claims_and_stale_heads(self):
        state = self.pause(self.claim(self.claim(), 2))
        entries = [self.transfer(state, i) for i in q.active_packages(state)]
        variants = [dict(previous_workers_stopped=False, transfers=entries),
                    dict(previous_workers_stopped=True, transfers=entries[:1]),
                    dict(previous_workers_stopped=True, transfers=[{**e, 'head_sha': 'c' * 40} for e in entries]),
                    dict(previous_workers_stopped=True, transfers=[{**e, 'pr_number': 999} for e in entries])]
        for variant in variants:
            with self.subTest(variant=variant), self.assertRaises(ValueError):
                self.step(state, 'handover_mode', **self.mode_data(target_mode='work', **variant))
        with self.assertRaises(ValueError):
            self.step(state, 'switch_mode', **self.mode_data(target_mode='work'))
        with self.assertRaises(ValueError):
            self.step(state, 'handover_mode', **{**self.mode_data(target_mode='work',
                previous_workers_stopped=True, transfers=entries), 'user_authorized': False})

    def test_three_work_handover_needs_the_same_real_independent_third_plan(self):
        state = self.pause(self.claim(self.claim(self.claim(), 2), 3))
        entries = [self.transfer(state, i) for i in q.active_packages(state)]
        data = self.mode_data(target_mode='work', previous_workers_stopped=True, transfers=entries)
        with self.assertRaises(ValueError):
            self.step(state, 'handover_mode', **data)
        plan = {'package_id': 'B006', 'independent_active_work': True, 'summary': SUMMARY,
                'active_work_items': ['CCO/B006'], 'implementation_actor_id': '/root/new_b006',
                'independence_report_path': f'{q.DIRECTORY}/reports/third-B006.md',
                'existing_batches': [{'package_id': i, 'head_sha': 'a' * 40,
                    'work_items': [f'CCO/{i}'], 'implementation_actor_ids': [f'/root/{i}']}
                    for i in ['B002', 'B003']]}
        result = self.step(state, 'handover_mode', **data, third_batch_exception=plan)
        self.assertEqual(result['execution_mode'], 'work')
        self.assertEqual(len(q.active_packages(result)), 3)
        plan['active_work_items'] = ['CCO/B002']
        with self.assertRaises(ValueError):
            self.step(state, 'handover_mode', **data, third_batch_exception=plan)


class ProfileDeploymentTests(unittest.TestCase):
    def setUp(self):
        from test_coordination_queue import QueueTests
        fixture = QueueTests()
        fixture.setUp()
        self.registry, self.policy = deepcopy((fixture.registry, fixture.policy))
        self.old = deepcopy(self.policy)
        for a in self.old.pop('chat_project_actors').values():
            self.old['actors'].pop(a)
        self.old.pop('execution_profiles')
        self.old['registered_projects'] = [1, 2, 3]
        self.old['revision'] -= 1
        self.state = deepcopy(fixture.state)
        self.state['policy_revision'] = self.old['revision']
        self.manifest = q.execution_profile_manifest(self.registry, self.old, self.registry, self.policy)
        self.locked = q.transition(self.registry, self.old, self.state, 3, 'start_infrastructure', {
            'actor_id': 'root', 'head_sha': 'b' * 40, 'pr_number': 71,
            'base_main_sha': 'a' * 40, 'head_contains_main': True, 'ci': ci('b' * 40),
            'author_actor_ids': ['root'], 'original_author_project_ids': [3],
            'profile_deployment': self.manifest,
            'review': {'actor_id': 'independent_review', 'head_sha': 'b' * 40,
                       'approved': True, 'summary': SUMMARY, 'independence': independence()}})

    def promote(self, **extra):
        return q.promote_profiles(self.registry, self.old, self.registry, self.policy,
            self.locked, 3, {'actor_id': 'root', 'head_sha': 'b' * 40,
                            'integration_commit': 'c' * 40, 'main_ci': ci('c' * 40),
                            'target_mode': 'chat', **extra})

    def test_profile_promotion_preserves_all_packages_and_old_history(self):
        result = self.promote()
        self.assertEqual(result['packages'], self.state['packages'])
        self.assertEqual(result['history'][:-1], self.locked['history'])
        self.assertIsNone(result['integration_lock'])
        self.assertEqual(result['execution_mode'], 'chat')
        self.assertEqual(result['policy_revision'], self.policy['revision'])
        with self.assertRaises(ValueError):
            q.validate_state(self.registry, self.policy, self.locked)

    def test_cannot_finish_without_exact_snapshots_head_and_main_audit(self):
        for change in [dict(head_sha='d' * 40), dict(main_ci=ci('e' * 40)),
                       dict(main_ci={**ci('c' * 40), 'conclusion': 'failure'})]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.promote(**change)
        with self.assertRaises(ValueError):
            q.transition(self.registry, self.old, self.locked, 3, 'finish_infrastructure',
                {'actor_id': 'root', 'integration_commit': 'c' * 40, 'main_ci': ci('c' * 40)})
        tampered = deepcopy(self.policy)
        tampered['actors']['root']['roles'].append('review')
        with self.assertRaises(ValueError):
            q.execution_profile_manifest(self.registry, self.old, self.registry, tampered)

    def test_profile_manifest_rejects_changed_source_catalogue_roles_limits_and_aliases(self):
        changes = [lambda b, p: b.update(source_commit='f' * 40),
                   lambda b, p: b['packages'][0].update(scope='different mathematics'),
                   lambda b, p: p['released_packages'].append('B999'),
                   lambda b, p: p.update(default_active_batches=3),
                   lambda b, p: p['execution_profiles']['chat'].update(per_project_limit=2),
                   lambda b, p: p['actors']['chat-1'].update(identity='/root'),
                   lambda b, p: p['actors']['independent_review'].update(identity='renamed'),
                   lambda b, p: p['actors']['chat-1'].update(historical_author_projects=[])]
        for change in changes:
            board, policy = deepcopy((self.registry, self.policy))
            change(board, policy)
            with self.subTest(change=change), self.assertRaises(ValueError):
                q.execution_profile_manifest(self.registry, self.old, board, policy)

    def test_adding_fourth_worker_preserves_live_claims_without_draining_the_pool(self):
        from configure_execution_profiles import add_worker
        state = self.promote()
        state = q.transition(self.registry, self.policy, state, 4, 'claim',
            {'actor_id': 'chat-1', 'package_id': 'B002', 'base_main_sha': 'a' * 40, 'base_ci': ci()})
        new, manifest = add_worker(self.registry, self.policy, 4)
        locked = q.transition(self.registry, self.policy, state, 4, 'start_infrastructure', {
            'actor_id': 'chat-1', 'head_sha': 'd' * 40, 'pr_number': 72,
            'base_main_sha': 'c' * 40, 'head_contains_main': True, 'ci': ci('d' * 40),
            'author_actor_ids': ['chat-1'], 'original_author_project_ids': [4],
            'profile_deployment': manifest, 'review': {'actor_id': 'chat-2', 'head_sha': 'd' * 40,
                'approved': True, 'summary': SUMMARY,
                'independence': {**independence(), 'identity': self.policy['actors']['chat-2']['identity']}}})
        result = q.promote_profiles(self.registry, self.policy, self.registry, new, locked, 4,
            {'actor_id': 'chat-1', 'head_sha': 'd' * 40, 'integration_commit': 'e' * 40,
             'main_ci': ci('e' * 40)})
        self.assertEqual(result['packages'], state['packages'])
        self.assertEqual(new['chat_project_actors']['7'], 'chat-4')
        self.assertEqual(new['execution_profiles']['chat']['maximum_active_batches'], 4)
        self.assertEqual(new['actors']['root'], self.policy['actors']['root'])
        with self.assertRaises(ValueError):
            add_worker(self.registry, self.policy, 1)
        with self.assertRaises(ValueError):
            q.promote_profiles(self.registry, self.policy, self.registry, new, locked, 4,
                {'actor_id': 'chat-1', 'head_sha': 'd' * 40, 'integration_commit': 'e' * 40,
                 'main_ci': ci('e' * 40), 'target_mode': 'work'})


if __name__ == '__main__':
    unittest.main()
