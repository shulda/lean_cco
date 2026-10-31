import hashlib
import io
import json
import unittest
from copy import deepcopy
from unittest.mock import patch
import urllib.error

import coordination_broker as b
import coordination_queue as q
from test_coordination_queue import ci


class FakeGitHub:
    def __init__(self):
        from test_coordination_queue import QueueTests
        f = QueueTests()
        f.setUp()
        self.registry, self.policy, self.state = deepcopy((f.registry, f.policy, f.state))
        self.state.update(execution_mode='chat', claims_paused=False)
        self.coord, self.main = 'c' * 40, 'a' * 40
        self.inbox, self.receipts, self.published, self.reports = {}, {}, [], {}
        self.eppa = json.loads((q.ROOT / 'tools/external_provider.json').read_text())
        self.ramsey = json.loads((q.ROOT / 'tools/ramsey_provider.json').read_text())
        self.run = {'id': 1, 'head_sha': self.main, 'status': 'completed', 'conclusion': 'success',
                    'path': '.github/workflows/lean.yml', 'run_attempt': 1}
        self.log = ("axiom-audit: audited 7 declaration(s) under 'CCO'; all within the allowlist "
                    '[propext, Classical.choice, Quot.sound]\n')
        self.log += 'Project cache consistent: 2 olean part(s), 2 current source module(s) checked\n' * 2
        self.log += (f'External provider cache consistent: {self.eppa["source_modules"]} olean part(s), '
                     f'{self.eppa["source_modules"]} current source module(s) checked; exact pin '
                     f'{self.eppa["commit"]}\n') * 3
        self.log += (f'Ramsey provider cache consistent: {self.ramsey["source_modules"]} olean part(s), '
                     f'{self.ramsey["source_modules"]} current source module(s) checked; exact subtree '
                     f'{self.ramsey["subtree"]}\n') * 3
        self.race = False
        self.pr = {'head': {'sha': 'b' * 40, 'ref': 'chat/chat-1/B002'},
                   'merged': False, 'merge_commit_sha': None}

    def request(self, actor='chat-1', ident='first', operation='claim_next', **extra):
        value = {'schema_version': 1, 'actor_id': actor, 'project_id': int(actor.split('-')[-1]) + 3,
                 'request_id': ident, 'operation': operation, 'policy_revision': self.policy['revision'], **extra}
        path = b.REQUESTS + actor + '/' + ident + '.json'
        self.inbox[path] = json.dumps(value)
        return path, value

    def ref(self, branch):
        return self.coord if branch == 'coordination' else self.main if branch == 'main' else 'f' * 40

    def files(self, ref):
        if ref == 'f' * 40:
            return {p: hashlib.sha1(v.encode()).hexdigest() for p, v in self.inbox.items()}
        if ref == self.coord:
            return {p: 'e' * 40 for p in self.receipts}
        return {'CCO.lean': '1' * 40, 'CCO/A.lean': '2' * 40}

    def commit(self, sha):
        return {'tree': {'sha': 'd' * 40}, 'parents': []}

    def file(self, path, ref, optional=False):
        if path in self.inbox:
            return self.inbox[path]
        if path in self.receipts:
            return json.dumps(self.receipts[path])
        if path in self.reports:
            return self.reports[path]
        names = {str(q.DIRECTORY / 'STATE.json'): self.state,
                 str(q.DIRECTORY / 'BOARD.json'): self.registry,
                 str(q.DIRECTORY / 'AUTONOMY.json'): self.policy,
                 'tools/external_provider.json': self.eppa, 'tools/ramsey_provider.json': self.ramsey}
        if path in names:
            return json.dumps(names[path])
        if optional:
            return None
        raise ValueError('Missing fixture file ' + path)

    def call(self, path, *args):
        if path == '/actions/runs/1':
            return self.run
        if path.startswith('/actions/runs?'):
            return {'workflow_runs': [self.run]}
        if path.startswith('/actions/runs/1/jobs'):
            return {'jobs': [{'id': 10, 'conclusion': 'success'}]}
        if path.startswith('/pulls/'):
            return self.pr
        if path.startswith('/compare/'):
            return {'status': 'ahead', 'merge_base_commit': {'sha': path.split('/')[2].split('...')[0]}}
        raise AssertionError(path)

    def logs(self, job):
        assert job == 10
        return self.log

    def publish(self, parent, tree, updates, message):
        if self.race:
            self.race = False
            self.state = q.transition(self.registry, self.policy, self.state, 5, 'claim',
                {'actor_id': 'chat-2', 'package_id': 'B002', 'base_main_sha': self.main, 'base_ci': ci()})
            self.coord = '9' * 40
            raise b.Collision('Another effective claimant won')
        if parent != self.coord:
            raise b.Collision('Stale parent')
        self.published.append((parent, deepcopy(updates)))
        for path, value in updates.items():
            if path == str(q.DIRECTORY / 'STATE.json'):
                self.state = deepcopy(value)
            elif path.startswith(b.RESULTS):
                self.receipts[path] = deepcopy(value)
            else:
                assert path == b.STATUS
        self.coord = f'{len(self.published):040x}'
        return self.coord


class BrokerTests(unittest.TestCase):
    def setUp(self):
        self.api = FakeGitHub()

    def process(self):
        with patch('builtins.print'):
            return b.process(self.api)

    def test_one_run_drains_every_pending_request_despite_replaced_pending_workflows(self):
        for worker in range(1, 4):
            self.api.request(f'chat-{worker}')
        self.assertEqual(self.process(), 3)
        self.assertEqual(len(q.active_packages(self.api.state)), 3)
        self.assertEqual({self.api.state['packages'][i]['owner_project_id']
                          for i in q.active_packages(self.api.state)}, {4, 5, 6})
        self.assertTrue(all(x['status'] == 'applied' for x in self.api.receipts.values()))

    def test_redelivery_and_even_wrongly_edited_old_request_never_replay_a_claim(self):
        path, request = self.api.request()
        self.process()
        before = deepcopy((self.api.state, self.api.receipts, self.api.published))
        self.assertEqual(self.process(), 0)
        self.api.inbox[path] = json.dumps({**request, 'operation': 'event', 'event': 'block'})
        self.assertEqual(self.process(), 0)
        self.assertEqual((self.api.state, self.api.receipts, self.api.published), before)

    def test_cas_loser_recomputes_the_claim_not_just_its_parent(self):
        self.api.request()
        self.api.race = True
        self.process()
        self.assertEqual(self.api.state['packages']['B002']['owner_project_id'], 5)
        self.assertEqual(self.api.state['packages']['B003']['owner_project_id'], 4)
        self.assertEqual(self.api.published[0][0], '9' * 40)

    def test_bad_request_cannot_poison_the_following_worker_or_replace_actor(self):
        bad, _ = self.api.request(ident='a_bad')
        self.api.inbox[bad] = '{broken JSON'
        self.api.request(ident='b_spoof', data={'actor_id': 'chat-2'})
        self.api.request(ident='c_good')
        self.api.inbox[b.REQUESTS + 'wrong/nested/path.json'] = '{}'
        self.process()
        self.assertEqual([v['status'] for v in self.api.receipts.values()], ['rejected', 'rejected', 'applied'])
        self.assertEqual(len(q.active_packages(self.api.state)), 1)

    def test_status_and_no_ready_package_write_no_state_event_or_speculative_claim(self):
        self.api.request(operation='status', data={'verify_ci': True})
        original = deepcopy(self.api.state)
        self.process()
        self.assertEqual(self.api.state, original)
        self.assertNotIn(str(q.DIRECTORY / 'STATE.json'), self.api.published[0][1])
        self.assertTrue(self.api.published[0][1][b.STATUS]['not_an_ownership_lease'])
        self.assertEqual(next(iter(self.api.receipts.values()))['verified_main_ci']['declarations'], 7)

    def test_specific_stale_events_are_rejected_without_mutating_claims(self):
        self.api.request(operation='event', event='block', expected_revision=0,
                         data={'package_id': 'B002', 'reason': 'stale'})
        original = deepcopy(self.api.state)
        self.process()
        self.assertEqual(self.api.state, original)
        self.assertIn('exact observed', next(iter(self.api.receipts.values()))['reason'])

    def test_policy_mismatch_or_inactive_profile_does_not_authorize_work(self):
        self.api.request(policy_revision=999)
        self.api.request('chat-2', ident='inactive')
        self.api.state['execution_mode'] = 'work'
        self.process()
        self.assertFalse(q.active_packages(self.api.state))
        self.assertEqual([v['status'] for v in self.api.receipts.values()], ['rejected', 'no_change'])

    def test_exact_ci_rejects_wrong_head_missing_audit_incomplete_closure_and_wrong_pin(self):
        mutations = [lambda a: a.run.update(head_sha='b' * 40),
                     lambda a: a.run.update(conclusion='failure'),
                     lambda a: a.run.update(path='.github/workflows/unrelated.yml'),
                     lambda a: setattr(a, 'log', a.log.replace('Quot.sound', 'sorryAx')),
                     lambda a: setattr(a, 'log', a.log.replace('2 olean part(s)', '1 olean part(s)')),
                     lambda a: setattr(a, 'log', a.log.replace(a.eppa['commit'], 'f' * 40)),
                     lambda a: setattr(a, 'log', a.log.replace(a.ramsey['subtree'], 'f' * 40))]
        for mutate in mutations:
            api = FakeGitHub()
            mutate(api)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                b.verified_ci(api, 1, api.main)
        # An early partial-cache observation is fine; both final closure guards must be complete.
        api = FakeGitHub()
        api.log = 'Project cache consistent: 1 olean part(s), 2 current source module(s) checked\n' + api.log
        self.assertEqual(b.verified_ci(api, 1, api.main)['source_modules'], 2)

    def test_no_new_claim_while_another_main_integration_has_not_passed(self):
        self.api.request()
        self.api.run['conclusion'] = None
        self.process()
        self.assertFalse(q.active_packages(self.api.state))
        self.assertEqual(next(iter(self.api.receipts.values()))['status'], 'rejected')

    def test_accepted_dependency_must_really_be_contained_in_current_main(self):
        self.api.request()
        original = self.api.call
        def call(path, *args):
            if path.startswith('/compare/'):
                return {'status': 'diverged', 'merge_base_commit': {'sha': 'f' * 40}}
            return original(path, *args)
        self.api.call = call
        self.process()
        self.assertFalse(q.active_packages(self.api.state))
        self.assertEqual(next(iter(self.api.receipts.values()))['status'], 'rejected')

    def test_transport_uses_one_exact_parent_nonforce_and_full_readback(self):
        api = b.GitHub('example/repo', 'test-token')
        parent, commit = 'a' * 40, 'b' * 40
        calls = []
        def call(path, method='GET', body=None):
            calls.append((path, method, body))
            return {'sha': 'd' * 40} if path == '/git/trees' else {'sha': commit}
        files = {str(q.DIRECTORY / 'STATE.json'): {'revision': 2}}
        with patch.object(api, 'call', side_effect=call), \
             patch.object(api, 'ref', side_effect=[parent, commit]), \
             patch.object(api, 'file', return_value=json.dumps({'revision': 2})):
            self.assertEqual(api.publish(parent, 'c' * 40, files, 'test'), commit)
        self.assertEqual(calls[1][2]['parents'], [parent])
        self.assertEqual(calls[2], ('/git/refs/heads/coordination', 'PATCH', {'sha': commit, 'force': False}))
        with self.assertRaises(ValueError):
            api.publish(parent, 'c' * 40, {'formalization/coordination/BOARD.json': {}}, 'forbidden')
        with patch.object(api, 'call', side_effect=call), \
             patch.object(api, 'ref', side_effect=[parent, commit]), \
             patch.object(api, 'file', return_value=json.dumps({'revision': 999})), self.assertRaises(ValueError):
            api.publish(parent, 'c' * 40, files, 'detect incorrect readback')

    def test_locked_policy_deployment_uses_old_snapshots_without_relaxing_validation(self):
        from test_execution_profiles import ProfileDeploymentTests
        fixture = ProfileDeploymentTests()
        fixture.setUp()
        self.api.state = fixture.locked
        self.api.main = 'e' * 40
        original = self.api.file
        def file(path, ref, optional=False):
            if path == str(q.DIRECTORY / 'AUTONOMY.json') and ref == 'a' * 40:
                return json.dumps(fixture.old)
            return original(path, ref, optional)
        self.api.file = file
        actual = b.snapshot(self.api)
        self.assertEqual(actual['policy'], fixture.old)
        self.assertEqual(actual['current_policy'], fixture.policy)
        self.api.state['integration_lock'] = None
        with self.assertRaises(ValueError):
            b.snapshot(self.api)

    def test_actual_merged_pr_prevents_premerge_cancellation(self):
        self.api.pr['merged'] = True
        snap = b.snapshot(self.api)
        snap['state']['integration_lock'] = {'pr_number': 70, 'head_sha': 'b' * 40}
        with self.assertRaises(ValueError):
            b.verify_evidence(self.api, snap, 'cancel_infrastructure', {'pr_not_merged': True})

    def test_readers_need_the_actual_durable_report_identity_and_full_sha(self):
        snap = b.snapshot(self.api)
        snap['state']['packages']['B002'].update(pr_number=70, head_sha='b' * 40,
            branch='chat/chat-1/B002')
        data = {'package_id': 'B002', 'head_sha': 'b' * 40,
                'independence': {'identity': 'actual-reader', 'report_path': 'review.md'}}
        with self.assertRaises(ValueError):
            b.verify_evidence(self.api, snap, 'review', data)
        self.api.reports['review.md'] = 'actual-reader reviewed ' + 'b' * 40
        b.verify_evidence(self.api, snap, 'review', data)
        self.api.pr['head']['sha'] = 'e' * 40
        with self.assertRaises(ValueError):
            b.verify_evidence(self.api, snap, 'review', data)

    def test_log_redirect_does_not_forward_the_github_token(self):
        headers = {'Location': 'https://example.blob.core.windows.net/signed-log'}
        error = urllib.error.HTTPError('https://api.github.com/log', 302, 'redirect', headers, None)
        opened = []
        class Opener:
            def open(self, request, timeout):
                self.token = request.get_header('Authorization')
                self.assertion = bool(self.token)
                raise error
        def download(request, timeout):
            opened.append(request)
            return io.BytesIO(b'actual log')
        with patch('urllib.request.build_opener', return_value=Opener()), \
             patch('urllib.request.urlopen', side_effect=download):
            self.assertEqual(b.GitHub('example/repo', 'private-test-token').logs(10), 'actual log')
        self.assertIsNone(opened[0].get_header('Authorization'))


if __name__ == '__main__':
    unittest.main()
