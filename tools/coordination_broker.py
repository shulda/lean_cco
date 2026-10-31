#!/usr/bin/env python3
"""Process append-only Chat requests using trusted main code and non-force CAS.

This is coordination, never a mathematical reviewer or a Lean replacement.
Requests are data, not code. Only main's validator is executed. Existing
requests are immutable; receipt existence makes redelivery idempotent.
"""
from __future__ import annotations

import argparse
import base64
from copy import deepcopy
import json
import os
import re
import urllib.error
import urllib.parse
import urllib.request

import coordination_queue as q
import coordination_profiles as profiles

INBOX = 'coordination-requests'
REQUESTS = 'coordination/requests/'
RESULTS = str(q.DIRECTORY / 'requests/results') + '/'
STATUS = str(q.DIRECTORY / 'STATUS.json')
SLUG = re.compile(r'[A-Za-z0-9][A-Za-z0-9_-]{0,95}')
ADMIN = {'promote_registry': q.promote_registry, 'promote_reviewer': q.promote_reviewer,
         'promote_profiles': q.promote_profiles}


class Collision(RuntimeError):
    pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        return None


class GitHub:
    def __init__(self, repository, token):
        q.require(bool(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)),
                  'Invalid repository')
        self.base = f'https://api.github.com/repos/{repository}'
        self.token = token

    def call(self, path, method='GET', body=None):
        request = urllib.request.Request(self.base + path, method=method,
            data=None if body is None else json.dumps(body).encode(),
            headers={'Authorization': f'Bearer {self.token}', 'User-Agent': 'cco-coordination',
                     'Accept': 'application/vnd.github+json', 'Content-Type': 'application/json',
                     'X-GitHub-Api-Version': '2022-11-28'})
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                return json.load(response)
        except urllib.error.HTTPError as error:
            if error.code == 404:
                return None
            raise RuntimeError(f'GitHub API {method} {path}: HTTP {error.code}') from None

    def ref(self, branch):
        value = self.call('/git/ref/heads/' + urllib.parse.quote(branch, safe='/'))
        q.require(value is not None, f'Missing branch {branch}')
        return value['object']['sha']

    def commit(self, sha):
        return self.call('/git/commits/' + sha)

    def files(self, ref):
        tree = self.call('/git/trees/' + ref + '?recursive=1')
        q.require(tree and tree.get('truncated') is False, 'Incomplete Git tree; do not guess ownership')
        return {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}

    def file(self, path, ref, optional=False):
        value = self.call('/contents/' + urllib.parse.quote(path, safe='/') +
                          '?ref=' + urllib.parse.quote(ref, safe=''))
        if value is None and optional:
            return None
        q.require(value is not None, 'Missing durable file: ' + path)
        if value.get('encoding') != 'base64':
            value = self.call('/git/blobs/' + value['sha'])
        return base64.b64decode(value['content']).decode()

    def logs(self, job):
        # Strip credentials on the signed download redirect. urllib otherwise
        # carries Authorization to a different host on a default redirect.
        request = urllib.request.Request(self.base + f'/actions/jobs/{job}/logs',
            headers={'Authorization': f'Bearer {self.token}', 'User-Agent': 'cco-coordination'})
        try:
            response = urllib.request.build_opener(NoRedirect()).open(request, timeout=30)
        except urllib.error.HTTPError as error:
            q.require(error.code in {301, 302, 303, 307, 308}, 'Actual CI log is not available yet')
            url = error.headers['Location']
            q.require(urllib.parse.urlsplit(url).scheme == 'https', 'CI logs require HTTPS')
            response = urllib.request.urlopen(urllib.request.Request(url,
                headers={'User-Agent': 'cco-coordination'}), timeout=30)
        with response:
            return response.read().decode()

    def publish(self, parent, tree, files, message):
        q.require(all(p == str(q.DIRECTORY / 'STATE.json') or p == STATUS or p.startswith(RESULTS)
                      for p in files), 'Broker cannot edit source, policy or BOARD')
        new_tree = self.call('/git/trees', 'POST', {'base_tree': tree, 'tree': [
            {'path': p, 'mode': '100644', 'type': 'blob', 'content': json.dumps(v, indent=2) + '\n'}
            for p, v in files.items()]})
        commit = self.call('/git/commits', 'POST', {'message': message,
            'tree': new_tree['sha'], 'parents': [parent]})
        if self.ref('coordination') != parent:
            raise Collision('Coordination moved: reload and recompute, never reparent a proposal')
        try:
            self.call('/git/refs/heads/coordination', 'PATCH',
                      {'sha': commit['sha'], 'force': False})
        except RuntimeError:
            if self.ref('coordination') != parent:
                raise Collision('Non-fast-forward CAS lost') from None
            raise
        observed = self.ref('coordination')
        if observed != commit['sha']:
            ancestry(self, commit['sha'], observed)
        for path, value in files.items():
            q.require(json.loads(self.file(path, commit['sha'])) == value,
                      'Read back the full exact published STATE/receipt/index')
        return commit['sha']


def snapshot(api):
    coord, main = api.ref('coordination'), api.ref('main')
    state = json.loads(api.file(str(q.DIRECTORY / 'STATE.json'), coord))
    current_registry = json.loads(api.file(str(q.DIRECTORY / 'BOARD.json'), main))
    current_policy = json.loads(api.file(str(q.DIRECTORY / 'AUTONOMY.json'), main))
    registry, policy = current_registry, current_policy
    if state['policy_revision'] != policy['revision']:
        lock = state.get('integration_lock') or {}
        q.require(lock.get('kind') == 'infrastructure' and q.sha(lock.get('base_main_sha')),
                  'Policy/STATE mismatch without a reviewed deployment lock')
        base = lock['base_main_sha']
        registry = json.loads(api.file(str(q.DIRECTORY / 'BOARD.json'), base))
        policy = json.loads(api.file(str(q.DIRECTORY / 'AUTONOMY.json'), base))
    q.validate_state(registry, policy, state)
    return {'coord': coord, 'tree': api.commit(coord)['tree']['sha'], 'main': main,
            'state': state, 'registry': registry, 'policy': policy,
            'current_registry': current_registry, 'current_policy': current_policy}


def verified_ci(api, run_id, head):
    q.require(type(run_id) is int and run_id > 0 and q.sha(head), 'CI needs an actual run and exact head')
    run = api.call(f'/actions/runs/{run_id}')
    q.require(run and run['head_sha'] == head and run['status'] == 'completed'
              and run['conclusion'] == 'success' and run['path'] == '.github/workflows/lean.yml',
              'Actual exact-head Lean CI is not successful')
    jobs = api.call(f'/actions/runs/{run_id}/jobs?filter=latest&per_page=100')['jobs']
    q.require(len(jobs) == 1 and jobs[0]['conclusion'] == 'success', 'Actual CI build job must be green')
    logs = api.logs(jobs[0]['id'])
    audits = re.findall(r"axiom-audit: audited (\d+) declaration\(s\) under 'CCO'; all within the allowlist "
                        r'\[propext, Classical.choice, Quot.sound\]', logs)
    guards = re.findall(r'Project cache consistent: (\d+) olean part\(s\), (\d+) current source module\(s\) checked', logs)
    sources = sum(name == 'CCO.lean' or (name.startswith('CCO/') and name.endswith('.lean'))
                  for name in api.files(head))
    q.require(len(audits) == 1 and int(audits[0]) > 0 and len(guards) >= 2
              and all(int(b) == sources for a, b in guards)
              and all(int(a) == sources for a, b in guards[-2:]),
              'Actual complete source closure and allowlist audit are required')
    for filename, pattern, pin_key in [
        ('external_provider.json', r'External provider cache consistent: (\d+) olean part\(s\), '
         r'(\d+) current source module\(s\) checked; exact pin ([0-9a-f]{40})', 'commit'),
        ('ramsey_provider.json', r'Ramsey provider cache consistent: (\d+) olean part\(s\), '
         r'(\d+) current source module\(s\) checked; exact subtree ([0-9a-f]{40})', 'subtree')]:
        spec = json.loads(api.file('tools/' + filename, head))
        found = re.findall(pattern, logs)
        q.require(len(found) >= 3 and all(int(a) == spec['source_modules']
            and int(b) == spec['source_modules'] and pin == spec[pin_key] for a, b, pin in found[-3:]),
            'Actual pinned external-provider guards are required')
    return {'run_id': run_id, 'run_attempt': run.get('run_attempt', 1), 'head_sha': head,
            'conclusion': 'success', 'axiom_audit': 'allowlist', 'job_id': jobs[0]['id'],
            'declarations': int(audits[0]), 'source_modules': sources}


def main_ci(api, head):
    runs = api.call('/actions/runs?branch=main&per_page=100')['workflow_runs']
    valid = [r for r in runs if r['head_sha'] == head and r['conclusion'] == 'success'
             and r['path'] == '.github/workflows/lean.yml']
    q.require(valid, 'Wait for successful actual-main CI; no claim on a green sibling')
    return verified_ci(api, valid[0]['id'], head)


def actual_pr(api, number, head, branch=None):
    q.require(type(number) is int and number > 0, 'Missing actual PR')
    pr = api.call(f'/pulls/{number}')
    q.require(pr and pr['head']['sha'] == head and
              (branch is None or pr['head']['ref'] == branch), 'Actual PR head/branch moved')
    return pr


def ancestry(api, base, head):
    compared = api.call(f'/compare/{base}...{head}?per_page=1&page=2')
    q.require(compared and compared['status'] in {'ahead', 'identical'}
              and compared['merge_base_commit']['sha'] == base,
              'Actual current main must be an ancestor of the approved head')


def verify_evidence(api, snap, event, data):
    state = snap['state']
    item = state['packages'].get(data.get('package_id'), {})
    if event == 'repair' and state.get('integration_lock'):
        base = item.get('base_main_sha')
        q.require(data.get('base_main_sha', base) == base, 'Repair during another integration retains its green base')
        data['base_main_sha'] = base
        data['base_ci'] = verified_ci(api, item.get('base_ci', {}).get('run_id'), base)
        ancestry(api, base, snap['main'])
    elif event in {'claim', 'claim_third', 'repair', 'resume_claims', 'switch_mode', 'handover_mode'}:
        q.require(data.get('base_main_sha', snap['main']) == snap['main'], 'Current main changed')
        data['base_main_sha'] = snap['main']
        data['base_ci'] = main_ci(api, snap['main'])
    if event in {'claim', 'claim_third', 'repair'}:
        packages = {p['id']: p for p in snap['registry']['packages']}
        checked = set()
        def check(ident):
            for dependency in packages[ident]['depends_on']:
                if dependency in checked:
                    continue
                checked.add(dependency)
                record = state['packages'][dependency]
                q.require(record['state'] == 'ACCEPTED', 'Every transitive dependency must be ACCEPTED')
                ancestry(api, record['accepted_commit'], data['base_main_sha'])
                check(dependency)
        check(data.get('package_id'))
    if event in {'submit', 'refresh_review', 'start_integration', 'start_infrastructure'}:
        head = data.get('head_sha')
        evidence = data.get('ci', {})
        data['ci'] = verified_ci(api, evidence.get('run_id'), head)
        actual_pr(api, data.get('pr_number', item.get('pr_number')), head, item.get('branch'))
    if event in {'start_integration', 'start_infrastructure'}:
        q.require(data.get('base_main_sha') == snap['main'], 'Actual main moved before locking')
        ancestry(api, snap['main'], data['head_sha'])
        data['head_contains_main'] = True
    if event == 'start_infrastructure':
        actual_registry = json.loads(api.file(str(q.DIRECTORY / 'BOARD.json'), data['head_sha']))
        actual_policy = json.loads(api.file(str(q.DIRECTORY / 'AUTONOMY.json'), data['head_sha']))
        for key, builder in [('profile_deployment', q.execution_profile_manifest),
                             ('registry_promotion', q.registry_promotion_manifest)]:
            if key in data:
                q.require(data[key] == builder(snap['registry'], snap['policy'],
                                               actual_registry, actual_policy),
                          'Deployment manifest must match actual reviewed PR files')
        if 'reviewer_recovery' in data:
            m = data['reviewer_recovery']
            q.require(m == q.reviewer_recovery_manifest(snap['registry'], snap['policy'],
                actual_registry, actual_policy, m['unavailable_actor_id'], m['bootstrap_actor_id']),
                'Recovery manifest must match actual reviewed PR files')
        review = data.get('review', {})
        evidence = review.get('independence', {})
        report = api.file(evidence.get('report_path', ''), snap['coord'], optional=True)
        q.require(report and data['head_sha'] in report and evidence.get('identity', '') in report,
                  'Publish the actual non-author infrastructure review first')
    if event in {'review', 'approve', 'request_changes'}:
        actual_pr(api, item.get('pr_number'), data.get('head_sha'), item.get('branch'))
        evidence = data.get('independence', item.get('review', {}).get('independence', {}))
        report = api.file(evidence.get('report_path', ''), snap['coord'], optional=True)
        q.require(report and data['head_sha'] in report and evidence.get('identity', '') in report,
                  'Publish the actual reader report, identity and full head before requesting review/decision')
    if event == 'checkpoint':
        observed = data.get('observed_ci', {})
        run = api.call(f'/actions/runs/{observed.get("run_id", 0)}')
        q.require(run and run['head_sha'] == data.get('head_sha') and run['status'] == 'completed'
                  and run['conclusion'] == observed.get('conclusion')
                  and run['path'] == '.github/workflows/lean.yml', 'Read actual completed WIP CI')
        actual_pr(api, data.get('pr_number'), data['head_sha'], item.get('branch'))
    if event == 'handover_mode':
        for transfer in data.get('transfers', []):
            previous = state['packages'].get(transfer.get('package_id'), {})
            if previous.get('pr_number'):
                actual_pr(api, previous['pr_number'], transfer.get('head_sha'), previous.get('branch'))
    if event in {'cancel_integration', 'cancel_infrastructure'}:
        lock = state.get('integration_lock') or {}
        pr = actual_pr(api, item.get('pr_number', lock.get('pr_number')), lock.get('head_sha'))
        q.require(pr['merged'] is False, 'A merged-main failure keeps its lock')
        data['pr_not_merged'] = True
    if event in {'accept', 'finish_infrastructure', *ADMIN}:
        head = data.get('integration_commit')
        q.require(head == snap['main'], 'Resulting main must be the actual current integration commit')
        data['main_ci'] = verified_ci(api, data.get('main_ci', {}).get('run_id'), head)
        lock = state.get('integration_lock') or {}
        pr = actual_pr(api, item.get('pr_number', lock.get('pr_number')), lock.get('head_sha'))
        q.require(pr['merged'] and pr['merge_commit_sha'] == head, 'Verify the actual merged PR')
        commit, source = api.commit(head), api.commit(lock['head_sha'])
        q.require([p['sha'] for p in commit['parents']] == [lock['base_main_sha'], lock['head_sha']]
                  and commit['tree']['sha'] == source['tree']['sha'],
                  'Preserve approved tree and ordered main/head history')


def propose(api, snap, request):
    allowed = {'schema_version', 'request_id', 'actor_id', 'project_id', 'policy_revision',
               'operation', 'event', 'data', 'expected_revision'}
    q.require(isinstance(request, dict) and set(request) <= allowed and request.get('schema_version') == 1,
              'Unknown request schema or fields')
    actor, project = request.get('actor_id'), request.get('project_id')
    q.actor_role(snap['policy'], project, {'actor_id': actor},
                 'review' if actor in snap['policy']['actors'] and
                 'implement' not in snap['policy']['actors'][actor]['roles'] else 'implement')
    q.require(request.get('policy_revision') == snap['state']['policy_revision'],
              'Reload actual policy and STATE; request policy revision is stale')
    action = request.get('operation')
    if action == 'status':
        answer = {'next_action': q.next_action(snap['registry'], snap['policy'], snap['state'], project, actor)}
        if request.get('data', {}).get('verify_ci') is True:
            answer['verified_main_ci'] = main_ci(api, snap['main'])
        return None, answer
    data = deepcopy(request.get('data', {}))
    q.require(isinstance(data, dict) and data.get('actor_id', actor) == actor, 'Request actor cannot be replaced')
    data['actor_id'] = actor
    data['request_id'] = actor + '/' + request['request_id']
    if action == 'claim_next':
        next_step = q.next_action(snap['registry'], snap['policy'], snap['state'], project, actor)
        if next_step['action'] != 'claim':
            return None, {'next_action': next_step}
        event = 'claim'
        data.update(package_id=next_step['package_id'], base_main_sha=snap['main'])
    else:
        q.require(action == 'event' and request.get('expected_revision') == snap['state']['revision'],
                  'Specific events require the exact observed STATE revision; reload on conflict')
        event = request.get('event')
    verify_evidence(api, snap, event, data)
    if event in ADMIN:
        result = ADMIN[event](snap['registry'], snap['policy'], snap['current_registry'],
            snap['current_policy'], snap['state'], project, data)
    else:
        result = q.transition(snap['registry'], snap['policy'], snap['state'], project, event, data)
    return result, {'event': event, 'package_id': data.get('package_id'),
                    'effective_revision': result['revision']}


def status(registry, policy, state, main):
    actors = [('root', policy['team_project_id'])] + [(a, int(p)) for p, a in
                                                     policy.get('chat_project_actors', {}).items()]
    return {'not_an_ownership_lease': True, 'state_revision': state['revision'],
            'policy_revision': state['policy_revision'], 'execution_mode': profiles.mode(policy, state),
            'claims_paused': state.get('claims_paused', False), 'main_sha': main,
            'accepted': sum(x['state'] == 'ACCEPTED' for x in state['packages'].values()),
            'integration_lock': state.get('integration_lock'),
            'available': q.available(registry, policy, state),
            'next_actions': {a: q.next_action(registry, policy, state, p, a) for a, p in actors},
            'active': {i: {'state': p['state'], 'owner_project_id': p['owner_project_id'],
                          'head_sha': p.get('head_sha', p.get('base_main_sha')),
                          'pr_number': p.get('pr_number'), 'branch': p.get('branch'),
                          'reviewer': p.get('review', {}).get('actor_id')}
                       for i, p in state['packages'].items() if p['state'] in q.ACTIVE}}


def process(api):
    inbox = api.ref(INBOX)
    files = api.files(inbox)
    receipts = api.files(api.ref('coordination'))
    processed = 0
    for path, blob in sorted(files.items()):
        if not path.startswith(REQUESTS) or not path.endswith('.json'):
            continue
        suffix = path[len(REQUESTS):]
        parts = suffix.split('/')
        if not (len(parts) == 2 and SLUG.fullmatch(parts[0]) and SLUG.fullmatch(parts[1][:-5])):
            print(json.dumps({'ignored_path': path, 'reason': 'Use requests/ACTOR/UNIQUE_ID.json'}))
            continue
        receipt_path = RESULTS + suffix
        if receipt_path in receipts:
            continue  # Never replay even if somebody wrongly edited an old request.
        for attempt in range(3):
            snap = snapshot(api)
            if api.file(receipt_path, snap['coord'], optional=True) is not None:
                break
            receipt = {'request_blob_sha': blob, 'request_path': path,
                       'coordination_parent': snap['coord'], 'main_sha': snap['main']}
            try:
                request = json.loads(api.file(path, inbox))
                q.require(isinstance(request, dict) and request.get('actor_id') == parts[0]
                          and request.get('request_id') == parts[1][:-5],
                          'Request identity and ID must match its immutable path')
                proposed, answer = propose(api, snap, request)
                receipt.update(status='applied' if proposed else 'no_change', **answer)
            except (ValueError, KeyError, TypeError, AttributeError) as error:
                proposed = None
                receipt.update(status='rejected', reason=str(error))
            effective = proposed or snap['state']
            registry, policy = ((snap['current_registry'], snap['current_policy']) if
                effective['policy_revision'] != snap['policy']['revision'] else (snap['registry'], snap['policy']))
            updates = {receipt_path: receipt, STATUS: status(registry, policy, effective, snap['main'])}
            if proposed:
                updates[str(q.DIRECTORY / 'STATE.json')] = proposed
            try:
                published = api.publish(snap['coord'], snap['tree'], updates,
                    f'Coordinate immutable request {suffix}: {receipt["status"]}')
            except Collision:
                if attempt == 2:
                    raise
                continue
            receipts[receipt_path] = published
            processed += 1
            print(json.dumps({'request': suffix, 'status': receipt['status'], 'coordination': published,
                              'revision': effective['revision']}))
            break
    return processed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', default=os.environ.get('GITHUB_REPOSITORY', 'shulda/lean_cco'))
    args = parser.parse_args()
    token = os.environ.get('GITHUB_TOKEN')
    q.require(token, 'GITHUB_TOKEN is required only inside the coordination workflow')
    print(json.dumps({'processed': process(GitHub(args.repository, token))}))


if __name__ == '__main__':
    main()
