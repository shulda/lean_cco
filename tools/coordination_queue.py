#!/usr/bin/env python3
"""Pure, validated proposals for the GitHub coordination branch.

This program does NOT claim work, merge PRs, contact GitHub or certify proofs.
Publish its proposed STATE.json as a child of the EXACT observed coordination
commit, then update that ref with expected_sha and force=false. A rejected
update means reload, recompute and retry; never start work speculatively.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = Path('formalization/coordination')
STATES = {'AVAILABLE', 'IN_PROGRESS', 'SUBMITTED', 'REVIEWING',
          'INTEGRATING', 'CHANGES_REQUESTED', 'ACCEPTED', 'BLOCKED'}
ACTIVE = {'IN_PROGRESS', 'SUBMITTED', 'REVIEWING', 'INTEGRATING', 'CHANGES_REQUESTED', 'BLOCKED'}
IMPLEMENTING = {'IN_PROGRESS'}
SHA = re.compile(r'[0-9a-f]{40}')
SHA256 = re.compile(r'[0-9a-f]{64}')


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(value):
    return isinstance(value, str) and bool(SHA.fullmatch(value))


def fingerprint(value):
    """Stable digest of a complete parsed public catalogue or policy snapshot."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def registry_promotion_manifest(previous_registry, previous_policy, registry, policy):
    """Validate a strictly additive release and bind both complete snapshot pairs.

    This checks the data, not their Git origin or actual CI. The coordinator
    must read old snapshots at the locked base and new snapshots at the exact
    reviewed head/resulting main; their digests are retained in the sole lock.
    """
    validate_policy(previous_registry, previous_policy)
    require(set(registry) == set(previous_registry), 'Promotion cannot change catalogue fields')
    require(type(registry.get('revision')) is int
            and registry['revision'] in {previous_registry['revision'], previous_registry['revision'] + 1},
            'Catalogue revision must stay unchanged or advance once')
    require({k: v for k, v in registry.items() if k not in {'packages', 'revision'}} ==
            {k: v for k, v in previous_registry.items() if k not in {'packages', 'revision'}},
            'Promotion must preserve old catalogue metadata and source pin')
    old = previous_registry['packages']
    rows = registry.get('packages')
    require(isinstance(rows, list) and len(rows) > len(old) and rows[:len(old)] == old,
            'Promotion must append packages and preserve every old catalogue row')
    ids = [p.get('id') for p in rows]
    require(all(isinstance(i, str) and re.fullmatch(r'B[0-9]{3}', i) for i in ids)
            and len(ids) == len(set(ids)), 'Duplicate or invalid catalogue package IDs')
    additions = rows[len(old):]
    added_ids = [p['id'] for p in additions]
    # Independent prepared work may be released before lower numbered packages.
    # The complete old prefix and unique IDs above protect history; a numeric
    # frontier would permanently prevent releasing those held packages later.
    require(added_ids == sorted(added_ids),
            'Append each release\'s new package IDs in increasing order')
    for p in additions:
        require(p.get('state') == 'PLANNED' and p.get('owner_project_id') is None
                and p.get('accepted_commit') is None,
                'New catalogue rows must be unowned preparation, never accepted claims')
        require(type(p.get('contract_revision')) is int and p['contract_revision'] > 0
                and p.get('spec_file') == f'{DIRECTORY}/packages/{p["id"]}.md'
                and isinstance(p.get('name'), str) and p['name'].strip()
                and isinstance(p.get('scope'), str) and p['scope'].strip(),
                'New packages need concrete versioned contracts and scope')
        claims = p.get('claims')
        require(isinstance(claims, dict) and claims
                and all(isinstance(module, str) and module and isinstance(values, list) and values
                        and all(isinstance(c, str) and c for c in values)
                        and len(values) == len(set(values)) for module, values in claims.items()),
                'New packages need explicit nonduplicate mathematical claims')
    edges = {}
    for p in rows:
        deps = p.get('depends_on')
        require(isinstance(deps, list) and all(isinstance(d, str) and d in ids for d in deps)
                and len(deps) == len(set(deps)), 'Unknown or duplicate package dependencies')
        edges[p['id']] = deps
    visiting, visited = set(), set()

    def visit(ident):
        require(ident not in visiting, 'Package dependency cycle')
        if ident not in visited:
            visiting.add(ident)
            for dep in edges[ident]:
                visit(dep)
            visiting.remove(ident)
            visited.add(ident)

    for ident in ids:
        visit(ident)
    require(set(policy) == set(previous_policy)
            and {k: v for k, v in policy.items() if k not in {'revision', 'released_packages'}} ==
            {k: v for k, v in previous_policy.items() if k not in {'revision', 'released_packages'}},
            'Promotion must preserve policy roles, limits and all existing permissions')
    require(type(policy.get('revision')) is int and policy['revision'] == previous_policy['revision'] + 1,
            'Promotion advances policy revision exactly once')
    require(policy.get('released_packages') == previous_policy['released_packages'] + added_ids,
            'Release exactly the appended packages without changing old releases')
    validate_policy(registry, policy)
    return {'package_ids': added_ids,
            'previous_registry_sha256': fingerprint(previous_registry),
            'previous_policy_sha256': fingerprint(previous_policy),
            'registry_sha256': fingerprint(registry), 'policy_sha256': fingerprint(policy)}


def validate_promotion_manifest(manifest):
    fields = {'package_ids', 'previous_registry_sha256', 'previous_policy_sha256',
              'registry_sha256', 'policy_sha256'}
    require(isinstance(manifest, dict) and set(manifest) == fields,
            'Registry promotion needs a complete snapshot manifest')
    require(all(isinstance(manifest[k], str) and SHA256.fullmatch(manifest[k])
                for k in fields - {'package_ids'}), 'Invalid registry promotion snapshot digest')
    ids = manifest['package_ids']
    require(isinstance(ids, list) and ids
            and all(isinstance(i, str) and re.fullmatch(r'B[0-9]{3}', i) for i in ids)
            and ids == sorted(set(ids)), 'Invalid registry promotion package IDs')


def reviewer_recovery_manifest(previous_registry, previous_policy, registry, policy,
                               unavailable_actor_id, bootstrap_actor_id):
    """Bind an append-only recovery of genuinely fresh, review-only readers.

    No old actor is renamed or removed. This exception authorizes only review
    of the recovery infrastructure itself, never a mathematical approval.
    Actual reader independence and runtime failure remain external evidence.
    """
    validate_policy(previous_registry, previous_policy)
    require(registry == previous_registry, 'Reviewer recovery cannot change the catalogue')
    require(set(policy) == set(previous_policy)
            and {k: v for k, v in policy.items() if k not in {'revision', 'actors'}} ==
            {k: v for k, v in previous_policy.items() if k not in {'revision', 'actors'}},
            'Reviewer recovery must preserve every other policy field')
    require(type(policy.get('revision')) is int
            and policy['revision'] == previous_policy['revision'] + 1,
            'Reviewer recovery advances policy revision exactly once')
    old = previous_policy['actors']
    require(isinstance(policy.get('actors'), dict)
            and all(policy['actors'].get(a) == entry for a, entry in old.items()),
            'Reviewer recovery must preserve every old actor and identity')
    additions = {a: entry for a, entry in policy['actors'].items() if a not in old}
    require(1 <= len(additions) <= 2, 'Recover one or two genuinely fresh review-only readers')
    for entry in additions.values():
        require(isinstance(entry, dict)
                and set(entry) == {'identity', 'roles', 'historical_author_projects'}
                and entry['roles'] == ['review', 'integrate']
                and entry['historical_author_projects'] == [],
                'Recovered readers may only review and integrate, without historical authorship')
    require(isinstance(unavailable_actor_id, str)
            and unavailable_actor_id in old and 'review' in old[unavailable_actor_id]['roles'],
            'Identify an existing unavailable review actor')
    require(isinstance(bootstrap_actor_id, str) and bootstrap_actor_id in additions,
            'Recovery approval needs a genuinely new reader')
    validate_policy(registry, policy)
    return {'unavailable_actor_id': unavailable_actor_id,
            'bootstrap_actor_id': bootstrap_actor_id, 'new_actors': deepcopy(additions),
            'previous_registry_sha256': fingerprint(previous_registry),
            'previous_policy_sha256': fingerprint(previous_policy),
            'registry_sha256': fingerprint(registry), 'policy_sha256': fingerprint(policy)}


def recovery_policy(registry, policy, manifest):
    """Reconstruct and validate the ONLY prospective policy allowed by a lock."""
    fields = {'unavailable_actor_id', 'bootstrap_actor_id', 'new_actors',
              'previous_registry_sha256', 'previous_policy_sha256',
              'registry_sha256', 'policy_sha256'}
    require(isinstance(manifest, dict) and set(manifest) == fields,
            'Reviewer recovery needs a complete snapshot manifest')
    require(isinstance(manifest['new_actors'], dict), 'Invalid new reviewer actors')
    proposed = deepcopy(policy)
    proposed['revision'] += 1
    proposed['actors'].update(deepcopy(manifest['new_actors']))
    expected = reviewer_recovery_manifest(registry, policy, registry, proposed,
                                         manifest['unavailable_actor_id'],
                                         manifest['bootstrap_actor_id'])
    require(manifest == expected, 'Recovery lock must bind the exact old and prospective snapshots')
    return proposed


def check_reviewer_recovery(registry, policy, state, lock):
    prospective = recovery_policy(registry, policy, lock['reviewer_recovery'])
    manifest = lock['reviewer_recovery']
    missing = lock.get('unavailable_reviewer', {})
    unavailable = manifest['unavailable_actor_id']
    require(isinstance(missing, dict)
            and set(missing) == {'actor_id', 'identity', 'reason', 'report_path'}
            and missing['actor_id'] == unavailable
            and missing['identity'] == policy['actors'][unavailable]['identity']
            and isinstance(missing['reason'], str) and len(missing['reason']) >= 80
            and isinstance(missing['report_path'], str)
            and missing['report_path'].startswith(str(DIRECTORY / 'reports') + '/')
            and missing['report_path'].endswith('.md'),
            'Recovery needs durable evidence of the actual unavailable reviewer')
    require(state['protocol_version'] == 3 and 'registry_promotion' not in lock,
            'Reviewer recovery is separate from registry promotion and the old handoff')
    require(lock.get('review', {}).get('actor_id') == manifest['bootstrap_actor_id'],
            'Only the manifest-bound fresh reader may approve recovery infrastructure')
    for actor in manifest['new_actors']:
        # Even readers not approving this PR must be non-authors of it and of
        # every active batch. No current review/approval is transferred or reused.
        check_actor_non_author(prospective, lock, actor)
        for ident in active_packages(state):
            package = state['packages'][ident]
            require(not package.get('review'),
                    'Reviewer recovery requires active batches without review leases or approvals')
            check_actor_non_author(prospective, package, actor)
    check_independence(prospective, lock, manifest['bootstrap_actor_id'],
                       lock['review'].get('independence', {}))
    return prospective


def validate_policy(registry, policy):
    ids = {p['id'] for p in registry['packages']}
    require(policy.get('protocol_version') == 3, 'Queue requires protocol 3')
    require(policy.get('state_branch') == 'coordination', 'Unexpected state branch')
    require(policy.get('state_file') == str(DIRECTORY / 'STATE.json'), 'Unexpected state path')
    released = policy['released_packages']
    require(len(released) == len(set(released)) and set(released) <= ids,
            'Unknown or duplicate released package')
    projects = policy['registered_projects']
    require(projects and all(type(i) is int and i > 0 for i in projects)
            and len(projects) == len(set(projects)), 'Invalid registered projects')
    require(policy['team_project_id'] in projects, 'Missing Work team')
    require(policy['default_active_batches'] == 2 and policy['maximum_active_batches'] == 3,
            'Work team must default to two active batches, at most three')
    require(policy.get('submission_releases_implementation_slot') is False,
            'Submission must not stockpile new batches')
    require(policy.get('review_requires_non_author') is True, 'Non-author review is required')
    require(set(policy['coordinator_review_packages']) <= ids, 'Unknown review gate')
    identities = [r['identity'] for r in policy['actors'].values()]
    require(len(identities) == len(set(identities)), 'Actor aliases cannot share a stable identity')
    for actor, role in policy['actors'].items():
        require(isinstance(actor, str) and actor and isinstance(role.get('identity'), str)
                and role['identity'], 'Actor must have a stable identity')
        require(set(role['roles']) <= {'coordinate', 'implement', 'review', 'integrate'}, 'Unknown role')
        require(not ('review' in role['roles'] and 'implement' in role['roles']),
                'Review role must be separate from implementation')
        require(set(role['historical_author_projects']) <= set(projects), 'Unknown historical author')


def actor_role(policy, project, data, role):
    actor = data.get('actor_id')
    entry = policy['actors'].get(actor, {})
    require(project in {0, policy['team_project_id']} and role in entry.get('roles', []),
            'Actor is not authorized for this role; old projects are stopped')
    return actor


def active_packages(state):
    return [i for i, p in state['packages'].items() if p['state'] in ACTIVE]


def check_actor_non_author(policy, package, actor):
    role = policy['actors'].get(actor, {})
    require('review' in role.get('roles', []), 'Actor has no independent review role')
    author_identities = {policy['actors'].get(a, {}).get('identity', a)
                         for a in package.get('author_actor_ids', [])}
    require(actor not in package.get('author_actor_ids', [])
            and role.get('identity') not in author_identities, 'Author cannot review their own package')
    require(not set(role['historical_author_projects']) & set(package.get('original_author_project_ids', [])),
            'Historical author cannot review their own package under another role')


def check_independence(policy, package, actor, evidence):
    check_actor_non_author(policy, package, actor)
    role = policy['actors'][actor]
    require(evidence.get('identity') == role['identity'] and evidence.get('non_author') is True,
            'Review must identify the actual non-author reader')
    require(isinstance(evidence.get('summary'), str) and len(evidence['summary']) >= 80,
            'Explain actual independence from implementation, including original authorship')
    require(isinstance(evidence.get('report_path'), str)
            and evidence['report_path'].startswith(str(DIRECTORY / 'reviews') + '/')
            and evidence['report_path'].endswith('.md'), 'Use a durable independent review report')


def validate_state(registry, policy, state):
    validate_policy(registry, policy)
    require(state.get('schema_version') == 1 and state.get('protocol_version') in {2, 3},
            'Unknown live state schema')
    require(type(state.get('revision')) is int and state['revision'] > 0, 'Invalid state revision')
    require(state.get('source_commit') == registry['source_commit'], 'Source pin mismatch')
    if state['protocol_version'] == 3:
        require(state.get('policy_revision') == policy['revision'], 'State/policy revision mismatch')
    records = state['packages']
    require(set(records) == {p['id'] for p in registry['packages']}, 'Package registry mismatch')
    reviewers = set()
    for ident, item in records.items():
        status, owner = item['state'], item.get('owner_project_id')
        require(status in STATES, 'Unknown package state')
        require(owner is None or owner in policy['registered_projects'], 'Unknown package owner')
        require((owner is None) == (status == 'AVAILABLE'), 'Available/owned package mismatch')
        legacy_digest = hashlib.sha256(json.dumps(item, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        pinned_legacy = policy.get('legacy_accepted_records', {}).get(ident)
        if pinned_legacy:
            require(legacy_digest == pinned_legacy, 'Immutable legacy acceptance record changed')
        if status == 'ACCEPTED':
            require(sha(item.get('accepted_commit')), 'Acceptance has no integration commit')
            validate_ci(item.get('main_ci', {}), item['accepted_commit'])
            if not pinned_legacy:
                require(item.get('author_actor_ids') and item.get('original_author_project_ids')
                        and owner == policy['team_project_id'], 'Acceptance needs preserved authorship')
                require(item.get('review', {}).get('approved') is True
                        and item['review'].get('head_sha') == item.get('head_sha')
                        and len(item['review'].get('summary', '')) >= 80,
                        'Acceptance needs approved substantive exact-head independent review')
                require(sha(item.get('head_sha')) and type(item.get('pr_number')) is int
                        and item['pr_number'] > 0, 'Acceptance needs exact reviewed PR head')
                validate_ci(item.get('ci', {}), item['head_sha'])
        if state['protocol_version'] == 3 and status in ACTIVE:
            require(owner == policy['team_project_id'], 'Active claim has not been handed to the Work team')
            require(item.get('author_actor_ids') and item.get('original_author_project_ids'),
                    'Active package needs preserved authorship provenance')
        review = item.get('review')
        if review:
            require(sha(review['head_sha']), 'Review must name an exact head')
            # Only immutable pre-v3 accepted records retain their historical review format.
            if not (status == 'ACCEPTED' and pinned_legacy):
                require(review['head_sha'] == item.get('head_sha'), 'Review head mismatch')
                check_independence(policy, item, review.get('actor_id'), review.get('independence', {}))
        if status in {'REVIEWING', 'INTEGRATING'}:
            require(review and review['head_sha'] == item.get('head_sha'), 'Leased review must bind current head')
            reviewer = review.get('actor_id')
            require(reviewer not in reviewers, 'Duplicate review lease')
            reviewers.add(reviewer)
            if status == 'INTEGRATING':
                require(review.get('approved') is True, 'Integration needs approved review')
        if status in {'SUBMITTED', 'REVIEWING', 'INTEGRATING'}:
            require(sha(item.get('head_sha')) and type(item.get('pr_number')) is int
                    and item['pr_number'] > 0, 'Submission needs PR and exact head')
            validate_ci(item.get('ci', {}), item['head_sha'])
    if state['protocol_version'] == 3:
        count = len(active_packages(state))
        require(count <= policy['maximum_active_batches'], 'Too many active batches')
        if count > policy['default_active_batches']:
            exception = state.get('third_batch_exception', {})
            require(exception.get('package_id') in active_packages(state)
                    and exception.get('independent_active_work') is True
                    and len(exception.get('summary', '')) >= 80,
                    'Third batch needs documented genuinely independent active work')
    lock = state.get('integration_lock')
    integrating = [i for i, x in records.items() if x['state'] == 'INTEGRATING']
    if lock and lock.get('kind') == 'infrastructure':
        require(not integrating and sha(lock.get('head_sha')) and sha(lock.get('base_main_sha'))
                and 'integrate' in policy['actors'].get(lock.get('actor_id'), {}).get('roles', [])
                and type(lock.get('pr_number')) is int and lock['pr_number'] > 0,
                'Infrastructure integration lock mismatch')
        validate_ci(lock.get('ci', {}), lock['head_sha'])
        review = lock.get('review', {})
        require(review.get('head_sha') == lock['head_sha'] and review.get('approved') is True
                and len(review.get('summary', '')) >= 80, 'Invalid infrastructure review')
        if 'reviewer_recovery' in lock:
            check_reviewer_recovery(registry, policy, state, lock)
        else:
            check_independence(policy, lock, review.get('actor_id'), review.get('independence', {}))
        if 'registry_promotion' in lock:
            manifest = lock['registry_promotion']
            validate_promotion_manifest(manifest)
            require(state['protocol_version'] == 3 and not active_packages(state),
                    'Registry promotion requires a paused queue with no active claims')
            require(manifest['previous_registry_sha256'] == fingerprint(registry)
                    and manifest['previous_policy_sha256'] == fingerprint(policy),
                    'Promotion lock must bind the current old catalogue and policy snapshots')
            require(not set(manifest['package_ids']) & set(records),
                    'Promotion lock may only name new package IDs')
    else:
        require((not integrating and lock is None) or
                (len(integrating) == 1 and lock is not None
                 and integrating[0] == lock['package_id']
                 and lock['head_sha'] == records[integrating[0]]['head_sha']
                 and sha(lock.get('base_main_sha'))
                 and 'integrate' in policy['actors'].get(lock.get('actor_id'), {}).get('roles', [])), 'Integration lock mismatch')
    by_id = {p['id']: p for p in registry['packages']}
    for ident, item in records.items():
        if item['state'] != 'AVAILABLE':
            require(all(records[d]['state'] == 'ACCEPTED' for d in by_id[ident]['depends_on']),
                    'Owned package depends on an unaccepted prerequisite')
    return state


def validate_ci(ci, expected_head):
    require(ci.get('head_sha') == expected_head and ci.get('conclusion') == 'success'
            and type(ci.get('run_id')) is int and ci['run_id'] > 0
            and ci.get('axiom_audit') == 'allowlist', 'Missing exact-head successful CI/audit evidence')


def available(registry, policy, state):
    return sorted(p['id'] for p in registry['packages']
                  if p['id'] in policy['released_packages']
                  and state['packages'][p['id']]['state'] == 'AVAILABLE'
                  and all(state['packages'][d]['state'] == 'ACCEPTED' for d in p['depends_on']))


def next_action(registry, policy, state, project, actor=None):
    validate_state(registry, policy, state)
    require(project == policy['team_project_id'], 'Project is not registered as the active Work team')
    if state['protocol_version'] == 2:
        return {'action': 'wait', 'reason': 'Deploy protocol 3 and atomically hand off both existing claims first.'}
    role = policy['actors'].get(actor, {})
    if 'review' in role.get('roles', []):
        reviewing = sorted(i for i, p in state['packages'].items()
                           if p.get('review', {}).get('actor_id') == actor
                           and p['state'] in {'REVIEWING', 'INTEGRATING'})
        if reviewing:
            return {'action': 'resume_review', 'package_id': reviewing[0]}
        reviews = sorted(i for i, p in state['packages'].items() if p['state'] == 'SUBMITTED'
                         and actor not in p.get('author_actor_ids', [])
                         and not set(role['historical_author_projects']) & set(p.get('original_author_project_ids', [])))
        if reviews:
            return {'action': 'review', 'package_id': reviews[0]}
        return {'action': 'wait', 'reason': 'No eligible non-author review.'}
    require('implement' in role.get('roles', []), 'Actor has no implementation role')
    repairs = sorted(i for i, p in state['packages'].items() if p['state'] == 'CHANGES_REQUESTED')
    if repairs:
        return {'action': 'repair', 'package_id': repairs[0]}
    owned = sorted(i for i, p in state['packages'].items() if p['state'] == 'IN_PROGRESS')
    if owned:
        result = {'action': 'resume', 'package_ids': owned, 'package_id': owned[0]}
        candidates = available(registry, policy, state)
        if candidates and state.get('integration_lock') is None and len(active_packages(state)) < 2:
            result['optional_second_claim'] = candidates[0]
        return result
    candidates = available(registry, policy, state)
    if (candidates and state.get('integration_lock') is None
            and len(active_packages(state)) < policy['default_active_batches']):
        return {'action': 'claim', 'package_id': candidates[0]}
    if (state.get('integration_lock') is None and not active_packages(state)
            and all(state['packages'][i]['state'] == 'ACCEPTED'
                    for i in policy['released_packages'])):
        return {'action': 'wait', 'reason': 'All released batches are accepted; prepare the next additive package release.'}
    return {'action': 'wait', 'reason': 'Finish or repair active batches; submitted work still occupies a slot.'}


def transition(registry, policy, state, project, event, data):
    """Propose exactly one CAS event; external evidence must be independently read."""
    validate_state(registry, policy, state)
    result = deepcopy(state)
    ident = data.get('package_id')
    records = result['packages']
    package = records.get(ident)
    actor = data.get('actor_id')
    require(state['protocol_version'] == 3 or event in
            {'handoff', 'start_infrastructure', 'finish_infrastructure', 'cancel_infrastructure'},
            'Old live state permits only authorized migration or infrastructure serialization')
    if event == 'handoff':
        actor_role(policy, project, data, 'coordinate')
        require(result.get('integration_lock') is None, 'Finish infrastructure integration before handoff')
        require(state['protocol_version'] == 2 and data.get('previous_projects_stopped') is True,
                'One-time handoff needs the confirmed stop of both original projects')
        transfers = data.get('transfers', [])
        require({t.get('package_id') for t in transfers} == {'B002', 'B003'} and len(transfers) == 2,
                'Hand off B002 and B003 atomically')
        for entry in transfers:
            item = records[entry['package_id']]
            require(item['state'] == 'IN_PROGRESS' and item['owner_project_id'] == entry.get('previous_owner_project_id'),
                    'Handoff must match the original live claim')
            require(sha(entry.get('head_sha')) and type(entry.get('pr_number')) is int
                    and entry['pr_number'] > 0 and isinstance(entry.get('branch'), str) and entry['branch'],
                    'Handoff must pin existing branch, PR and current head')
            checkpoint = entry.get('last_green_checkpoint', {})
            require(sha(checkpoint.get('head_sha')), 'Preserve the last green checkpoint')
            validate_ci(checkpoint.get('ci', {}), checkpoint['head_sha'])
            observed = entry.get('observed_ci', {})
            require(observed.get('head_sha') == entry['head_sha'] and type(observed.get('run_id')) is int
                    and observed['run_id'] > 0 and observed.get('conclusion') in {'success', 'failure'},
                    'Record actual head CI, including a failing WIP head')
            original = item['owner_project_id']
            item['handoff_history'] = item.get('handoff_history', []) + [deepcopy(entry)]
            item.update(owner_project_id=policy['team_project_id'],
                        original_author_project_ids=[original],
                        author_actor_ids=[f'legacy-project-{original}', actor],
                        branch=entry['branch'], head_sha=entry['head_sha'], pr_number=entry['pr_number'],
                        observed_ci=observed, last_green_checkpoint=checkpoint,
                        handoff_revision=state['revision'] + 1)
        result['protocol_version'] = 3
        result['policy_revision'] = policy['revision']
    elif event in {'start_infrastructure', 'finish_infrastructure', 'cancel_infrastructure'}:
        actor_role(policy, project, data, 'integrate')
        if event == 'start_infrastructure':
            require(result.get('integration_lock') is None, 'Another integration holds the lock')
            require(sha(data.get('head_sha')) and sha(data.get('base_main_sha'))
                    and type(data.get('pr_number')) is int and data['pr_number'] > 0
                    and data.get('head_contains_main') is True, 'Infrastructure needs exact PR head and current main ancestry')
            validate_ci(data.get('ci', {}), data['head_sha'])
            review = data.get('review', {})
            require(review.get('head_sha') == data['head_sha'] and review.get('approved') is True
                    and review.get('actor_id') != actor and len(review.get('summary', '')) >= 80,
                    'Infrastructure needs substantive independent exact-head review')
            # Infrastructure authorship is explicit too; a distinct label alone is insufficient.
            authors = data.get('author_actor_ids', [])
            require(authors and review.get('actor_id') not in authors, 'Infrastructure reviewer is an author')
            review_policy = (recovery_policy(registry, policy, data['reviewer_recovery'])
                             if 'reviewer_recovery' in data else policy)
            check_independence(review_policy, {'author_actor_ids': authors,
                                       'original_author_project_ids': data.get('original_author_project_ids', [])},
                               review.get('actor_id'), review.get('independence', {}))
            result['integration_lock'] = {'kind': 'infrastructure', 'actor_id': actor,
                'head_sha': data['head_sha'], 'base_main_sha': data['base_main_sha'],
                'pr_number': data['pr_number'], 'review': deepcopy(review),
                'ci': deepcopy(data['ci']), 'author_actor_ids': deepcopy(authors),
                'original_author_project_ids': deepcopy(data.get('original_author_project_ids', []))}
            if 'registry_promotion' in data:
                actor_role(policy, project, data, 'coordinate')
                result['integration_lock']['registry_promotion'] = deepcopy(data['registry_promotion'])
            if 'reviewer_recovery' in data:
                actor_role(policy, project, data, 'coordinate')
                result['integration_lock']['reviewer_recovery'] = deepcopy(data['reviewer_recovery'])
                result['integration_lock']['unavailable_reviewer'] = deepcopy(data.get('unavailable_reviewer'))
        else:
            lock = result.get('integration_lock') or {}
            require(lock.get('kind') == 'infrastructure' and lock.get('actor_id') == actor,
                    'Only the infrastructure lock holder can finish or cancel')
            if event == 'finish_infrastructure':
                require('registry_promotion' not in lock,
                        'Finish a registry promotion atomically with promote_registry and both snapshot pairs')
                require('reviewer_recovery' not in lock,
                        'Finish reviewer recovery atomically with promote_reviewer and both snapshot pairs')
                require(sha(data.get('integration_commit')), 'Missing infrastructure integration commit')
                validate_ci(data.get('main_ci', {}), data['integration_commit'])
                result.setdefault('infrastructure_integrations', []).append({**lock,
                    'integration_commit': data['integration_commit'], 'main_ci': data['main_ci']})
            else:
                require(data.get('pr_not_merged') is True, 'Keep lock after failed merged-main CI')
            result['integration_lock'] = None
    elif event in {'claim', 'claim_third', 'repair'}:
        actor_role(policy, project, data, 'implement')
        require(result.get('integration_lock') is None, 'New claims wait for verified main under integration lock')
        if event == 'repair':
            chosen = next_action(registry, policy, state, project, actor)
            require(chosen.get('action') == 'repair' and chosen.get('package_id') == ident,
                    'Repair the lowest requested repair before continuing or claiming')
        else:
            candidates = available(registry, policy, state)
            require(package and candidates and candidates[0] == ident, 'Claim the lowest dependency-ready available package')
            require(not any(p['state'] == 'CHANGES_REQUESTED' for p in records.values()), 'Repairs have priority')
            count = len(active_packages(state))
            if event == 'claim_third':
                existing = data.get('existing_batches', [])
                implementer = data.get('implementation_actor_id')
                require(count == 2 and data.get('independent_active_work') is True
                        and len(data.get('summary', '')) >= 80 and data.get('active_work_items')
                        and isinstance(implementer, str) and implementer
                        and implementer not in {r['identity'] for r in policy['actors'].values() if 'review' in r['roles']}
                        and 'review' not in policy['actors'].get(implementer, {}).get('roles', [])
                        and isinstance(data.get('independence_report_path'), str)
                        and data['independence_report_path'].startswith(str(DIRECTORY / 'reports') + '/'),
                        'Third batch needs concrete independent active work, owner and anchored report')
                require(len(existing) == 2 and {e.get('package_id') for e in existing} == set(active_packages(state)),
                        'Third-slot independence must cover both actual current active batches')
                for e in existing:
                    old = records[e['package_id']]
                    require(e.get('head_sha') == old.get('head_sha', old.get('base_main_sha'))
                            and sha(e.get('head_sha')) and e.get('work_items') and e.get('implementation_actor_ids'),
                            'Anchor existing work allocations to actual current heads and implementers')
                    require(not set(data['active_work_items']) & set(e['work_items'])
                            and implementer not in e['implementation_actor_ids'],
                            'Third batch overlaps existing work or lacks an independent active implementer')
                result['third_batch_exception'] = {'package_id': ident, 'independent_active_work': True,
                    'summary': data['summary'], 'active_work_items': data['active_work_items'],
                    'implementation_actor_id': data['implementation_actor_id'],
                    'independence_report_path': data['independence_report_path'],
                    'existing_batches': deepcopy(existing), 'revision': state['revision'] + 1}
            else:
                require(count < policy['default_active_batches'], 'Two active batches already occupy the team slots')
            package.update(owner_project_id=policy['team_project_id'], author_actor_ids=[actor],
                           original_author_project_ids=[policy['team_project_id']])
        require(sha(data.get('base_main_sha')), 'Claim must pin current green main')
        validate_ci(data.get('base_ci', {}), data['base_main_sha'])
        package.update(state='IN_PROGRESS', claim_revision=state['revision'] + 1,
                       base_main_sha=data['base_main_sha'], base_ci=data['base_ci'])
        package.pop('review', None)
    elif event == 'checkpoint':
        actor_role(policy, project, data, 'implement')
        require(package and package['owner_project_id'] == project
                and package['state'] == 'IN_PROGRESS',
                'Only the owner can checkpoint unleased IN_PROGRESS work')
        require(sha(data.get('head_sha')) and type(data.get('pr_number')) is int
                and data['pr_number'] > 0, 'Checkpoint needs the actual WIP PR and exact head')
        require(package.get('pr_number', data['pr_number']) == data['pr_number'],
                'Checkpoint preserves the existing WIP PR')
        observed = data.get('observed_ci', {})
        require(observed.get('head_sha') == data['head_sha'] and type(observed.get('run_id')) is int
                and observed['run_id'] > 0 and observed.get('conclusion') in {'success', 'failure'},
                'Checkpoint needs observed success/failure CI at the exact WIP head')
        package.update(head_sha=data['head_sha'], pr_number=data['pr_number'],
                       observed_ci=deepcopy(observed), checkpoint_revision=state['revision'] + 1)
    elif event == 'record_authorship':
        actor_role(policy, project, data, 'coordinate')
        require(package and package['state'] == 'IN_PROGRESS', 'Record contributors before submission')
        contributors = data.get('author_actor_ids', [])
        require(contributors and all(isinstance(x, str) and x for x in contributors), 'Missing actual contributor identities')
        require(not any('review' in policy['actors'].get(x, {}).get('roles', []) for x in contributors),
                'Independent review role cannot implement; replace the reviewer through a policy decision')
        package['author_actor_ids'] = sorted(set(package['author_actor_ids']) | set(contributors))
    elif event == 'submit':
        actor_role(policy, project, data, 'implement')
        require(package and package['owner_project_id'] == project
                and package['state'] in {'IN_PROGRESS', 'SUBMITTED', 'REVIEWING', 'CHANGES_REQUESTED'},
                'Only assigned author can submit or refresh an unlocked submission')
        require(sha(data.get('head_sha')), 'Submission must name exact head')
        require(type(data.get('pr_number')) is int and data['pr_number'] > 0, 'Missing PR')
        require(data.get('report_path') == f'{DIRECTORY}/submissions/{ident}.md', 'Use durable per-package report')
        validate_ci(data.get('ci', {}), data['head_sha'])
        package.update(state='SUBMITTED', head_sha=data['head_sha'], pr_number=data['pr_number'],
                       ci=data['ci'], report_path=data['report_path'])
        package.pop('review', None)
    elif event == 'review':
        actor_role(policy, project, data, 'review')
        require(package and package['state'] == 'SUBMITTED', 'Package is not submitted')
        chosen = next_action(registry, policy, state, project, actor)
        require(chosen.get('action') == 'review' and chosen.get('package_id') == ident,
                'Finish leased review, then review lowest eligible submission')
        require(data.get('head_sha') == package['head_sha'], 'Review head mismatch')
        check_independence(policy, package, actor, data.get('independence', {}))
        package.update(state='REVIEWING', review={'project_id': project, 'actor_id': actor,
            'head_sha': package['head_sha'], 'approved': False, 'independence': data['independence']})
    elif event in {'refresh_review', 'approve', 'request_changes'}:
        actor_role(policy, project, data, 'review')
        require(package and package['state'] == 'REVIEWING'
                and package.get('review', {}).get('actor_id') == actor, 'Only leased non-author reviewer can decide')
        if event == 'refresh_review':
            require(sha(data.get('head_sha')), 'Missing refreshed head')
            validate_ci(data.get('ci', {}), data['head_sha'])
            package.update(head_sha=data['head_sha'], ci=data['ci'])
            package['review'].update(head_sha=data['head_sha'], approved=False)
            package['review'].pop('summary', None)
        else:
            require(data.get('head_sha') == package['head_sha'], 'Review head mismatch')
            require(isinstance(data.get('summary'), str) and len(data['summary']) >= 80,
                    'Review needs actual source/signature/provider/consumer and exact-head evidence')
            package['review'].update(summary=data['summary'], approved=event == 'approve')
            if event == 'request_changes':
                package['state'] = 'CHANGES_REQUESTED'
    elif event == 'start_integration':
        actor_role(policy, project, data, 'integrate')
        require(package and package['state'] == 'REVIEWING'
                and package.get('review', {}).get('approved'), 'Approved independent review is required')
        require(result.get('integration_lock') is None, 'Another integration holds the lock')
        require(data.get('head_sha') == package['head_sha'], 'Reviewed head changed')
        require(sha(data.get('base_main_sha')) and data.get('head_contains_main') is True,
                'Bring current main into reviewed head, review again and rerun CI')
        validate_ci(data.get('ci', {}), package['head_sha'])
        package['state'] = 'INTEGRATING'
        result['integration_lock'] = {'kind': 'package', 'package_id': ident, 'actor_id': actor,
            'base_main_sha': data['base_main_sha'], 'head_sha': package['head_sha']}
    elif event in {'cancel_integration', 'accept'}:
        actor_role(policy, project, data, 'integrate')
        lock = result.get('integration_lock') or {}
        require(package and package['state'] == 'INTEGRATING' and lock.get('actor_id') == actor
                and lock.get('package_id') == ident, 'Only locked integrator can finish')
        if event == 'cancel_integration':
            require(data.get('pr_not_merged') is True, 'Keep lock after failed merged-main build')
            package['state'] = 'REVIEWING'
            package['review']['approved'] = False
        else:
            require(sha(data.get('integration_commit')), 'Missing integration commit')
            validate_ci(data.get('main_ci', {}), data['integration_commit'])
            package.update(state='ACCEPTED', accepted_commit=data['integration_commit'], main_ci=data['main_ci'])
        result['integration_lock'] = None
    elif event == 'block':
        actor_role(policy, project, data, 'coordinate')
        require(package and package['state'] != 'ACCEPTED', 'Accepted package needs reviewed repair decision')
        require(isinstance(data.get('reason'), str) and data['reason'], 'Missing blocker reason')
        if package['state'] != 'INTEGRATING':
            package['state'] = 'BLOCKED'
        package['blocker'] = data['reason']
    else:
        raise ValueError('Unknown queue event')
    result['revision'] += 1
    result.setdefault('history', []).append({'revision': result['revision'], 'project_id': project,
        'actor_id': actor, 'event': event, 'package_id': ident, 'details': deepcopy(data)})
    validate_state(registry, policy, result)
    return result


def promote_registry(previous_registry, previous_policy, registry, policy, state, project, data):
    """Finish one reviewed registry deployment and append live AVAILABLE rows.

    Unlike ordinary events, this explicitly validates the still-old locked
    STATE against the previous public snapshots. There is no relaxed normal
    validator, inferred registry or path that reconstructs existing records.
    The returned proposal still needs the usual exact-parent non-force CAS.
    """
    validate_state(previous_registry, previous_policy, state)
    actor = actor_role(previous_policy, project, data, 'coordinate')
    actor_role(previous_policy, project, data, 'integrate')
    require(state['protocol_version'] == 3 and not active_packages(state),
            'Registry promotion requires a paused queue with no active claims')
    lock = state.get('integration_lock') or {}
    require(lock.get('kind') == 'infrastructure' and lock.get('actor_id') == actor,
            'Only the current infrastructure lock holder can promote the registry')
    manifest = registry_promotion_manifest(previous_registry, previous_policy, registry, policy)
    require(lock.get('registry_promotion') == manifest,
            'Promotion snapshots must match the complete reviewed lock manifest')
    require(data.get('head_sha') == lock['head_sha'], 'Registry promotion reviewed head mismatch')
    require(data.get('package_ids') == manifest['package_ids'], 'Promote exactly the locked package IDs')
    require(sha(data.get('integration_commit')), 'Missing infrastructure integration commit')
    validate_ci(data.get('main_ci', {}), data['integration_commit'])
    result = deepcopy(state)
    for ident in manifest['package_ids']:
        result['packages'][ident] = {'state': 'AVAILABLE', 'owner_project_id': None}
    result['policy_revision'] = policy['revision']
    result.setdefault('infrastructure_integrations', []).append({**deepcopy(lock),
        'integration_commit': data['integration_commit'], 'main_ci': deepcopy(data['main_ci'])})
    result['integration_lock'] = None
    result['revision'] += 1
    result.setdefault('history', []).append({'revision': result['revision'], 'project_id': project,
        'actor_id': actor, 'event': 'promote_registry', 'package_id': None,
        'details': {**deepcopy(data), 'registry_promotion': manifest}})
    validate_state(registry, policy, result)
    return result


def promote_reviewer(previous_registry, previous_policy, registry, policy, state, project, data):
    """Finish exactly the reviewed recovery without reconstructing any claim."""
    validate_state(previous_registry, previous_policy, state)
    actor = actor_role(previous_policy, project, data, 'coordinate')
    actor_role(previous_policy, project, data, 'integrate')
    lock = state.get('integration_lock') or {}
    require(lock.get('kind') == 'infrastructure' and lock.get('actor_id') == actor
            and 'reviewer_recovery' in lock,
            'Only the current recovery infrastructure lock holder can promote reviewers')
    old_manifest = lock['reviewer_recovery']
    manifest = reviewer_recovery_manifest(previous_registry, previous_policy, registry, policy,
                                         old_manifest['unavailable_actor_id'],
                                         old_manifest['bootstrap_actor_id'])
    require(manifest == old_manifest, 'Recovery snapshots must match the complete reviewed lock manifest')
    require(data.get('head_sha') == lock['head_sha'], 'Reviewer recovery reviewed head mismatch')
    require(sha(data.get('integration_commit')), 'Missing infrastructure integration commit')
    validate_ci(data.get('main_ci', {}), data['integration_commit'])
    result = deepcopy(state)
    result['policy_revision'] = policy['revision']
    result.setdefault('infrastructure_integrations', []).append({**deepcopy(lock),
        'integration_commit': data['integration_commit'], 'main_ci': deepcopy(data['main_ci'])})
    result['integration_lock'] = None
    result['revision'] += 1
    result.setdefault('history', []).append({'revision': result['revision'], 'project_id': project,
        'actor_id': actor, 'event': 'promote_reviewer', 'package_id': None,
        'details': {**deepcopy(data), 'reviewer_recovery': manifest}})
    validate_state(registry, policy, result)
    return result


def compare_and_swap(current_head, expected_head, current, proposed):
    """Model the publication lease; the real guard is Git's non-force ref update."""
    require(current_head == expected_head, 'Stale coordination ref: reload and recompute')
    require(proposed['revision'] == current['revision'] + 1, 'Revision is not a single transition')
    return proposed


def render_instructions(registry, project):
    return f'''# Work team instructions — protocol 3 (historical project {project})

Repozitář: https://github.com/{registry['public_repository']}. Původní projekty
1 a 2 jsou zastavené; jejich ID a autorství zůstávají v historii. Jeden Work
tým (project 3) koordinuje a dokončuje obě převzaté větve bez resetu WIP.

Na začátku čti čerstvý main: PROTOCOL.md, AUTONOMY.json, BOARD.json, runbook,
kontrakty, skutečný kód a reporty. Živé claimy/review/přijetí čti VÝHRADNĚ
z přesného headu coordination:formalization/coordination/STATE.json.
BOARD je katalog. Používej coordination_queue.py a QUEUE_OPERATIONS.md;
zápisy jsou účinné až po non-force CAS nad přesně načteným rodičem.

Standardně drž dva aktivní batche v celém týmu. SUBMITTED, REVIEWING,
INTEGRATING, CHANGES_REQUESTED i BLOCKED stále zabírají slot. Opravy a dokončení
mají přednost. Třetí batch potřebuje zaznamenanou konkrétní nezávislou aktivní
práci; žádné předběžné hromadění záloh. Všechny závislosti musí být ACCEPTED.

Čti původní připnuté důkazy i skutečné Lean signatury. Zachovej přesné
kvantifikátory, RAW/STRONG a AP/SAP/CCO. Podmíněný provider není source instance.
Žádné sorry/admit, nové axiomy ani zesílení hypotéz. Veřejné moduly importuj
do CCO.lean. Importuj konkrétní potřebné Mathlib moduly a taktiky; chybějící
import patří konzumentovi. Používej připnutý toolchain/manifest, malé inkrementy
a přesný transitive axiom audit. Ukládej commity a aktuální per-package report.

Celý batch kontroluje skutečně neautorský kontrolní agent. Jiné ID ani
přejmenování původního autora nezávislost nedokazuje. Zaznamenej všechny
původní i nové autory a skutečnou identitu, neautorství a samostatný report
reviewera. Review porovná původní zdroj, hypotézy, všechny provider discharge,
consumer a CI/audit přesného SHA. Kontrolní role nesmí psát implementaci.

Při nedostupnosti kontrolního runtime nesmí autor přejmenovat sebe ani použít
cizí nehotové review. Použij výslovný append-only reviewer_recovery manifest,
nezávislou kontrolu opravného infrastrukturního PR, jediný zámek a přesný PR/main
CI/audit. promote_reviewer atomicky aktivuje nové skutečné identity bez změny
claimů, přijetí nebo autorství; teprve pak může začít jejich vlastní nové review.

Po oprávněném nezávislém schválení integruj automaticky: jediný integrační
zámek i pro infrastrukturu, čerstvý main jako předek, schválený přesný PR head
se zeleným CI/auditem; potom merge se zachováním historie a zelený výsledný
main před ACCEPTED. Změna headu ruší schválení. Při selhání merged-main drž
zámek a vrať konkrétní problém přípravnému projektu. Větev coordination nikdy
nemerguj do main. Otevřené důkazy neoznačuj za dokončené.
'''


def render_catalogue(registry):
    rows = ['# Package catalogue — protocol 3', '',
            '**Live allocation and acceptance:** branch `coordination`,',
            '`formalization/coordination/STATE.json`. This main-branch table is a',
            'mathematical catalogue/initial checkpoint, not current ownership.', '',
            '| Package | Prerequisites | Contract |', '|---|---|---|']
    for p in registry['packages']:
        rows.append(f"| {p['id']}: {p['name']} | {', '.join(p['depends_on']) or '—'} | "
                    f"[{p['id']}](../../{p['spec_file']}) |")
    rows += ['', 'Autonomous release permissions are in [AUTONOMY.json](AUTONOMY.json).',
             'Use [QUEUE_OPERATIONS.md](QUEUE_OPERATIONS.md) to claim or review work.', '']
    return '\n'.join(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--registry', type=Path, default=ROOT / DIRECTORY / 'BOARD.json')
    parser.add_argument('--policy', type=Path, default=ROOT / DIRECTORY / 'AUTONOMY.json')
    parser.add_argument('--previous-registry', type=Path)
    parser.add_argument('--previous-policy', type=Path)
    parser.add_argument('--project', type=int)
    parser.add_argument('--event')
    parser.add_argument('--actor', default='root')
    parser.add_argument('--data', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    registry, policy, state = [json.loads(p.read_text())
                               for p in (args.registry, args.policy, args.state)]
    if args.event in {'promote_registry', 'promote_reviewer'}:
        require(args.previous_registry is not None and args.previous_policy is not None,
                args.event + ' requires explicit previous public registry and policy snapshots')
        require(args.project is not None and args.data is not None and args.output is not None,
                'Event needs --project, --data and --output')
        previous_registry = json.loads(args.previous_registry.read_text())
        previous_policy = json.loads(args.previous_policy.read_text())
        data = json.loads(args.data.read_text())
        data.setdefault('actor_id', args.actor)
        promote = promote_registry if args.event == 'promote_registry' else promote_reviewer
        proposed = promote(previous_registry, previous_policy, registry, policy,
                           state, args.project, data)
        args.output.write_text(json.dumps(proposed, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps({'proposed_revision': proposed['revision'], 'published': False,
                          'next_step': 'Commit only on coordination with expected parent/ref and force=false.'}))
        return
    require(args.previous_registry is None and args.previous_policy is None,
            'Previous snapshots are only valid for promote_registry or promote_reviewer')
    validate_state(registry, policy, state)
    if args.project is None:
        print(json.dumps({'valid': True, 'revision': state['revision'],
                          'available': available(registry, policy, state)}))
    elif args.event is None:
        print(json.dumps(next_action(registry, policy, state, args.project, args.actor)))
    else:
        require(args.data is not None and args.output is not None, 'Event needs --data and --output')
        data = json.loads(args.data.read_text())
        data.setdefault('actor_id', args.actor)
        proposed = transition(registry, policy, state, args.project, args.event, data)
        args.output.write_text(json.dumps(proposed, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps({'proposed_revision': proposed['revision'], 'published': False,
                          'next_step': 'Commit only on coordination with expected parent/ref and force=false.'}))


if __name__ == '__main__':
    main()
