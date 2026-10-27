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
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = Path('formalization/coordination')
STATES = {'AVAILABLE', 'IN_PROGRESS', 'SUBMITTED', 'REVIEWING',
          'INTEGRATING', 'CHANGES_REQUESTED', 'ACCEPTED', 'BLOCKED'}
ACTIVE = {'IN_PROGRESS'}
SHA = re.compile(r'[0-9a-f]{40}')


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(value):
    return isinstance(value, str) and bool(SHA.fullmatch(value))


def validate_policy(registry, policy):
    ids = {p['id'] for p in registry['packages']}
    require(policy.get('protocol_version') == 2, 'Queue requires protocol 2')
    require(policy.get('state_branch') == 'coordination', 'Unexpected state branch')
    require(policy.get('state_file') == str(DIRECTORY / 'STATE.json'), 'Unexpected state path')
    released = policy['released_packages']
    require(len(released) == len(set(released)) and set(released) <= ids,
            'Unknown or duplicate released package')
    projects = policy['registered_projects']
    require(projects and all(type(i) is int and i > 0 for i in projects)
            and len(projects) == len(set(projects)), 'Invalid registered projects')
    require(len(projects) <= policy['max_projects'], 'Too many registered projects')
    require(policy.get('review_requires_different_project') is True,
            'Independent package review is required')
    require(set(policy['coordinator_review_packages']) <= ids, 'Unknown review gate')


def validate_state(registry, policy, state):
    validate_policy(registry, policy)
    require(state.get('schema_version') == 1 and state.get('protocol_version') == 2,
            'Unknown live state schema')
    require(type(state.get('revision')) is int and state['revision'] > 0,
            'Invalid state revision')
    require(state.get('source_commit') == registry['source_commit'], 'Source pin mismatch')
    records = state['packages']
    require(set(records) == {p['id'] for p in registry['packages']}, 'Package registry mismatch')
    active = set()
    reviewers = set()
    for ident, item in records.items():
        status, owner = item['state'], item.get('owner_project_id')
        require(status in STATES, 'Unknown package state')
        require(owner is None or owner in policy['registered_projects'], 'Unknown package owner')
        if status == 'AVAILABLE':
            require(owner is None, 'Available package has an owner')
        else:
            require(owner is not None, 'Owned package has no owner')
        if status in ACTIVE:
            require(owner not in active, 'Project has more than one implementation')
            active.add(owner)
        if status == 'ACCEPTED':
            require(sha(item.get('accepted_commit')), 'Acceptance has no integration commit')
            validate_ci(item.get('main_ci', {}), item['accepted_commit'])
        review = item.get('review')
        if review:
            reviewer = review['project_id']
            require(reviewer == 0 or reviewer in policy['registered_projects'], 'Unknown reviewer')
            require(reviewer != owner, 'Author cannot accept their own package')
            require(sha(review['head_sha']), 'Review must name an exact head')
        if status in {'REVIEWING', 'INTEGRATING'}:
            require(review and review['head_sha'] == item.get('head_sha'),
                    'Leased review must bind the current submitted head')
            require(review['project_id'] not in reviewers, 'Duplicate review lease')
            reviewers.add(review['project_id'])
            if status == 'INTEGRATING':
                require(review.get('approved') is True, 'Integration needs approved review')
        if status in {'SUBMITTED', 'REVIEWING', 'INTEGRATING'}:
            require(sha(item.get('head_sha')) and type(item.get('pr_number')) is int
                    and item['pr_number'] > 0, 'Submission needs PR and exact head')
            validate_ci(item.get('ci', {}), item['head_sha'])
    lock = state.get('integration_lock')
    integrating = [i for i, x in records.items() if x['state'] == 'INTEGRATING']
    require((not integrating and lock is None) or
            (len(integrating) == 1 and lock is not None
             and integrating[0] == lock['package_id']
             and lock['project_id'] == records[integrating[0]]['review']['project_id']
             and lock['head_sha'] == records[integrating[0]]['head_sha']), 'Integration lock mismatch')
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


def next_action(registry, policy, state, project):
    validate_state(registry, policy, state)
    require(project in policy['registered_projects'], 'Project is not registered')
    reviewing = sorted(i for i, p in state['packages'].items()
                       if p.get('review', {}).get('project_id') == project
                       and p['state'] in {'REVIEWING', 'INTEGRATING'})
    if reviewing:
        return {'action': 'resume_review', 'package_id': reviewing[0]}
    reviews = sorted(i for i, p in state['packages'].items()
                     if p['state'] == 'SUBMITTED' and p['owner_project_id'] != project
                     and i not in policy['coordinator_review_packages'])
    if reviews:
        return {'action': 'review', 'package_id': reviews[0]}
    owned = sorted(i for i, p in state['packages'].items()
                   if p['owner_project_id'] == project and p['state'] in ACTIVE)
    if owned:
        return {'action': 'resume', 'package_id': owned[0]}
    repairs = sorted(i for i, p in state['packages'].items()
                     if p['owner_project_id'] == project and p['state'] == 'CHANGES_REQUESTED')
    if repairs:
        return {'action': 'repair', 'package_id': repairs[0]}
    candidates = available(registry, policy, state)
    if candidates and state.get('integration_lock') is None:
        return {'action': 'claim', 'package_id': candidates[0]}
    return {'action': 'wait', 'reason': 'No released dependency-ready job; check reports or notify Matěj.'}


def transition(registry, policy, state, project, event, data):
    """Return a new state; committing it remotely is a separate atomic step."""
    validate_state(registry, policy, state)
    require(project == 0 or project in policy['registered_projects'], 'Project is not registered')
    result = deepcopy(state)
    ident = data.get('package_id')
    records = result['packages']
    package = records.get(ident)
    if event in {'claim', 'repair'}:
        require(project != 0, 'Coordinator does not take implementation work')
        chosen = next_action(registry, policy, state, project)
        require(chosen.get('action') == event and chosen.get('package_id') == ident,
                'Must take the lowest eligible next job; resume existing work/review first')
        require(sha(data.get('base_main_sha')), 'Claim must pin the current green main')
        validate_ci(data.get('base_ci', {}), data['base_main_sha'])
        if event == 'claim':
            package.update(owner_project_id=project)
        package.update(state='IN_PROGRESS', claim_revision=state['revision'] + 1,
                       base_main_sha=data['base_main_sha'], base_ci=data['base_ci'])
        package.pop('review', None)
    elif event == 'submit':
        require(package and package['owner_project_id'] == project
                and package['state'] in {'IN_PROGRESS', 'SUBMITTED', 'REVIEWING', 'CHANGES_REQUESTED'},
                'Only assigned author can submit or refresh an unlocked submission')
        require(sha(data.get('head_sha')), 'Submission must name exact head')
        require(type(data.get('pr_number')) is int and data['pr_number'] > 0, 'Missing PR')
        require(data.get('report_path') == f'{DIRECTORY}/submissions/{ident}.md',
                'Use an immutable per-package submission report')
        validate_ci(data.get('ci', {}), data['head_sha'])
        package.update(state='SUBMITTED', head_sha=data['head_sha'],
                       pr_number=data['pr_number'], ci=data['ci'], report_path=data['report_path'])
        package.pop('review', None)
    elif event == 'review':
        require(package and package['state'] == 'SUBMITTED', 'Package is not submitted')
        require(project != package['owner_project_id'], 'Author cannot review their own package')
        if project:
            candidates = sorted(i for i, p in records.items()
                                if p['state'] == 'SUBMITTED' and p['owner_project_id'] != project
                                and i not in policy['coordinator_review_packages'])
            require(candidates and ident == candidates[0], 'Review the lowest eligible submission')
            require(ident not in policy['coordinator_review_packages'], 'Coordinator review gate')
            require(not any(p.get('review', {}).get('project_id') == project
                            and p['state'] in {'REVIEWING', 'INTEGRATING'} for p in records.values()),
                    'Project already has a review lease')
        require(data.get('head_sha') == package['head_sha'], 'Review head mismatch')
        package.update(state='REVIEWING', review={'project_id': project,
                       'head_sha': package['head_sha'], 'approved': False})
    elif event == 'refresh_review':
        require(package and package['state'] == 'REVIEWING'
                and package.get('review', {}).get('project_id') == project,
                'Only the leased reviewer can refresh a reviewed head')
        require(sha(data.get('head_sha')), 'Missing refreshed head')
        validate_ci(data.get('ci', {}), data['head_sha'])
        package.update(head_sha=data['head_sha'], ci=data['ci'])
        package['review'] = {'project_id': project, 'head_sha': data['head_sha'], 'approved': False}
    elif event in {'approve', 'request_changes'}:
        require(package and package['state'] == 'REVIEWING'
                and package.get('review', {}).get('project_id') == project,
                'Only the leased reviewer can decide')
        require(data.get('head_sha') == package['head_sha'], 'Review head mismatch')
        require(isinstance(data.get('summary'), str) and len(data['summary']) >= 40,
                'Review needs an actual source-fidelity/provider/consumer summary')
        package['review'].update(summary=data['summary'], approved=event == 'approve')
        if event == 'request_changes':
            package['state'] = 'CHANGES_REQUESTED'
    elif event == 'start_integration':
        require(package and package['state'] == 'REVIEWING'
                and package.get('review', {}).get('approved')
                and package['review']['project_id'] == project, 'Approved reviewer must integrate')
        require(result.get('integration_lock') is None, 'Another integration holds the lock')
        require(data.get('head_sha') == package['head_sha'], 'Reviewed head changed')
        require(sha(data.get('base_main_sha')) and data.get('head_contains_main') is True,
                'Bring current main into the reviewed head, review again and rerun CI')
        validate_ci(data.get('ci', {}), package['head_sha'])
        package.update(state='INTEGRATING')
        result['integration_lock'] = {'package_id': ident, 'project_id': project,
                                      'base_main_sha': data['base_main_sha'],
                                      'head_sha': package['head_sha']}
    elif event == 'cancel_integration':
        require(package and package['state'] == 'INTEGRATING'
                and package.get('review', {}).get('project_id') == project,
                'Only the locked reviewer can cancel')
        require(data.get('pr_not_merged') is True,
                'Do not release a lock after a failed merged-main build')
        package['state'] = 'REVIEWING'
        package['review']['approved'] = False
        result['integration_lock'] = None
    elif event == 'accept':
        require(package and package['state'] == 'INTEGRATING'
                and package.get('review', {}).get('project_id') == project,
                'Only the locked reviewer can accept')
        require(sha(data.get('integration_commit')), 'Missing integration commit')
        validate_ci(data.get('main_ci', {}), data['integration_commit'])
        package.update(state='ACCEPTED', accepted_commit=data['integration_commit'],
                       main_ci=data['main_ci'])
        result['integration_lock'] = None
    elif event == 'block':
        require(package and (project == 0 or package['owner_project_id'] == project
                                or package.get('review', {}).get('project_id') == project),
                'Only owner, leased reviewer or coordinator can block')
        require(package['state'] != 'ACCEPTED', 'Accepted packages require a reviewed repair decision')
        require(isinstance(data.get('reason'), str) and data['reason'], 'Missing blocker reason')
        # Preserve INTEGRATING/lock if main CI failed: no dependent may consume it.
        if package['state'] != 'INTEGRATING':
            package['state'] = 'BLOCKED'
        package['blocker'] = data['reason']
    else:
        raise ValueError('Unknown queue event')
    result['revision'] += 1
    result.setdefault('history', []).append({'revision': result['revision'], 'project_id': project,
                                           'event': event, 'package_id': ident})
    validate_state(registry, policy, result)
    return result


def compare_and_swap(current_head, expected_head, current, proposed):
    """Model the publication lease; the real guard is Git's non-force ref update."""
    require(current_head == expected_head, 'Stale coordination ref: reload and recompute')
    require(proposed['revision'] == current['revision'] + 1, 'Revision is not a single transition')
    return proposed


def render_instructions(registry, project):
    return f'''# Project {project} instructions — protocol 2

Jsi rovnocenný formalizační projekt č. {project} v https://github.com/{registry['public_repository']}.
Na začátku tahu čti aktuální `main/formalization/coordination/PROTOCOL.md`,
`AUTONOMY.json`, `BOARD.json`, `DECISIONS.md` a svůj report `reports/{project}.md`.
Živé přidělení a přijetí čti VÝHRADNĚ z větve `coordination`, souboru
`formalization/coordination/STATE.json`. Main BOARD je katalog, nikoli fronta.

Použij `tools/coordination_queue.py` a přesný postup `QUEUE_OPERATIONS.md`.
Dokonči své leased review; na dalším checkpointu nejprve zkontroluj nejnižší
cizí odevzdaný PR, pak pokračuj ve svém rozpracovaném balíčku. Pokud nemáš
rozpracováno, vezmi nejnižší volný uvolněný balíček, jehož
VŠECHNY závislosti jsou ACCEPTED. Převzetí platí až po atomickém non-force
zápisu do `coordination` nad přesně načteným headem. Při kolizi znovu načti
stav a přepočti výběr; nezačínej práci před úspěšným přidělením.

Implementuj na vlastní nové větvi z aktuálního zeleného `main`, čti celé
připnuté důkazy a proof notes. Ukládej commity, svůj report a per-package
`submissions/Bxxx.md`. Zachovej společné API/toolchain, skutečné předpoklady,
RAW/STRONG rozdíl a nulové nedokázané transitive providers. Vše importuj do
CCO a dolož přesný head, source map, consumer, CI a audit axiomů.

Po zeleném odevzdání označ balíček SUBMITTED ve frontě a můžeš autonomně
pokračovat dalším nezávislým úkolem. Odevzdaná větev ještě není závislost.
Cizí PR přijímej podle protokolu: druhý čtenář, přesný head, aktuální main
ve větvi, integrační zámek, merge a zelené výsledné main CI, pak ACCEPTED.
Vlastní balíček sám nepřijímej. Větev coordination nikdy nemerguj do main.

Matěje kontaktuj při skutečném blockeru, opravě matematiky, změně sdíleného
API/toolchainu, selhání integrace nebo pokud není další dostupná práce.
Běžné dokončení a převzetí dalšího uvolněného balíčku konzultaci nepotřebuje.
'''


def render_catalogue(registry):
    rows = ['# Package catalogue — protocol 2', '',
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
    parser.add_argument('--project', type=int)
    parser.add_argument('--event')
    parser.add_argument('--data', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    registry, policy, state = [json.loads(p.read_text())
                               for p in (args.registry, args.policy, args.state)]
    validate_state(registry, policy, state)
    if args.project is None:
        print(json.dumps({'valid': True, 'revision': state['revision'],
                          'available': available(registry, policy, state)}))
    elif args.event is None:
        print(json.dumps(next_action(registry, policy, state, args.project)))
    else:
        require(args.data is not None and args.output is not None, 'Event needs --data and --output')
        data = json.loads(args.data.read_text())
        proposed = transition(registry, policy, state, args.project, args.event, data)
        args.output.write_text(json.dumps(proposed, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps({'proposed_revision': proposed['revision'], 'published': False,
                          'next_step': 'Commit only on coordination with expected parent/ref and force=false.'}))


if __name__ == '__main__':
    main()
