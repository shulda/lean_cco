"""Execution policy and reversible ownership changes; no network or Git writes."""
from copy import deepcopy

SCOPE_NOTE = ('Work-specific historical notes above remain preserved; STATE.execution_mode selects '
              'execution_profiles. In chat mode each registered Chat project owns one unresolved '
              'batch and reviews only work it never authored.')


def mode(policy, state):
    return state.get('execution_mode', 'work')


def actor_project(policy, actor):
    return next((int(p) for p, a in policy.get('chat_project_actors', {}).items()
                 if a == actor), policy['team_project_id'])


def profile(policy, state):
    name = mode(policy, state)
    return policy.get('execution_profiles', {}).get(name, {
        'project_ids': [policy['team_project_id']],
        'default_active_batches': policy['default_active_batches'],
        'maximum_active_batches': policy['maximum_active_batches'],
        'per_project_limit': policy['maximum_active_batches']})


def validate_policy(q, policy):
    if 'execution_profiles' not in policy:
        q.require('chat_project_actors' not in policy, 'Chat actors need execution profiles')
        return
    profiles = policy['execution_profiles']
    actors = policy.get('chat_project_actors', {})
    q.require(isinstance(actors, dict) and actors and all(
        isinstance(p, str) and p.isdecimal() and str(int(p)) == p
        and int(p) not in {1, 2, policy['team_project_id']}
        and int(p) in policy['registered_projects'] for p in actors),
        'Chat projects need fresh registered positive IDs, never historical 1/2/3')
    q.require(len(set(actors.values())) == len(actors), 'Each Chat project needs its own actor')
    q.require(isinstance(profiles, dict) and set(profiles) == {'work', 'chat'},
              'Provide exactly work and chat execution profiles')
    q.require(profiles['work'] == {'project_ids': [policy['team_project_id']],
        'default_active_batches': 2, 'maximum_active_batches': 3, 'per_project_limit': 3},
        'Preserve the two/exceptional-three Work team policy')
    ids = sorted(map(int, actors))
    q.require(profiles['chat'] == {'project_ids': ids, 'default_active_batches': len(ids),
        'maximum_active_batches': len(ids), 'per_project_limit': 1},
        'Chat capacity is one unresolved batch per fresh registered project')
    for p, a in actors.items():
        entry = policy['actors'].get(a, {})
        q.require(entry.get('roles') == ['coordinate', 'implement', 'review', 'integrate']
                  and entry.get('historical_author_projects') == [int(p)],
                  'Chat actors need explicit project provenance and package-specific cross-review')


def validate_state(q, policy, state):
    q.require(mode(policy, state) in {'work', 'chat'} and
              (mode(policy, state) == 'work' or 'execution_profiles' in policy),
              'Unknown or undeployed execution profile')
    q.require(type(state.get('claims_paused', False)) is bool, 'Invalid claim pause flag')
    active = q.active_packages(state)
    p = profile(policy, state)
    q.require(all(state['packages'][i]['owner_project_id'] in p['project_ids'] for i in active),
              'Active ownership must belong to the current execution profile')
    q.require(len(active) <= p['maximum_active_batches'], 'Too many active batches')
    if mode(policy, state) == 'chat':
        q.require(all(sum(state['packages'][i]['owner_project_id'] == owner for i in active) <= 1
                      for owner in p['project_ids']), 'Each Chat project may own only one unresolved batch')


def authorize(q, policy, state, project, actor, event, package):
    if event in {'start_infrastructure', 'finish_infrastructure', 'cancel_infrastructure',
                 'pause_claims', 'resume_claims', 'switch_mode', 'handover_mode', 'handoff'}:
        return
    q.require(project in profile(policy, state)['project_ids']
              and actor_project(policy, actor) == project,
              'Actor is not authorized in this execution profile')
    if mode(policy, state) == 'chat' and event in {
            'repair', 'checkpoint', 'record_authorship', 'submit', 'block'}:
        q.require(package and package['owner_project_id'] == project,
                  'Only this Chat project may change its own implementation')


def next_action(q, registry, policy, state, project, actor):
    """Chat workers first finish locks/reviews, then their own repair/work."""
    if project not in profile(policy, state)['project_ids']:
        return {'action': 'wait', 'reason': 'This execution profile is inactive for this project.'}
    q.actor_role(policy, project, {'actor_id': actor}, 'implement')
    lock = state.get('integration_lock')
    if lock and lock.get('actor_id') == actor:
        result = {'action': 'finish_integration', 'package_id': lock.get('package_id'), 'lock': lock}
        # Checking the main run is first. While it is pending, independent
        # already-owned repair/work and an unleased foreign review are legal.
        eligible = q.eligible_reviews(policy, state, actor)
        leased = any(x['state'] in {'REVIEWING', 'INTEGRATING'}
            and x.get('review', {}).get('actor_id') == actor for x in state['packages'].values())
        if eligible and not leased:
            result['optional_review_while_ci_pending'] = eligible[0]
        own_repairs = sorted(i for i, x in state['packages'].items()
                             if x['state'] == 'CHANGES_REQUESTED' and x['owner_project_id'] == project)
        if own_repairs:
            result['optional_repair_while_ci_pending'] = own_repairs[0]
        return result
    own = [(i, x) for i, x in sorted(state['packages'].items())
           if x['state'] in q.ACTIVE and x['owner_project_id'] == project]
    for ident, item in sorted(state['packages'].items()):
        if item['state'] in {'REVIEWING', 'INTEGRATING'} and item.get('review', {}).get('actor_id') == actor:
            if not item['review'].get('approved'):
                return {'action': 'resume_review', 'package_id': ident}
            if not lock:
                return {'action': 'integrate', 'package_id': ident}
            if own and own[0][1]['state'] == 'IN_PROGRESS':
                return {'action': 'resume', 'package_id': own[0][0], 'waiting_integration': ident}
            if own and own[0][1]['state'] == 'CHANGES_REQUESTED':
                return {'action': 'repair', 'package_id': own[0][0], 'waiting_integration': ident}
            return {'action': 'wait_for_integration', 'package_id': ident}
    repairs = [i for i, x in own if x['state'] == 'CHANGES_REQUESTED']
    if repairs:
        return {'action': 'repair', 'package_id': repairs[0]}
    for ident, item in sorted(state['packages'].items()):
        if item['state'] == 'SUBMITTED':
            try:
                q.check_actor_non_author(policy, item, actor)
            except ValueError:
                continue
            return {'action': 'review', 'package_id': ident}
    # An author can integrate after a different project's actual approval.
    if not lock:
        for ident, item in own:
            if item['state'] == 'REVIEWING' and item.get('review', {}).get('approved'):
                return {'action': 'integrate', 'package_id': ident}
    if own:
        i, item = own[0]
        return {'action': ('resume' if item['state'] == 'IN_PROGRESS' else
                           'blocked' if item['state'] == 'BLOCKED' else 'wait_for_review'),
                'package_id': i, 'state': item['state']}
    candidates = q.available(registry, policy, state)
    if (candidates and not lock and not state.get('claims_paused', False)
            and not any(x['state'] == 'CHANGES_REQUESTED' for x in state['packages'].values())
            and len(q.active_packages(state)) < profile(policy, state)['default_active_batches']):
        return {'action': 'claim', 'package_id': candidates[0]}
    return {'action': 'wait', 'reason': ('New claims are paused for a handover.' if
        state.get('claims_paused', False) else 'No eligible released batch; finish reviews or await preparation.')}


def third_plan(q, policy, state, ident, data):
    existing = data.get('existing_batches', [])
    implementer = data.get('implementation_actor_id')
    q.require(data.get('independent_active_work') is True
        and len(data.get('summary', '')) >= 80 and data.get('active_work_items')
        and isinstance(implementer, str) and implementer
        and implementer not in {r['identity'] for r in policy['actors'].values()
                               if 'review' in r['roles']}
        and 'review' not in policy['actors'].get(implementer, {}).get('roles', [])
        and isinstance(data.get('independence_report_path'), str)
        and data['independence_report_path'].startswith(str(q.DIRECTORY / 'reports') + '/'),
        'Third batch needs concrete independent active work, owner and anchored report')
    expected = set(q.active_packages(state)) - {ident}
    q.require(len(existing) == 2 and len(expected) == 2
              and {e.get('package_id') for e in existing} == expected,
              'Third-slot independence must cover both actual current active batches')
    for e in existing:
        old = state['packages'][e['package_id']]
        q.require(e.get('head_sha') == old.get('head_sha', old.get('base_main_sha'))
                  and q.sha(e.get('head_sha')) and e.get('work_items')
                  and e.get('implementation_actor_ids'),
                  'Anchor existing work allocations to actual current heads and implementers')
        q.require(not set(data['active_work_items']) & set(e['work_items'])
                  and implementer not in e['implementation_actor_ids'],
                  'Third batch overlaps existing work or lacks an independent active implementer')
    return {k: deepcopy(data[k]) for k in ['package_id', 'independent_active_work', 'summary',
        'active_work_items', 'implementation_actor_id', 'independence_report_path', 'existing_batches']} | {
        'revision': state['revision'] + 1}


def deployment_manifest(q, previous_registry, previous_policy, registry, policy):
    q.validate_policy(previous_registry, previous_policy)
    q.require(registry == previous_registry, 'Profile deployment cannot change BOARD or mathematics')
    q.require(isinstance(policy, dict) and set(policy) == set(previous_policy) |
              {'execution_profiles', 'chat_project_actors'}, 'Unexpected policy fields')
    excluded = {'revision', 'registered_projects', 'actors', 'execution_profiles', 'chat_project_actors', 'notes'}
    q.require({k: v for k, v in policy.items() if k not in excluded} ==
              {k: v for k, v in previous_policy.items() if k not in excluded},
              'Profile deployment must preserve every existing permission, pin and release')
    old_notes = previous_policy.get('notes', [])
    q.require(policy.get('notes', []) in [old_notes, old_notes + [SCOPE_NOTE]],
              'Preserve old policy notes and only append their execution-profile scope')
    q.require(policy['revision'] == previous_policy['revision'] + 1,
              'Profile deployment advances policy revision exactly once')
    q.require(policy['registered_projects'][:len(previous_policy['registered_projects'])] ==
              previous_policy['registered_projects'], 'Preserve every historical project ID')
    q.require(all(policy['actors'].get(a) == e for a, e in previous_policy['actors'].items()),
              'Preserve every old actor, role, identity and original authorship')
    old_chat = previous_policy.get('chat_project_actors', {})
    q.require(all(policy.get('chat_project_actors', {}).get(p) == a for p, a in old_chat.items()),
              'Never remove or rename a registered Chat identity; idle projects simply stop')
    new_ids = set(policy['registered_projects']) - set(previous_policy['registered_projects'])
    new_actors = set(policy['actors']) - set(previous_policy['actors'])
    added = {p: a for p, a in policy.get('chat_project_actors', {}).items() if p not in old_chat}
    q.require(new_ids == set(map(int, added)) and new_actors == set(added.values()) and added,
              'Append only fresh Chat project/actor pairs')
    q.validate_policy(registry, policy)
    return {'previous_registry_sha256': q.fingerprint(previous_registry),
            'previous_policy_sha256': q.fingerprint(previous_policy),
            'registry_sha256': q.fingerprint(registry), 'policy_sha256': q.fingerprint(policy),
            'new_policy': deepcopy(policy)}


def validate_deployment_lock(q, registry, policy, state, manifest):
    q.require('execution_profiles' in policy or not q.active_packages(state),
              'Initial profile installation requires no active claims')
    expected = deployment_manifest(q, registry, policy, registry, manifest.get('new_policy', {}))
    q.require(manifest == expected, 'Profile lock must bind complete old/new snapshots')


def promote(q, previous_registry, previous_policy, registry, policy, state, project, data):
    q.validate_state(previous_registry, previous_policy, state)
    actor = q.actor_role(previous_policy, project, data, 'coordinate')
    q.actor_role(previous_policy, project, data, 'integrate')
    lock = state.get('integration_lock') or {}
    q.require(lock.get('kind') == 'infrastructure' and lock.get('actor_id') == actor,
              'Only the profile deployment lock holder may finish')
    manifest = deployment_manifest(q, previous_registry, previous_policy, registry, policy)
    q.require(lock.get('profile_deployment') == manifest and data.get('head_sha') == lock['head_sha'],
              'Profile promotion must match the reviewed locked snapshots and head')
    q.require(q.sha(data.get('integration_commit')), 'Missing actual resulting main')
    q.validate_ci(data.get('main_ci', {}), data['integration_commit'])
    target = data.get('target_mode', state.get('execution_mode', 'work'))
    q.require(target in policy['execution_profiles'], 'Unknown target mode')
    q.require(not q.active_packages(state) or target == mode(previous_policy, state),
              'Adding a worker preserves active ownership; switch modes with an explicit handover')
    result = deepcopy(state)
    result.update(policy_revision=policy['revision'], execution_mode=target,
                  claims_paused=False, integration_lock=None, revision=state['revision'] + 1)
    result.setdefault('infrastructure_integrations', []).append({**deepcopy(lock),
        'integration_commit': data['integration_commit'], 'main_ci': deepcopy(data['main_ci'])})
    result.setdefault('history', []).append({'revision': result['revision'], 'project_id': project,
        'actor_id': actor, 'event': 'promote_profiles', 'package_id': None, 'details': deepcopy(data)})
    q.validate_state(registry, policy, result)
    return result


def apply_mode_event(q, registry, policy, state, project, event, data):
    actor = q.actor_role(policy, project, data, 'coordinate')
    q.require('execution_profiles' in policy and data.get('user_authorized') is True,
              'Mode changes require deployed profiles and the actual user instruction')
    q.require(isinstance(data.get('summary'), str) and len(data['summary']) >= 80,
              'Record the real user instruction, stop acknowledgements and handover plan')
    result = deepcopy(state)
    if event == 'pause_claims':
        result['claims_paused'] = True
        return result
    q.require(state.get('integration_lock') is None, 'Finish the single integration lock first')
    q.require(q.sha(data.get('base_main_sha')), 'Mode change needs actual green main')
    q.validate_ci(data.get('base_ci', {}), data['base_main_sha'])
    if event == 'resume_claims':
        result['claims_paused'] = False
        return result
    target = data.get('target_mode')
    q.require(target in policy['execution_profiles'] and target != mode(policy, state),
              'Select the other deployed execution profile')
    active = q.active_packages(state)
    if event == 'switch_mode':
        q.require(not active, 'Use a confirmed WIP handover or drain every active claim first')
    else:
        q.require(state.get('claims_paused') is True and data.get('previous_workers_stopped') is True,
                  'WIP handover needs paused claims and actual confirmed stopped workers')
        transfers = data.get('transfers', [])
        q.require(len(transfers) == len(active) and
                  {x.get('package_id') for x in transfers} == set(active),
                  'Transfer every actual active claim exactly once')
        for entry in transfers:
            item = result['packages'][entry['package_id']]
            owner = entry.get('new_owner_project_id')
            q.require(entry.get('previous_owner_project_id') == item['owner_project_id']
                      and owner in policy['execution_profiles'][target]['project_ids'],
                      'Handover owners must match current claims and the target profile')
            q.require(entry.get('head_sha') == item.get('head_sha', item['base_main_sha']),
                      'Publish and checkpoint the latest WIP head before handover, even if CI fails')
            for key in ['branch', 'pr_number']:
                q.require(entry.get(key) == item.get(key), 'Preserve the existing branch and PR')
            original = deepcopy(item)
            new_actor = (policy['chat_project_actors'][str(owner)] if target == 'chat' else 'root')
            item.setdefault('handover_history', []).append({'revision': state['revision'] + 1,
                'previous_record': original, 'transfer': deepcopy(entry), 'coordinator': actor})
            item.update(owner_project_id=owner, state='IN_PROGRESS')
            item['author_actor_ids'] = sorted(set(item['author_actor_ids']) | {new_actor})
            item.pop('review', None)
        if target == 'work' and len(active) == 3:
            exception = data.get('third_batch_exception', {})
            q.require(exception.get('package_id') in active, 'Three Work claims need a real third-slot plan')
            result['third_batch_exception'] = third_plan(q, policy, result,
                                                        exception['package_id'], exception)
    result.update(execution_mode=target, claims_paused=False)
    if target == 'chat':
        result.pop('third_batch_exception', None)
    return result


def work_instructions(repository):
    return f'''# CCO Work project — project 3, actor root

Repozitář: https://github.com/{repository}. Jsi jeden Work formalizační tým,
project_id 3, actor_id root. Historické projekty 1/2 zůstávají zastavené;
nové Chat projekty mají jiné identity. Oprávnění pokračovat neznamená
oprávnění převzít jejich živé claimy bez řádného předání.

Na začátku každého tahu načti čerstvý main, AGENTS.md a
formalization/coordination/PROTOCOL.md, AUTONOMY.json, BOARD.json,
EXECUTION_PROFILES.md, QUEUE_OPERATIONS.md a COORDINATOR_RUNBOOK.md.
Živý stav čti na přesném headu větve coordination ze STATE.json; STATUS.json
je pouze odvozený přehled, nikoli claim. Zkontroluj skutečné PR heads a CI.
Pokud execution_mode není work, nic si neclaimuj. Návrat smí proběhnout jen
podle skutečného pokynu uživatele a RETURN_TO_WORK.md, bez resetu STATE.

Používej tools/coordination_queue.py a exact-parent non-force CAS. Standard
jsou dva neuzavřené batche za celý Work tým, třetí jen pro doloženou skutečně
nezávislou aktivní práci. Submit/review/integrace/blocker stále zabírají slot.
Opravy a dokončení mají přednost. Každá závislost musí být ACCEPTED na mainu.
Původní větve, všechny WIP commity, skuteční autoři a claim historie zůstávají.

Můžeš rozdělit nezávislé implementace mezi subagenty s oddělenými worktrees
a build výstupy. Samostatný skutečně neautorský reader nesmí navrhovat ani
psát implementaci kontrolovaného batchů. Eviduj všechny skutečné přispěvatele.
Nový reader musí být zaregistrován pod svou skutečnou identitou; starou roli
ani částečný report nepřejmenuj na nový souhlas. Při nedostupnosti původního
readeru použij explicitní reviewer_recovery podle protokolu. Tři Chat projekty
mohou vzájemně kontrolovat cizí batche, ale ne vlastní historické příspěvky.

Čti skutečné připnuté matematické důkazy, kontrakty, notes a Lean signatury.
Zachovej kvantifikátory, RAW/STRONG a AP/SAP/CCO, všechny skutečné providery
a quotient-action povinnosti. Podmíněný provider není source instance.
Žádné sorry/admit, nové axiomy, zesílené hypotézy ani změna source pinu.
Importuj konkrétní Mathlib moduly/taktiky v konzumentech; veřejné moduly
zahrň do CCO.lean. Zachovej toolchain, manifest, externí piny a axiom audit.

Ověř lean/lake proti připnutým verzím, manifest a malý inkrementální build.
Lokální instalace a cache mohou být po restartu pryč. Při doložené síťové
překážce neopakuj dlouhé stejné instalace: použij CI a nezávislou práci.
Kořeny Mathlib cache zjisti tools/mathlib_cache_roots.py --include-provider
--reject-broad; samotné cache get CCO.lean nestačí. Platné dependency cache
zachovej; buildy a přesný transitive audit zůstávají povinné.

Ukládej koherentní commity, per-package source map a přesné otevřené povinnosti.
Nečekej nečinně na jeden CI checkpoint. Po skutečném neautorském schválení
integruj autonomně pod jediným STATE zámkem: main jako předek schváleného
headu, čerstvé refs, expected-head merge se zachováním historie, CI a audit
výsledného mainu, teprve pak ACCEPTED. Head změna vyžaduje nový CI/review.
Merged-main selhání drží zámek. Nepiš přímo do mainu, nemerguj coordination
do mainu a nepřepisuj veřejný BOARD/STATE soukromou přípravnou verzí.

Rutinní práce a schválená integrace nepotřebují další souhlas uživatele.
Skutečné matematické mezery, změny zdroje/API/toolchainu a nevyřešené integrační
selhání vrať přípravě. Před koncem tahu ulož WIP a sděl konkrétní stav.
'''


def chat_instructions(repository, project, actor):
    return f'''# CCO Chat — project_id {project}, actor_id {actor}

Repozitář: https://github.com/{repository}. Jsi samostatný nový formalizační
Chat projekt s trvalou identitou chat-project:cco-{actor}. Toto číslo ani
identitu nepoužívej v jiném projektu. Nový chat uvnitř téhož projektu dědí
všechno jeho historické autorství. Projekty 1/2 jsou zastavené historické
projekty; project 3 je Work tým. Nejsi žádný z nich.

Při každém restartu čti čerstvý main: AGENTS.md a
formalization/coordination/PROTOCOL.md, AUTONOMY.json, EXECUTION_PROFILES.md,
CHAT_REQUESTS.md, BOARD.json a svou PROJECT_{project}_INSTRUCTIONS.md.
Živé claimy a přijetí jsou pouze coordination:formalization/coordination/STATE.json
na přesném observed headu. STATUS.json je levný odvozený přehled, ne vlastnictví.
Pokud execution_mode není chat, nepřebírej práci. Jedině uživatel autorizuje
změnu režimu; neřeš jeho nepřítomnost přesunem na jinou identitu.

Pracuj autonomně: dokonči vlastní integraci/review, oprav svůj batch, přečti
čekající cizí review, pokračuj ve vlastním důkazu, jinak claimni nejnižší
vydaný AVAILABLE batch s výhradně ACCEPTED závislostmi. Nejvýše jeden tvůj
neuzavřený batch včetně submit/review/integrace/blockeru. Čekání na CI neuvolní
slot. Při něm můžeš skutečně neautorsky kontrolovat cizí práci. Nezačínej
nevydané batche a neber cizí větev. Každý package má jednoho publishera.

Pro běžnou koordinaci používej append-only JSON requesty na větvi
coordination-requests podle CHAT_REQUESTS.md. Tvůj actor_id je {actor},
project_id je {project}. Každý request má nový unikátní request_id a soubor
coordination/requests/{actor}/ID.json. Starý request nikdy neupravuj.
Vyčkej jeho receipt na coordination ve formalization/coordination/requests/results/
{actor}/ID.json. Teprve applied + odpovídající skutečný STATE jsou účinný claim.
claim_next vybírá čerstvou frontu až na serveru; rejected/no_change nejsou claim.
Konkrétní eventy vážou policy_revision, expected_revision a přesný head.
Nepřepisuj STATE ručně. Přímý postup je možný jen přes aktuální Python validátor
a exact-parent non-force CAS. Ztracený CAS znamená znovu načíst a přepočítat.

Nejdřív ověř skutečné GitHub nástroje: čtení, vytvoření/změnu souboru, větev,
PR a expected-head merge. Pokud zápisy chybí, nehlásit úspěch a nepředstírat
push. Ulož připravený kód/report a popiš přesně chybějící schopnost. Nevyžaduj
lokální Lean, síť ani Python, pokud je nemáš; koherentní malé PR checkpointy
ověř vzdáleným Lean CI. Neinstaluj opakovaně nefunkční toolchain a neměň pin.

Čti skutečné připnuté zdrojové důkazy, kontrakt, PROOF_NOTES, package DAG,
aktuální kód a Lean signatury. Zachovej přesné hypotézy/kvantifikátory,
RAW/STRONG, AP/SAP/CCO a skutečné provider/quotient-action povinnosti.
Žádné sorry/admit, nové axiomy, záměna závěru za předpoklad ani změna zdroje.
Podmíněný provider není dokončená source instance. Závislosti nejsou k dispozici
jen proto, že jejich PR zezelenalo. Používej připnutý manifest/toolchain,
úzké Mathlib/tactic importy v konzumentech a všechny veřejné root importy.

Veď submissions/Bxxx.md se source-to-Lean mapou a všemi otevřenými providery,
vlastní průběžný report, skutečné autorství a obnovitelné commity. CI checkpoint
s chybou je WIP, nikoli dokončení. Submit pouze s celým skutečným kontraktem
a úspěšným exact-head buildem/auditem. Kontrola si sama přečte celý batch,
zdroj, providery, consumer a skutečný CI log; zkopírovaný cizí report nestačí.
Kontroluj pouze práci, kterou jsi nikdy nenavrhoval ani nepsal, včetně starších
chatů a pomoci jinému projektu. Review roli na vlastní kód nepřejmenuj.
Pokud při review začneš implementovat opravu, zaznamenej autorství a předej
review skutečně jinému neautorskému projektu. Head změna ruší starý souhlas.
Čtení a rozumné úzké kompilace autora zbytečně neduplikuj; nezávislý review
a konečné PR/main CI/audit zůstávají povinné.

Po skutečném cizím schválení integruj bez další otázky uživateli: request
start_integration, účinný jediný integrační zámek, znovu refs, expected-head
merge_method=merge přes GitHub nástroj. Nepoužívej squash/rebase. Poté počkej
na green CI/audit skutečného merge mainu a pošli accept. Autor může integrovat
po cizím review. Cizí zámek respektuj a mezitím dělej nezávislou vlastní práci.
Při již merged selhání zámek neruš; ulož konkrétní překážku pro přípravu.
Větev coordination nikdy nemerguj do mainu. Veřejný BOARD/STATE neresetuj.

Při odstranění projektu nejdřív dokonči jeho claim, review lease i integrační
zámek; potom stačí přestat promptovat. Autorství a registrace zůstávají.
Při pokynu k předání publikuj nejnovější WIP i chybový CI checkpoint a report,
potvrď zastavení; nepřebírej další práci. Mode handover zachová větev, PR,
head, zelený checkpoint i historii; žádné tiché opuštění claimu.

Rutinní důkazy, opravy a schválená integrace jsou autorizované. Skutečné mezery,
změny zdroje/API/toolchainu a nevyřešené selhání vrať přípravnému projektu.
Před koncem tahu ulož stav a stručně řekni co je skutečně hotovo a co zbývá.
'''


def generated_files(policy, repository):
    if 'execution_profiles' not in policy:
        return {}
    directory = 'formalization/coordination/'
    files = {directory + 'WORK_PROJECT_INSTRUCTIONS.md': work_instructions(repository)}
    rows = ['# Chat projekty — generováno z AUTONOMY.json', '',
            '| Projekt | project_id | actor_id | Instrukce | První prompt |',
            '|---|---|---|---|---|']
    for project, actor in sorted(policy['chat_project_actors'].items(), key=lambda x: int(x[0])):
        number = actor.removeprefix('chat-')
        name = f'PROJECT_{project}_INSTRUCTIONS.md'
        first = f'FIRST_PROMPT_CHAT_{number}.md'
        files[directory + name] = chat_instructions(repository, int(project), actor)
        files[directory + first] = f'''Jsi nový projekt CCO Chat {number}, project_id {project}, actor_id {actor}.
Pracuj v https://github.com/{repository} podle aktuálních projektových instrukcí.

Nejdřív načti čerstvý main, formalization/coordination/PROJECT_{project}_INSTRUCTIONS.md,
PROTOCOL.md, AUTONOMY.json, EXECUTION_PROFILES.md a CHAT_REQUESTS.md. Ověř skutečné
GitHub read/write/branch/PR/merge nástroje; není potřeba lokální Lean ani terminál.
Přečti levný STATUS.json a poté skutečný STATE na přesném headu coordination.

Pokud je režim chat a máš potřebné nástroje, zapiš vlastní stručný restartovací
report a pošli první unikátní status request. Po jeho potvrzení pokračuj podle
čerstvé fronty: případné vlastní review/integrace a opravy, neautorská kontrola
cizího odevzdaného batchů, vlastní rozpracovaná práce, jinak claim_next.
Pracovat na novém batchi začni až po účinném claimu. Přečti celý jeho kontrakt,
zdrojové důkazy, notes a přijaté závislosti, pak autonomně formalizuj.

Pokud není vydaný žádný připravený batch, nic si nerezervuj. Napiš, že jsi
připravený a čekáš na přípravu; nepouštěj se do nepublikovaného B049 jen podle
staršího textu. Aktuální číslo fronty vždy zjisti živě. Na prvním checkpointu
stručně potvrď svou identitu, výsledek testu nástrojů, účinný claim nebo čekání
a nejbližší skutečný důkaz. Dále pokračuj podle instrukcí bez rutinních dotazů.
'''
        rows.append(f'| CCO Chat {number} | {project} | {actor} | [{name}]({name}) | [{first}]({first}) |')
    rows += ['', 'Každý řádek je jiný skutečný projekt. Projekty 1/2 se z historie nepoužívají znovu.',
             'Nečinný prázdný projekt nevyžaduje odstranění registrace.', '']
    files[directory + 'CHAT_PROJECTS.md'] = '\n'.join(rows)
    files[directory + 'FIRST_PROMPT_WORK.md'] = f'''Přebíráš CCO formalizaci jako jeden Work tým, project 3, actor root,
v https://github.com/{repository}. Použij aktuální WORK_PROJECT_INSTRUCTIONS.md.
Nejprve načti čerstvý main/protokol/policy a živý STATE. Návrat na Work je mnou
autorizovaný; před převzetím si ověř skutečné zastavení případných Chat workerů.
Postupuj podle RETURN_TO_WORK.md. Při prázdné frontě použij switch_mode; při WIP
jen explicitní úplné handover_mode s aktuálními checkpointy a zachovanou historií.
Při chybějícím potvrzení zastavení nic nepřebírej a popiš konkrétní chybějící údaj.
Neresetuj STATE a nezačínej ze staršího zeleného commitu místo novějšího WIP.
Ověř lokální pinned Lean/Lake a jeden malý build; při síťové překážce pokračuj
přes CI. Rozděl nezávislé důkazy mezi subagenty a zajisti odděleného skutečně
neautorského readera pod jeho vlastní řádně registrovanou identitou.
Po účinném přepnutí pokračuj autonomně od skutečné fronty, ne od historických ID.
'''
    return files
