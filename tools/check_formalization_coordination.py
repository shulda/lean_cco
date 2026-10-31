#!/usr/bin/env python3
"""Validate peer-project allocation and render its short instructions/board.

This checks preparation metadata. It does not certify Lean or GitHub setup.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path, PurePosixPath
import re

import build_formalization_module as modules


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = Path('formalization/coordination')
MODULES = ('raw_exact', 'strong_selectors', 'parity_hasse', 'exact_crt', 'canonical_hull', 'real_closure', 'finite_packets', 'rigid_groupoid', 'finite_kernel', 'owner_action', 'sir', 'owner_master', 'joint_owner', 'acl_owner_geometry', 'finite_lift', 'mi_geometry', 'owner_transversal', 'safe_readings', 'direct_owner_closure', 'hkn_reservoir', 'terminal_powers', 'full_rows', 'profile_helly', 'relative_mi', 'rank_induction', 'unary_support', 'full_code', 'reset_order', 'unary_hn', 'relational_completion', 'unary_fresh_frames', 'quotient_transport', 'simultaneous_quotients', 'finite_fibres', 'point_generated_sap', 'ap_character', 'clone_sap', 'orbital_cover_boundary', 'pair_safe_split', 'full_phase_lift', 'transition_closure', 'terminal_lattice', 'terminal_profiles', 'unary_terms_return', 'typed_orbit_frames', 'hereditary_hidden_orbits', 'hidden_sap_readings', 'guarded_two_root', 'guarded_old_seams', 'old_idempotent_forest', 'terminal_hidden_hn', 'clone_tuple_geometry', 'ap_ramsey_readout', 'exact_ep_geometry', 'automatic_ep_core', 'unfiltered_ep')
STATES = {'PLANNED', 'PREPARED', 'ASSIGNED', 'BLOCKED', 'SUBMITTED', 'ACCEPTED'}
CURRENT = STATES - {'PLANNED', 'ACCEPTED'}


def valid_repository(value):
    return (isinstance(value, str) and re.fullmatch(
        r'[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*', value)
        and not value.endswith('.git'))


def validate(root, board, require_launch=False):
    if board.get('schema_version') != 1 or board.get('protocol_version') not in {1, 2, 3}:
        raise ValueError('Unsupported coordination schema/protocol')
    if type(board.get('revision')) is not int or board['revision'] < 1:
        raise ValueError('Invalid board revision')
    if board.get('phase') not in {'PREPARATION', 'READY'}:
        raise ValueError('Unknown launch phase')
    if board.get('protocol_version') in {2, 3} and board.get('phase') == 'READY':
        import coordination_queue as queue
        policy = json.loads((root / DIRECTORY / 'AUTONOMY.json').read_text())
        queue.validate_policy(board, policy)
        if board.get('allocation_authority') != {'branch': policy['state_branch'], 'file': policy['state_file']}:
            raise ValueError('Live allocation authority differs from policy')
    repository = board.get('public_repository')
    if repository is not None and not valid_repository(repository):
        raise ValueError('Invalid public repository')
    if board.get('default_branch') != 'main':
        raise ValueError('Review instructions before changing the default branch')
    projects = board['projects']
    ids = [p['id'] for p in projects]
    if any(type(i) is not int or i < 1 for i in ids) or len(ids) != len(set(ids)):
        raise ValueError('Project IDs must be unique positive integers')
    if any(p['state'] not in {'RESERVED', 'ACTIVE', 'WAITING', 'PAUSED'} for p in projects):
        raise ValueError('Unknown project state')
    packages = board['packages']
    modules.topological_order(packages)
    by_package = {p['id']: p for p in packages}
    if any(not re.fullmatch(r'B[0-9]{3}', p['id']) for p in packages):
        raise ValueError('Invalid package ID')
    assigned = {}
    known_claims = {}
    declarations = json.loads((root / 'catalogue/declarations.json').read_text())
    if board['source_commit'] != declarations['summary']['source_commit']:
        raise ValueError('Coordination and mathematical source pins differ')
    labels = set(modules.catalogue_references(declarations['declarations']))
    for ident in MODULES:
        config = json.loads((root / 'formalization' / ident / 'module.json').read_text())
        known_claims[ident] = {c['id'] for c in config['claims']}
    covered = set()
    for package in packages:
        if package['state'] not in STATES:
            raise ValueError('Unknown package state')
        if type(package['contract_revision']) is not int or package['contract_revision'] < 1:
            raise ValueError('Invalid contract revision')
        owner = package['owner_project_id']
        if owner is not None and (type(owner) is not int or owner not in ids):
            raise ValueError('Unknown project owner')
        if package['state'] == 'PLANNED' and owner is not None:
            raise ValueError('Unprepared planned package has an owner')
        if package['state'] in CURRENT:
            if owner is None:
                raise ValueError('Current package has no owner')
            if owner in assigned:
                raise ValueError('Project has more than one current package')
            assigned[owner] = package['id']
        if package['state'] in {'ASSIGNED', 'SUBMITTED', 'ACCEPTED'}:
            if any(by_package[d]['state'] != 'ACCEPTED' for d in package['depends_on']):
                raise ValueError('Package depends on an unaccepted prerequisite')
        if package['state'] == 'ACCEPTED' and not re.fullmatch(
                r'[0-9a-f]{40}', package.get('accepted_commit') or ''):
            raise ValueError('Accepted package lacks an integration commit')
        path = PurePosixPath(package['spec_file'])
        if path.is_absolute() or '..' in path.parts or not (root / str(path)).is_file():
            raise ValueError('Missing or unsafe package specification')
        for module, claims in package['claims'].items():
            if module not in known_claims or not set(claims) <= known_claims[module]:
                raise ValueError('Unknown package claim')
            for claim in claims:
                key = (module, claim)
                if key in covered:
                    raise ValueError('Claim assigned to multiple packages')
                covered.add(key)
        if not set(package.get('additional_source_exports', [])) <= labels:
            raise ValueError('Unknown additional source export')
    expected = {(module, claim) for module, claims in known_claims.items() for claim in claims}
    if covered != expected:
        raise ValueError('Current preparation claims missing from package plan')
    seen_sources = set()
    for source in board['source_files']:
        name = source['file']
        path = PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or name in seen_sources:
            raise ValueError('Invalid coordination source path')
        seen_sources.add(name)
        if modules.blob_sha((root / name).read_bytes()) != source['git_blob']:
            raise ValueError(f'Coordination source changed: {name}')
    active = {p['id'] for p in projects if p['state'] == 'ACTIVE'}
    if board['phase'] == 'PREPARATION':
        if repository is not None or active or any(p['state'] == 'ASSIGNED' for p in packages):
            raise ValueError('Preparation state pretends to have launched')
    else:
        if not repository or not active <= assigned.keys():
            raise ValueError('Ready launch lacks repository or active assignment')
    if require_launch and board['phase'] != 'READY':
        raise ValueError('Public repository not bound and first assignment not activated')
    return assigned


def render_instructions(board, project_id):
    if board.get('protocol_version') in {2, 3} and board['phase'] == 'READY':
        import coordination_queue as queue
        return queue.render_instructions(board, project_id)
    package = next(p for p in board['packages']
                   if p['owner_project_id'] == project_id and p['state'] in CURRENT)
    repository = board['public_repository']
    destination = (f'https://github.com/{repository}' if repository else
                   'DOSUD NEURČEN — tento text zatím nevkládej do projektu')
    return f'''# Project {project_id} instructions

Jsi formalizační projekt č. {project_id}. Repozitář: {destination}.

Na začátku pracovního tahu čti aktuální `main`:

- `formalization/coordination/BOARD.json` — přidělení a revize úkolu;
- `formalization/coordination/PROTOCOL.md` — pravidla práce;
- `formalization/coordination/DECISIONS.md` — společná rozhodnutí;
- `formalization/coordination/reports/{project_id}.md` — tvůj checkpoint.

Tvůj současný balíček je {package['id']}:
`{package['spec_file']}`. Rozhodující je aktuální přidělení v boardu.
Pracuj autonomně v jeho rozsahu, čti připnuté důkazy i proof notes a průběžně
ukládej obnovitelné commity a vlastní report. Dílčí lemmata jsou tvoje interní
kroky. Nepřebírej si sám další balíček ani úkol jiného projektu.

Používej vlastní větev a PR; nepiš přímo do `main`. Dodržuj společné API a
toolchain. Dokončené exporty musí mít doložené předpoklady a žádné nedokázané
závislosti. Podmíněný důkaz vykazuj jako podmíněný. Změny matematiky vrať
v reportu; lidský článek samovolně nepřepisuj.

Při dokončení, blokujícím problému nebo potřebě změnit společné API či rozsah
ulož stav a řekni Matějovi: balíček, commit/PR, výsledek nebo přesná překážka
a navržený další krok. Matěj to vyřeší s přípravným projektem. Běžná práce
uvnitř zadání souhlas nevyžaduje. Žádný nadřazený formalizační projekt není.
'''


def render_board(board):
    if board.get('protocol_version') in {2, 3} and board['phase'] == 'READY':
        import coordination_queue as queue
        return queue.render_catalogue(board)
    repository = board['public_repository'] or 'not yet bound'
    rows = ['# Project allocation — generated from BOARD.json', '',
            f"Revision {board['revision']}; phase **{board['phase']}**; public repository: **{repository}**.", '',
            '| Package | Owner | State | Prerequisites | Mathematical scope |',
            '|---|---|---|---|---|']
    for p in board['packages']:
        owner = str(p['owner_project_id']) if p['owner_project_id'] is not None else '—'
        deps = ', '.join(p['depends_on']) or '—'
        rows.append(f"| [{p['id']}: {p['name']}](../../{p['spec_file']}) | {owner} | {p['state']} | {deps} | {p['scope']} |")
    rows += ['', 'Only B001 has a complete launch contract. Later rows are planning envelopes.',
             'Package edges schedule work; consult the module claim DAG for actual theorem dependencies.',
             'No Lean export is certified by this allocation table.', '']
    return '\n'.join(rows)


def generated(board):
    files = {str(DIRECTORY / 'BOARD.md'): render_board(board)}
    for project in board['projects']:
        if (board.get('protocol_version') in {2, 3} and board['phase'] == 'READY') or any(
                p['owner_project_id'] == project['id'] and p['state'] in CURRENT
                for p in board['packages']):
            path = DIRECTORY / f"PROJECT_{project['id']}_INSTRUCTIONS.md"
            files[str(path)] = render_instructions(board, project['id'])
    if board.get('phase') == 'READY' and board.get('protocol_version') in {2, 3}:
        import coordination_profiles
        policy = json.loads((ROOT / DIRECTORY / 'AUTONOMY.json').read_text())
        files.update(coordination_profiles.generated_files(policy, board['public_repository']))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--require-launch', action='store_true')
    args = parser.parse_args()
    board = json.loads((ROOT / DIRECTORY / 'BOARD.json').read_text())
    assigned = validate(ROOT, board, args.require_launch)
    for path, content in generated(board).items():
        target = ROOT / path
        if args.check:
            if not target.exists() or target.read_text() != content:
                raise ValueError(f'Stale generated coordination file: {path}')
        else:
            target.write_text(content)
    print(f"Coordination valid: {len(board['packages'])} package envelopes, "
          f"{len(assigned)} reserved/current project, phase {board['phase']}; no Lean certification.")


if __name__ == '__main__':
    main()
