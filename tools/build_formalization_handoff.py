#!/usr/bin/env python3
"""Build/verify a deterministic source handoff for OTHER Lean projects.

This packages preparation only. It never creates a Lean project or runs CI.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile

import build_formalization_module as module_tool
import check_formalization_coordination as coordination


ROOT = Path(__file__).resolve().parents[1]
MODULES = ('raw_exact', 'strong_selectors', 'parity_hasse', 'exact_crt', 'canonical_hull', 'real_closure', 'finite_packets', 'rigid_groupoid', 'finite_kernel', 'owner_action', 'sir', 'owner_master', 'joint_owner', 'acl_owner_geometry', 'finite_lift', 'mi_geometry', 'owner_transversal', 'safe_readings', 'direct_owner_closure', 'hkn_reservoir', 'terminal_powers', 'full_rows', 'profile_helly', 'relative_mi', 'rank_induction', 'unary_support', 'full_code', 'reset_order', 'unary_hn', 'relational_completion', 'unary_fresh_frames', 'quotient_transport', 'simultaneous_quotients', 'finite_fibres', 'point_generated_sap', 'ap_character', 'clone_sap', 'orbital_cover_boundary', 'pair_safe_split', 'full_phase_lift', 'transition_closure', 'terminal_lattice', 'terminal_profiles', 'unary_terms_return', 'typed_orbit_frames', 'hereditary_hidden_orbits', 'hidden_sap_readings', 'guarded_two_root', 'guarded_old_seams', 'old_idempotent_forest', 'terminal_hidden_hn', 'clone_tuple_geometry', 'ap_ramsey_readout', 'exact_ep_geometry', 'automatic_ep_core', 'unfiltered_ep')
MANIFEST = 'HANDOFF_MANIFEST.json'


def collect(root):
    declarations = json.loads((root / 'catalogue/declarations.json').read_text())
    paths = {'formalization/README.md', 'formalization/HANDOFF.md',
             'formalization/EXTERNAL_PROVIDER_BUILD_CACHE.md',
             'formalization/FACTORIZATION_FOREST_PROVIDER.md',
             'formalization/PREPARATION_COVERAGE.md',
             'formalization/PREPARATION_COMPLETION_REVIEW.md',
             'formalization/preparation_coverage.json',
             'catalogue/declarations.json', 'tools/build_formalization_module.py',
             'tools/build_formalization_handoff.py', 'tools/test_formalization_module.py',
             'tools/test_formalization_handoff.py', 'tools/test_external_provider_metadata.py',
             'tools/test_prepared_release_metadata.py',
             'tools/check_formalization_coordination.py',
             'tools/prepare_formalization_launch.py',
             'tools/test_formalization_coordination.py', 'tools/coordination_queue.py',
             'tools/test_coordination_queue.py', 'tools/test_registry_promotion.py',
             'tools/coordination_profiles.py', 'tools/coordination_broker.py',
             'tools/configure_execution_profiles.py', 'tools/test_execution_profiles.py',
             'tools/test_coordination_broker.py'}
    board = json.loads((root / coordination.DIRECTORY / 'BOARD.json').read_text())
    coordination.validate(root, board)
    for path, content in coordination.generated(board).items():
        if (root / path).read_text() != content:
            raise ValueError(f'Stale coordination file: {path}')
    paths.update(str(path.relative_to(root)) for path in
                 (root / coordination.DIRECTORY).rglob('*')
                 if path.is_file() and path.suffix in {'.json', '.md'})
    paths.update(item['file'] for item in board['source_files'])
    modules = []
    for ident in MODULES:
        directory = Path('formalization') / ident
        config = json.loads((root / directory / 'module.json').read_text())
        order, by_label, raw = module_tool.validate(root, config, declarations)
        if (root / directory / 'README.md').read_text() != module_tool.render(config, order, by_label, raw):
            raise ValueError(f'Stale module index: {ident}')
        paths.update(str(directory / name) for name in ['README.md', 'PROOF_NOTES.md', 'module.json'])
        paths.update(x['file'] for x in config['source_files'])
        paths.add(config.get('control_script', 'tools/check_raw_exact_controls.py'))
        modules.append({'id': ident, 'definitions': len(config['definitions']),
                        'claims': len(config['claims']), 'source_exports': len(config['exports']),
                        'tasks': len(config['tasks']), 'source_commit': config['source_commit'],
                        'imports': config.get('imports', []),
                        'external_providers': config.get('external_providers', []),
                        'proof_status': config['status']})
    files = {path: (root / path).read_bytes() for path in sorted(paths)}
    manifest = {'format_version': 1,
                'purpose': 'Mathematical preparation and work orders for separate receiving Lean projects; no Lean proof or compiled provider API.',
                'layout': 'Extract to a dedicated directory; paths are relative to its manuscript snapshot root. Not a complete typeset article checkout.',
                'modules': modules,
                'coordination': {'phase': board['phase'],
                                 'repository': board['public_repository'],
                                 'project': 1, 'package': 'B001', 'contract_revision': 1,
                                 'protocol_version': board['protocol_version'],
                                 'allocation_authority': board.get('allocation_authority')},
                'files': [{'path': path, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
                          for path, data in files.items()],
                'verification': ['python tools/build_formalization_handoff.py --verify .'] +
                                [f'python tools/build_formalization_module.py --module {m} --check' for m in MODULES] +
                                ['python ' + json.loads((root / 'formalization' / m / 'module.json').read_text()).get('control_script', 'tools/check_raw_exact_controls.py') for m in MODULES] +
                                ['python tools/check_formalization_coordination.py --check'],
                'external_providers': [dict(module=m['id'], **item) for m in modules
                                       for item in m['external_providers']],
                'unexpanded_upstream': [dict(module=m['id'], **item) for m in modules
                                       for item in m['imports']
                                       if item['status'] == 'EXPLICIT_UPSTREAM_NOT_EXPANDED']}
    return files, manifest


def archive_bytes(files, manifest):
    entries = {**files, MANIFEST: (json.dumps(manifest, ensure_ascii=False, indent=2)+'\n').encode()}
    result = io.BytesIO()
    with gzip.GzipFile(fileobj=result, mode='wb', filename='', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for path, data in sorted(entries.items()):
                info = tarfile.TarInfo(path)
                info.size = len(data)
                info.mode = 0o644
                info.uid = info.gid = info.mtime = 0
                info.uname = info.gname = ''
                archive.addfile(info, io.BytesIO(data))
    return result.getvalue()


def verify(root):
    manifest = json.loads((root / MANIFEST).read_text())
    if manifest.get('format_version') != 1:
        raise ValueError('Unsupported handoff manifest')
    seen = set()
    for item in manifest['files']:
        path = PurePosixPath(item['path'])
        if path.is_absolute() or '..' in path.parts or str(path) in seen or str(path) == MANIFEST:
            raise ValueError('Invalid or duplicate manifest path')
        seen.add(str(path))
        target = root / str(path)
        if target.is_symlink() or not target.is_file() or root.resolve() not in target.resolve().parents:
            raise ValueError(f'Unsafe or absent manifest file: {path}')
        data = target.read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            raise ValueError(f'Handoff file changed: {path}')
    return len(seen), manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--output', type=Path)
    action.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify is not None:
        count, manifest = verify(args.verify)
        print(f"Verified {count} snapshot files for {len(manifest['modules'])} preparation modules; no Lean certification.")
    else:
        files, manifest = collect(ROOT)
        data = archive_bytes(files, manifest)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(data)
        print(json.dumps({'path': str(args.output.resolve()), 'bytes': len(data),
                          'sha256': hashlib.sha256(data).hexdigest(), 'snapshot_files': len(files),
                          'modules': list(MODULES), 'unexpanded_upstream': len(manifest['unexpanded_upstream'])}))


if __name__ == '__main__':
    main()
