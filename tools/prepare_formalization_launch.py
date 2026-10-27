#!/usr/bin/env python3
"""Stage a repository-bound handoff locally; never upload or create Lean files."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import build_formalization_handoff as handoff
import check_formalization_coordination as coordination


def prepare(root, destination, repository):
    if not coordination.valid_repository(repository):
        raise ValueError('Expected a public repository in owner/name form')
    files, manifest = handoff.collect(root)
    board_path = str(coordination.DIRECTORY / 'BOARD.json')
    board = json.loads(files[board_path])
    if board['phase'] != 'PREPARATION':
        raise ValueError('Launch already bound; review rather than silently rebind')
    board['phase'] = 'READY'
    board['public_repository'] = repository
    for project in board['projects']:
        if project['id'] == 1:
            project['state'] = 'ACTIVE'
    for package in board['packages']:
        if package['id'] == 'B001':
            package['state'] = 'ASSIGNED'
    files[board_path] = (json.dumps(board, ensure_ascii=False, indent=2)+'\n').encode()
    for path, content in coordination.generated(board).items():
        files[path] = content.encode()
    report = str(coordination.DIRECTORY / 'reports/1.md')
    files[report] = files[report].replace(
        b'not yet bound; this is preparation only.', repository.encode()+b'; staged for initial assignment.')
    files['README.md'] = f'''# CCO formalization — launch snapshot

Destination: https://github.com/{repository}; receiving Project 1, package B001.
Read `formalization/coordination/README.md`, `PROTOCOL.md` and `BOARD.json` in
that directory. This snapshot supplies mathematical preparation and work
orders. Project 1 implements the mathematical API; the coordinator may supply
an initial Lean/CI scaffold for it to validate and extend. The manuscript
preparation repository itself contains no Lean implementation.
For resuming the coordinating preparation project, read
`formalization/coordination/COORDINATOR_RUNBOOK.md`.

Before implementation run the Python preflight listed in `HANDOFF_MANIFEST.json`.
The board is staged as READY; this does not attest to GitHub publication,
permissions, a Lean build or a proof. Source files are a focused pinned
snapshot, not a complete compilable human article.

The full hash manifest records the initial snapshot. Verify it before the
first edits; later legitimate board/report/README changes need not match
those initial hashes. Ongoing validation uses module source pins, the
coordination checker and the actual Lean build. Never replace a running
repository with a newly staged initial snapshot.
'''.encode()
    manifest['coordination'] = {'phase': 'READY', 'repository': repository,
                                'project': 1, 'package': 'B001', 'contract_revision': 1}
    manifest['verification'] = [command + ' --require-launch'
                               if command == 'python tools/check_formalization_coordination.py --check'
                               else command for command in manifest['verification']]
    manifest['files'] = [{'path': p, 'bytes': len(data),
                          'sha256': hashlib.sha256(data).hexdigest()}
                         for p, data in sorted(files.items())]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.mkdir(exist_ok=False)
    for path, data in sorted(files.items()):
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    (destination / handoff.MANIFEST).write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
    coordination.validate(destination, board, require_launch=True)
    handoff.verify(destination)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    manifest = prepare(handoff.ROOT, args.output, args.repository)
    print(json.dumps({'directory': str(args.output.resolve()),
                      'repository': args.repository,
                      'snapshot_files': len(manifest['files']),
                      'published': False, 'lean_implemented': False}))


if __name__ == '__main__':
    main()
