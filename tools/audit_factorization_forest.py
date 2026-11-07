#!/usr/bin/env python3
"""Audit the exact pinned Tree import using the actual receiving audit CLI."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

from external_provider import require
from factorization_forest_provider import materialized_provider
from verify_factorization_forest_provider import verify

ALLOW = ['propext', 'Classical.choice', 'Quot.sound']


def audit(project: Path, executable: Path) -> dict:
    config, _ = materialized_provider(project)
    verify(project, require_complete=True)
    result = subprocess.run(['lake', 'env', str(executable), '--root', 'AlgebraicAutomata',
                             '--modules', config['module'], '--allow', ','.join(ALLOW), '--json'],
                            cwd=project, text=True, capture_output=True)
    require(result.returncode == 0, 'Forest axiom audit failed:\n' + result.stderr + result.stdout)
    report = json.loads(result.stdout)
    require(report.get('ok') is True and report.get('audited') == config['audited_declarations']
            and report.get('root') == 'AlgebraicAutomata' and report.get('allowed') == ALLOW
            and set(report.get('axiomsUsed', [])) <= set(ALLOW) and report.get('violations') == [],
            'Forest audit must cover all 791 defining-module declarations with the standard allowlist')
    directory = project / '.lake/audits'
    require(directory.resolve() == directory.absolute(), 'Aliased audit output directory')
    directory.mkdir(parents=True, exist_ok=True)
    output = directory / 'factorization-forest.json'
    require(not output.is_symlink(), 'Aliased audit output file')
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--audit', type=Path, required=True)
    args = parser.parse_args()
    try:
        audit(args.project.resolve(), args.audit.resolve())
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
