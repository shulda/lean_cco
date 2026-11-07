#!/usr/bin/env python3
"""Replay this finite provider using exact existing dependency builds read only.

All compiler/audit outputs are confined to this package's own .lake directory.
Ordinary isolated `lake build` is also available; this entry point avoids
rebuilding or writing a concurrently shared dependency package directory.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[1]
PROVIDER_ROOT = 'AlgebraicAutomata.FactorizationForest.Tree'
IMPORT = re.compile(r'^(?:public\s+)?import\s+([\w.]+)', re.M)


def replay(dependencies: Path, lean: Path, audit: Path | None) -> None:
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())

    def option_flags(options: dict, prefix: str = '') -> list[str]:
        flags: list[str] = []
        for key, value in options.items():
            name = prefix + key
            if isinstance(value, dict):
                flags.extend(option_flags(value, name + '.'))
            else:
                text = str(value).lower() if isinstance(value, bool) else str(value)
                flags.append(f'-D{name}={text}')
        return flags

    lean_options = option_flags(config.get('leanOptions', {}))
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if not version.startswith('Lean (version 4.34.1,'):
        raise RuntimeError(f'Wrong compiler: {version}')
    for package in manifest['packages']:
        path = dependencies / package['name']
        actual = subprocess.check_output(
            ['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise RuntimeError(f"Wrong dependency pin: {package['name']} {actual}")
    for source in provenance['files']:
        data = (ROOT / source['path']).read_bytes()
        if hashlib.sha256(data).hexdigest() != source['ported_sha256']:
            raise RuntimeError(f"Source differs from inventory: {source['path']}")
        if b'CCO compatibility port, 6 November 2026.' not in data:
            raise RuntimeError(f"Missing modification notice: {source['path']}")
        if b"Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved." not in data:
            raise RuntimeError(f"Missing original copyright: {source['path']}")
    build = ROOT / '.lake/build/lib/lean'
    paths = [build] + [dependencies / p['name'] / '.lake/build/lib/lean'
                       for p in manifest['packages']]
    env = os.environ.copy()
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    seen: set[str] = set()
    order: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace('.', '/') + '.lean')
        for imported in IMPORT.findall(source.read_text()):
            if imported.startswith('AlgebraicAutomata.'):
                visit(imported)
        order.append(module)

    visit(PROVIDER_ROOT)
    expected = {source['module'] for source in provenance['files']}
    if seen != expected:
        raise RuntimeError('Actual finite import closure differs from inventory')
    for module in order + ['Tests.Consumer']:
        relative = module.replace('.', '/')
        output = build / (relative + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f'COMPILING {module}', flush=True)
        subprocess.run([str(lean)] + lean_options + ['-o', str(output), relative + '.lean'],
                       cwd=ROOT, env=env, check=True)
        print(f'PASS {module}', flush=True)
    if audit is not None:
        result = subprocess.run([
            str(audit), '--root', 'AlgebraicAutomata', '--modules', PROVIDER_ROOT,
            '--allow', 'propext,Classical.choice,Quot.sound', '--json'],
            cwd=ROOT, env=env, text=True, capture_output=True)
        (ROOT / '.lake/provider-axiom-audit.json').write_text(result.stdout)
        print(result.stdout, end='', flush=True)
        if result.stderr:
            print(result.stderr, end='', flush=True)
        result.check_returncode()
    receipt = {
        'provider_commit': provenance['commit'], 'compiler': version,
        'lean_options': lean_options,
        'receiving_manifest_sha256': hashlib.sha256(
            (ROOT / 'lake-manifest.json').read_bytes()).hexdigest(),
        'source_modules': order, 'consumer': 'Tests.Consumer',
        'source_sha256': {p['path']: p['ported_sha256'] for p in provenance['files']},
        'dependency_builds_read_only': True,
        'status': 'isolated provider preparation; not a B058 adapter or accepted dependency',
    }
    (ROOT / '.lake/replay-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS finite provider replay and consumer; shared dependency builds read only.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-root', type=Path, required=True,
                        help='Existing exact receiving .lake/packages directory')
    parser.add_argument('--lean', type=Path, required=True,
                        help='Exact Lean 4.34.1 compiler executable')
    parser.add_argument('--audit', type=Path,
                        help='Receiving protocol axiom-audit executable')
    args = parser.parse_args()
    replay(args.dependency_root.resolve(), args.lean.resolve(),
           args.audit.resolve() if args.audit else None)


if __name__ == '__main__':
    main()
