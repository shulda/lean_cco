#!/usr/bin/env python3
"""Verify source identity and every current-source compiled Ramsey artifact."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

from external_provider import require
from ramsey_provider import NAMESPACES, cache_key, materialized_provider
from verify_project_cache import inspect_metadata, mismatched_modules, mismatched_sources


def run_json(command: list[str], project: Path):
    result = subprocess.run(command, cwd=project, text=True, capture_output=True)
    require(result.returncode == 0, 'Ramsey provider metadata/hash check failed:\n' + result.stderr + result.stdout)
    return json.loads(result.stdout)


def clear_provider_outputs(provider: Path, build: Path) -> None:
    require(provider.resolve() == provider.absolute()
            and build.resolve() == (provider / '.lake/build').absolute(),
            'Refusing to invalidate an aliased/shared Ramsey build')
    for directory in (build / 'lib/lean', build / 'ir'):
        require(directory.resolve() == directory.absolute(), 'Aliased Ramsey artifact parent')
    for directory in (build / 'lib/lean', build / 'ir'):
        for namespace in NAMESPACES:
            tree = directory / namespace
            if tree.is_symlink():
                tree.unlink()
            elif tree.exists():
                shutil.rmtree(tree)
            for path in directory.glob(namespace + '.*'):
                if path.is_file() or path.is_symlink():
                    path.unlink()


def verify(project: Path, require_complete: bool, repair: bool = False) -> dict:
    config, provider = materialized_provider(project)
    build = provider / '.lake/build'
    tools = project / 'tools'
    metadata = run_json(['lake', 'env', 'lean', '--run', str(tools / 'ramsey_provider_metadata.lean'),
                         str(provider), str(build), config['module']], project)
    require(len(metadata) == config['source_modules'], 'Ramsey current source-closure count changed')
    errors = mismatched_sources(provider, build, metadata, require_complete)
    traces = [(build / 'lib/lean' / Path(entry['source']).relative_to(provider)).with_suffix('.trace')
              for entry in metadata]
    expected, invalid = inspect_metadata(build, traces)
    existing = [str(path) for path in expected if path.is_file()]
    actual = {}
    if existing:
        actual = {Path(path): value for path, value in run_json(
            ['lake', 'env', 'lean', '--run', str(tools / 'project_cache_hashes.lean'), *existing], project)}
    invalid |= mismatched_modules(expected, actual)
    invalid |= set(errors)
    if invalid:
        if not repair:
            descriptions = [str(trace.relative_to(build)) + ': ' + errors.get(trace, 'artifact bytes/trace mismatch')
                            for trace in sorted(invalid)]
            raise ValueError('Inconsistent Ramsey provider cache:\n' + '\n'.join(descriptions))
        clear_provider_outputs(provider, build)
        print(f'Ramsey provider cache invalidated: {len(invalid)} inconsistent module(s); rebuild pinned facade.')
        return {'invalidated': len(invalid), 'modules': len(metadata), 'parts': 0}
    print(f'Ramsey provider cache consistent: {len(expected)} olean part(s), '
          f'{len(metadata)} current source module(s) checked; exact subtree {config["subtree"]}.')
    return {'invalidated': 0, 'modules': len(metadata), 'parts': len(expected)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--repair', action='store_true')
    parser.add_argument('--cache-key', action='store_true')
    parser.add_argument('--github-output', action='store_true')
    parser.add_argument('--os', default=platform.system())
    parser.add_argument('--arch', default=platform.machine())
    args = parser.parse_args()
    try:
        project = args.project.resolve()
        if args.cache_key:
            key, identity = cache_key(project, args.os, args.arch)
            if args.github_output:
                with Path(os.environ['GITHUB_OUTPUT']).open('a') as output:
                    output.write('key=' + key + '\n')
            print(key)
        else:
            verify(project, args.require_complete, args.repair)
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
