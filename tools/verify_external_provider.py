#!/usr/bin/env python3
"""Verify the exact source and compiled artifacts of the pinned EPPA facade.

The CCO guard remains separate. This tool deliberately uses a distinct output
prefix; provider counts must not be mistaken for CCO source-closure evidence.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

from external_provider import cache_key, check_source_blobs, materialized_provider, require
from verify_project_cache import inspect_metadata, mismatched_modules, mismatched_sources


def run_json(command: list[str], project: Path):
    result = subprocess.run(command, cwd=project, text=True, capture_output=True)
    require(result.returncode == 0, 'Pinned provider metadata/hash check failed:\n' + result.stderr + result.stdout)
    return json.loads(result.stdout)


def clear_provider_outputs(project: Path, build: Path, namespace: str) -> None:
    package = project / '.lake/packages' / namespace
    require(package.resolve() == package.absolute()
            and (package / '.lake/build').resolve() == (package / '.lake/build').absolute(),
            'Refusing to invalidate a shared/aliased provider build')
    for directory in (build / 'lib/lean', build / 'ir'):
        require(directory.resolve() == directory.absolute(), 'Refusing an aliased provider artifact parent')
    for directory in (build / 'lib/lean', build / 'ir'):
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
    build = (provider / '.lake/build').resolve()
    tools = project / 'tools'
    metadata = run_json(['lake', 'env', 'lean', '--run', str(tools / 'project_cache_metadata.lean'),
                         str(provider), str(build), config['module']], project)
    require(len(metadata) == config['source_modules'], 'Provider current source-closure count changed')
    check_source_blobs(provider, [Path(entry['source']) for entry in metadata])
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
            raise ValueError('Inconsistent external provider cache:\n' + '\n'.join(descriptions))
        clear_provider_outputs(project, build, config['namespace'])
        print(f'External provider cache invalidated: {len(invalid)} inconsistent module(s); rebuild pinned facade.')
        return {'invalidated': len(invalid), 'modules': len(metadata), 'parts': 0}
    print(f'External provider cache consistent: {len(expected)} olean part(s), '
          f'{len(metadata)} current source module(s) checked; exact pin {config["commit"]}.')
    return {'invalidated': 0, 'modules': len(metadata), 'parts': len(expected)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--repair', action='store_true')
    parser.add_argument('--cache-key', action='store_true', help='check pin/configuration and print dependency cache key only')
    parser.add_argument('--github-output', action='store_true', help='append the checked key to GITHUB_OUTPUT')
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
