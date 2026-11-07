#!/usr/bin/env python3
"""Verify all fourteen source/compiled forest modules and licensed cache contents."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tomllib

from external_provider import require
from factorization_forest_provider import (DISTRIBUTION, NAMESPACE, cache_key,
    materialized_provider, prepare_distribution, verify_distribution)
from verify_project_cache import inspect_metadata, mismatched_sources


def run_json(command: list[str], project: Path):
    result = subprocess.run(command, cwd=project, text=True, capture_output=True)
    require(result.returncode == 0, 'Forest metadata/hash check failed:\n' + result.stderr + result.stdout)
    return json.loads(result.stdout)


def clear_provider_outputs(project: Path) -> None:
    build = project / '.lake/build'
    require(build.resolve() == build.absolute(), 'Refusing an aliased/shared forest build')
    parents = (build / 'lib/lean', build / 'ir', project / '.lake')
    require(all(p.resolve() == p.absolute() for p in parents), 'Aliased forest artifact parent')
    # Delete only provider namespace outputs. All CCO/other dependency outputs
    # remain available; never follow a namespace alias into another build.
    for directory in parents[:2]:
        for path in [directory / NAMESPACE, *directory.glob(NAMESPACE + '.*')]:
            if path.is_symlink() or path.is_file():
                path.unlink()
            elif path.is_dir():
                shutil.rmtree(path)
    distribution = project / DISTRIBUTION
    if distribution.is_symlink() or distribution.is_file():
        distribution.unlink()
    elif distribution.is_dir():
        shutil.rmtree(distribution)


def inspect_forest_traces(build: Path, traces: list[Path], config: dict,
                          options: dict) -> tuple[dict[Path, str], dict[Path, str]]:
    """Bind traces to the receiving compiler/options and hash all Lean outputs.

    Lake's real trace schema records compiler and option captions. Check the
    native C/IR and editor artifacts too, since the dependency cache exports
    them along with every olean partition; ignore mutable hash sidecars.
    """
    def flags(values: dict, prefix: str = '') -> set[str]:
        result = set()
        for name, value in values.items():
            name = prefix + name
            if isinstance(value, dict):
                result |= flags(value, name + '.')
            else:
                text = str(value).lower() if isinstance(value, bool) else str(value)
                result.add('-D' + name + '=' + text)
        return result

    expected_flags = flags(options)
    expected: dict[Path, str] = {}
    errors: dict[Path, str] = {}
    for trace in traces:
        if not trace.is_file():
            continue  # Cold caches are handled by the normal completeness check.
        try:
            data = json.loads(trace.read_text())
            inputs = data['inputs']
            captions = [caption for caption, _ in inputs]
            require(config['compiler_trace'] in captions
                    and sum(c.startswith('Lean ') for c in captions) == 1,
                    'compiled trace compiler pin changed')
            module = '.'.join(trace.relative_to(build / 'lib/lean').with_suffix('').parts)
            require('Module.name: ' + module in captions and 'Package.id?: (some CCO)' in captions
                    and 'Module.leanArgs: #[]' in captions,
                    'compiled trace module/package/compiler arguments changed')
            option_entries = [value for caption, value in inputs if caption == 'options']
            require(len(option_entries) == 1 and len(option_entries[0]) == len(expected_flags)
                    and {caption for caption, _ in option_entries[0]} == expected_flags,
                    'compiled trace original compiler options changed')
            require(data.get('synthetic') is False and data.get('schemaVersion') == '2025-09-10',
                    'unsupported/synthetic forest trace')
            for key, suffix in (('i', 'ilean'), ('r', 'ir'), ('rs', 'ir.sig'), ('c', 'c')):
                descriptor = data['outputs'][key]
                match = re.fullmatch(r'([0-9a-f]{16})\.' + re.escape(suffix), descriptor)
                require(match is not None, 'missing/unsupported forest output descriptor')
                if suffix == 'c':
                    path = (build / 'ir' / trace.relative_to(build / 'lib/lean')).with_suffix('.c')
                else:
                    path = trace.with_suffix('.' + suffix)
                expected[path] = match[1]
                require(path.is_file(), 'missing forest C/IR/editor output')
        except (OSError, ValueError, KeyError, TypeError) as error:
            errors[trace] = str(error)
    return expected, errors


def verify(project: Path, require_complete: bool, repair: bool = False) -> dict:
    config, provider = materialized_provider(project)
    build = project / '.lake/build'
    tools = project / 'tools'
    metadata = run_json(['lake', 'env', 'lean', '--run', str(tools / 'project_cache_metadata.lean'),
                         str(provider), str(build), config['module']], project)
    inventory = json.loads((provider / 'PROVENANCE.json').read_text())['files']
    require({entry['source'] for entry in metadata} == {str(provider / entry['path']) for entry in inventory}
            and len(metadata) == config['source_modules'], 'Forest compiled source-closure changed')
    errors = mismatched_sources(provider, build, metadata, require_complete)
    traces = [(build / 'lib/lean' / Path(entry['source']).relative_to(provider)).with_suffix('.trace')
              for entry in metadata]
    expected, invalid = inspect_metadata(build, traces, namespaces=(NAMESPACE,))
    extra_outputs, trace_errors = inspect_forest_traces(
        build, traces, config, tomllib.loads((provider / 'lakefile.toml').read_text())['leanOptions'])
    expected.update(extra_outputs)
    errors.update(trace_errors)
    # A cache may not smuggle another upstream module outside the licensed
    # and audited finite closure, even if that module is not imported by Tree.
    known = {trace.with_suffix('.olean') for trace in traces}
    extra = set((build / 'lib/lean' / NAMESPACE).rglob('*.olean')) - known
    for output in extra:
        errors[output.with_suffix('.trace')] = 'compiled module outside the pinned fourteen-file closure'
    for path in [*expected, *traces]:
        if (path.exists() or path.is_symlink()) and path.resolve() != path.absolute():
            relative = path.relative_to(build / ('ir' if path.suffix == '.c' else 'lib/lean'))
            module = relative.name.split('.')[0]
            errors[build / 'lib/lean' / relative.parent / (module + '.trace')] = 'aliased forest artifact'
    existing = [str(path) for path in expected if path.is_file()]
    actual = {}
    if existing:
        actual = {Path(path): value for path, value in run_json(
            ['lake', 'env', 'lean', '--run', str(tools / 'project_cache_hashes.lean'), *existing], project)}
    for path, wanted in expected.items():
        if actual.get(path) != wanted:
            relative = path.relative_to(build / ('ir' if path.suffix == '.c' else 'lib/lean'))
            module = relative.name.split('.')[0]
            invalid.add(build / 'lib/lean' / relative.parent / (module + '.trace'))
    invalid |= set(errors)
    distribution_error = None
    if require_complete or expected or (project / DISTRIBUTION).exists() or (project / DISTRIBUTION).is_symlink():
        try:
            verify_distribution(project)
        except ValueError as error:
            distribution_error = str(error)
    if invalid or distribution_error:
        descriptions = [str(trace.relative_to(build)) + ': ' + errors.get(trace, 'artifact bytes/trace mismatch')
                        for trace in sorted(invalid)]
        if distribution_error:
            descriptions.append(distribution_error)
        if not repair:
            raise ValueError('Inconsistent forest provider cache:\n' + '\n'.join(descriptions))
        clear_provider_outputs(project)
        print(f'Forest provider cache invalidated: {len(invalid)} inconsistent module(s); '
              f'license/provenance error: {distribution_error}; rebuild finite Tree closure.')
        return {'invalidated': len(invalid) + bool(distribution_error), 'modules': len(metadata), 'parts': 0}
    print(f'Forest provider cache consistent: {len(expected)} compiled output(s), '
          f'{len(metadata)} current source module(s); exact port subtree {config["subtree"]}.')
    return {'invalidated': 0, 'modules': len(metadata), 'parts': len(expected)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--repair', action='store_true')
    parser.add_argument('--cache-key', action='store_true')
    parser.add_argument('--prepare-distribution', action='store_true')
    parser.add_argument('--github-output', action='store_true')
    parser.add_argument('--os', default=platform.system())
    parser.add_argument('--arch', default=platform.machine())
    args = parser.parse_args()
    try:
        project = args.project.resolve()
        if args.cache_key:
            key, _ = cache_key(project, args.os, args.arch)
            if args.github_output:
                with Path(os.environ['GITHUB_OUTPUT']).open('a') as output:
                    output.write('key=' + key + '\n')
            print(key)
        elif args.prepare_distribution:
            prepare_distribution(project)
        else:
            verify(project, args.require_complete, args.repair)
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
