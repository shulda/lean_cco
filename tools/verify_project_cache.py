#!/usr/bin/env python3
"""Repair inconsistent CCO outputs before incremental builds and external audits.

Lake validates matching input traces and output existence, so an inconsistent
manual snapshot can leave stale legacy oleans. Verify bytes against each
trace's output descriptors, then invalidate only inconsistent modules.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

DESCRIPTOR = re.compile(r'([0-9a-f]{16})\.(olean(?:\.(?:server|private))?)\Z')


def inspect_metadata(build: Path) -> tuple[dict[Path, str], set[Path]]:
    lib = build / 'lib/lean'
    traces = sorted((lib / 'CCO').rglob('*.trace'))
    if (lib / 'CCO.trace').is_file():
        traces.append(lib / 'CCO.trace')
    expected: dict[Path, str] = {}
    invalid: set[Path] = set()
    for trace in traces:
        try:
            outputs = json.loads(trace.read_text(encoding='utf-8'))['outputs']['o']
            if not isinstance(outputs, list) or not outputs:
                raise ValueError('missing olean descriptors')
            for descriptor in outputs:
                match = DESCRIPTOR.fullmatch(descriptor)
                if match is None:
                    raise ValueError('unsupported olean descriptor')
                path = trace.with_suffix('.' + match[2])
                expected[path] = match[1]
                if not path.is_file():
                    invalid.add(trace)
        except (OSError, ValueError, KeyError, TypeError):
            invalid.add(trace)
    return expected, invalid


def mismatched_modules(expected: dict[Path, str], actual: dict[Path, str]) -> set[Path]:
    result: set[Path] = set()
    for path, wanted in expected.items():
        if actual.get(path) != wanted:
            # All olean partitions share the same module trace.
            suffix = path.name.index('.olean')
            result.add(path.with_name(path.name[:suffix] + '.trace'))
    return result


def invalidate(build: Path, traces: set[Path]) -> list[Path]:
    removed: list[Path] = []
    lib = build / 'lib/lean'
    for trace in sorted(traces):
        stem = trace.with_suffix('')
        relative = stem.relative_to(lib)
        for directory, name in ((stem.parent, stem.name),
                                ((build / 'ir' / relative).parent, relative.name)):
            for artifact in sorted(directory.glob(name + '.*')):
                if artifact.is_file() or artifact.is_symlink():
                    artifact.unlink()
                    removed.append(artifact)
    return removed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path, default=Path('.lake/build'))
    parser.add_argument('--repair', action='store_true')
    args = parser.parse_args()
    build = args.build_dir.resolve()
    expected, invalid = inspect_metadata(build)
    existing = [str(path) for path in expected if path.is_file()]
    actual: dict[Path, str] = {}
    if existing:
        helper = Path(__file__).with_name('project_cache_hashes.lean').resolve()
        process = subprocess.run(['lake', 'env', 'lean', '--run', str(helper), *existing],
                                 text=True, capture_output=True)
        if process.returncode:
            parser.error('pinned Lake output hash check failed:\n' + process.stderr + process.stdout)
        try:
            actual = {Path(path): value for path, value in json.loads(process.stdout)}
        except (ValueError, TypeError) as exc:
            parser.error('invalid pinned Lake hash output: ' + str(exc))
    invalid |= mismatched_modules(expected, actual)
    if invalid:
        for trace in sorted(invalid):
            print('Inconsistent project cache:', trace.relative_to(build))
        if not args.repair:
            raise SystemExit(1)
        removed = invalidate(build, invalid)
        print(f'Invalidated {len(invalid)} module(s), {len(removed)} generated output(s).')
    else:
        print(f'Project cache consistent: {len(expected)} olean part(s) checked.')


if __name__ == '__main__':
    main()
