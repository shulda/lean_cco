#!/usr/bin/env python3
"""Repair inconsistent CCO outputs before incremental builds and external audits.

Lake validates matching input traces and output existence, so an inconsistent
manual snapshot can leave stale legacy oleans. Verify bytes against each
trace's output descriptors, source inputs, and actual compiled import headers.
The post-build check also requires the complete current source closure.
"""
from __future__ import annotations

import argparse
from collections.abc import Iterable
import json
from pathlib import Path
import re
import subprocess

from clear_project_cache import clear_project_artifacts

DESCRIPTOR = re.compile(r'([0-9a-f]{16})\.(olean(?:\.(?:server|private))?)\Z')


def inspect_metadata(build: Path, source_traces: Iterable[Path] = ()) -> tuple[dict[Path, str], set[Path]]:
    lib = build / 'lib/lean'
    # rglob deliberately does not follow directory symlinks. Include exact
    # paths from the finite canonical source closure, avoiding both omissions
    # behind aliases and unbounded recursive traversal through symlink loops.
    traces = set((lib / 'CCO').rglob('*.trace'))
    traces.update(trace for trace in source_traces if trace.is_file())
    if (lib / 'CCO.trace').is_file():
        traces.add(lib / 'CCO.trace')
    expected: dict[Path, str] = {}
    invalid: set[Path] = set()
    for trace in sorted(traces):
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


def source_trace_hash(trace: Path, relative: Path) -> str | None:
    """Find the source input even after an archive moves between worktrees."""
    try:
        inputs = json.loads(trace.read_text(encoding='utf-8'))['inputs']
        matches = [value for caption, value in inputs
                   if isinstance(caption, str)
                   and (caption == relative.as_posix()
                        or caption.endswith('/' + relative.as_posix()))]
        return matches[0] if len(matches) == 1 and isinstance(matches[0], str) else None
    except (OSError, ValueError, KeyError, TypeError):
        return None


def mismatched_sources(project: Path, build: Path, metadata: list[dict],
                       require_complete: bool = False) -> dict[Path, str]:
    """Reject stale source inputs and semantically stale compiled import closure."""
    invalid: dict[Path, str] = {}
    for entry in metadata:
        source = Path(entry['source'])
        relative = source.relative_to(project)
        trace = (build / 'lib/lean' / relative).with_suffix('.trace')
        compiled = entry['compiledImports']
        # A cold pre-build cache has nothing to repair. A post-build audit
        # must have every source-reachable project module materialized.
        if (compiled is None and entry['readError'] is None
                and not trace.exists() and not require_complete):
            continue
        if compiled is None:
            invalid[trace] = 'missing/unreadable compiled module'
        elif entry['readError'] is not None:
            invalid[trace] = 'unreadable compiled header'
        elif (entry['resolvedOlean'] is None
              or Path(entry['resolvedOlean']).resolve() != trace.with_suffix('.olean').resolve()):
            invalid[trace] = 'audit search path resolves a different compiled module'
        elif (compiled != entry['imports']
              or entry['compiledIsModule'] != entry['isModule']):
            invalid[trace] = 'compiled imports differ from current source header'
        elif source_trace_hash(trace, relative) != entry['sourceHash']:
            invalid[trace] = 'source input hash differs from current source'
    return invalid


def invalidate(build: Path, traces: set[Path]) -> list[Path]:
    # Deleting a file beneath a directory alias would mutate its external
    # target. Drop only our generated namespace trees instead; rmtree does
    # not traverse directory symlinks and valid external artifacts survive.
    lib = build / 'lib/lean'
    for trace in traces:
        relative = trace.with_suffix('').relative_to(lib)
        parents = (trace.parent, (build / 'ir' / relative).parent)
        if any(parent.resolve() != parent for parent in parents):
            return clear_project_artifacts(build)
    removed: list[Path] = []
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
    parser.add_argument('--project', type=Path, default=Path.cwd())
    parser.add_argument('--require-complete', action='store_true',
                        help='require every current source-reachable CCO module after build')
    args = parser.parse_args()
    build = args.build_dir.resolve()
    project = args.project.resolve()
    helper = Path(__file__).with_name('project_cache_metadata.lean').resolve()
    process = subprocess.run(['lake', 'env', 'lean', '--run', str(helper),
                              str(project), str(build)], text=True, capture_output=True)
    if process.returncode:
        parser.error('pinned source/compiled import check failed:\n' + process.stderr + process.stdout)
    try:
        metadata = json.loads(process.stdout)
        source_errors = mismatched_sources(project, build, metadata, args.require_complete)
        source_traces = [(build / 'lib/lean' / Path(entry['source']).relative_to(project))
                         .with_suffix('.trace') for entry in metadata]
    except (ValueError, TypeError, KeyError) as exc:
        parser.error('invalid source/compiled import metadata: ' + str(exc))
    expected, invalid = inspect_metadata(build, source_traces)
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
    invalid |= set(source_errors)
    if invalid:
        for trace in sorted(invalid):
            print('Inconsistent project cache:', trace.relative_to(build),
                  source_errors.get(trace, 'output bytes differ from trace descriptors'))
        if not args.repair:
            raise SystemExit(1)
        removed = invalidate(build, invalid)
        if any(path.exists() or path.is_symlink() for path in removed):
            parser.error('invalidated outputs are still present; refusing incremental rebuild')
        print(f'Invalidated {len(invalid)} module(s), {len(removed)} generated output(s).')
    else:
        print(f'Project cache consistent: {len(expected)} olean part(s), '
              f'{len(metadata)} current source module(s) checked.')


if __name__ == '__main__':
    main()
