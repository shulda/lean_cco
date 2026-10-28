#!/usr/bin/env python3
"""Find external cache roots by following the project's actual Lean imports.

Mathlib's pinned cache parser ignores CCO edges while computing transitive
imports. Passing only CCO.lean therefore cannot discover these roots.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

# Namespaces accepted by Cache.IO.isPartOfMathlibCache at the manifest pin.
CACHE_NAMESPACES = frozenset({
    'Mathlib', 'Batteries', 'BatteriesRecycling', 'Aesop', 'Cli',
    'ImportGraph', 'LeanSearchClient', 'Plausible', 'Qq', 'ProofWidgets',
    'Archive', 'Counterexamples', 'Wanted', 'MathlibTest', 'Requests',
    'OpenAIClient', 'Reap', 'Canonical', 'Duper', 'Auto', 'PremiseSelection',
    'Hammer',
})


def uncomment(source: str) -> str:
    """Remove nested Lean block and line comments, preserving line breaks."""
    out: list[str] = []
    depth = 0
    pos = 0
    while pos < len(source):
        pair = source[pos:pos + 2]
        if pair == '/-':
            depth += 1
            out.extend('  ')
            pos += 2
        elif depth and pair == '-/':
            depth -= 1
            out.extend('  ')
            pos += 2
        elif not depth and pair == '--':
            end = source.find('\n', pos)
            if end == -1:
                break
            out.extend(' ' * (end - pos))
            pos = end
        else:
            out.append(source[pos] if not depth or source[pos] == '\n' else ' ')
            pos += 1
    if depth:
        raise ValueError('unterminated Lean block comment')
    return ''.join(out)


def imports(source: str) -> list[str]:
    result: list[str] = []
    # CCO imports are header commands, one or several module names per line.
    # Stop at the first non-header command to avoid interpreting examples.
    for line in uncomment(source).splitlines():
        line = line.strip()
        if not line or line.startswith('module') or line == 'prelude':
            continue
        match = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if not match:
            break
        names = match.group(1).split()
        if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', n) for n in names):
            raise ValueError(f'unsupported import syntax: {line}')
        result.extend(names)
    return result


def cache_roots(project: Path, root: str = 'CCO') -> tuple[list[str], list[str]]:
    visited: set[str] = set()
    external: set[str] = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        path = project.joinpath(*module.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError(f'missing project module {module}: {path}')
        for imported in imports(path.read_text(encoding='utf-8')):
            namespace = imported.split('.')[0]
            if namespace == 'CCO':
                pending.append(imported)
            elif namespace in CACHE_NAMESPACES:
                external.add(imported)
            elif namespace not in {'Init', 'Lean', 'Std'}:
                raise ValueError(f'unrecognized external import {imported} in {path}')
    return sorted(external), sorted(visited)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--root', default='CCO')
    parser.add_argument('--json', action='store_true')
    parser.add_argument('--reject-broad', action='store_true')
    args = parser.parse_args()
    try:
        roots, modules = cache_roots(args.project, args.root)
        if args.reject_broad and {'Mathlib', 'Mathlib.Tactic'} & set(roots):
            raise ValueError('broad Mathlib import in project closure')
        if not roots:
            raise ValueError('no external cache roots discovered')
    except ValueError as exc:
        parser.error(str(exc))
    if args.json:
        print(json.dumps({'roots': roots, 'project_modules': modules}, indent=2))
    else:
        print('\n'.join(roots))


if __name__ == '__main__':
    main()
