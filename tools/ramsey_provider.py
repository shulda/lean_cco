"""Exact-subtree identity of the vendored, Lean4.34.1 Ramsey provider.

This registration is separate from the unchanged exact-pinned EPPA provider.
The changing receiving CCO commit is deliberately not a dependency cache key.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from external_provider import git, require, sha256

INPUTS = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
NAMESPACES = ('CCORamsey', 'PartiteConstruction', 'SuccessorTree')


def specification(project: Path) -> dict:
    config = json.loads((project / 'tools/ramsey_provider.json').read_text())
    require(config.get('schema_version') == 1 and config.get('package') == 'CCORamsey'
            and config.get('directory') == 'vendor/ramsey'
            and config.get('module') == 'CCORamsey'
            and config.get('namespaces') == list(NAMESPACES), 'Unsupported Ramsey provider registration')
    require(re.fullmatch('[0-9a-f]{40}', config.get('subtree', '')) is not None,
            'Ramsey provider needs an exact Git subtree pin')
    require(config.get('source_modules') == 106, 'Ramsey facade source count changed')
    require(set(config.get('input_sha256', {})) == set(INPUTS),
            'Ramsey provider needs exact configuration hashes')
    require(len(config.get('receiving_dependencies', [])) == 10
            and len(config.get('shared_dependencies', [])) == 9,
            'The ten receiving and nine shared dependency entries must be preserved')
    return config


def materialized_provider(project: Path) -> tuple[dict, Path]:
    config = specification(project)
    provider = project / config['directory']
    require(provider.is_dir() and provider.resolve() == provider.absolute(),
            'Ramsey source must be a private physical vendor directory')
    actual_tree = git(project, 'rev-parse', 'HEAD:' + config['directory'])
    require(actual_tree == config['subtree'], 'Ramsey provider Git subtree pin mismatch')
    # Check bytes against Git blobs, even if assume-unchanged/index flags hide edits.
    expected = {}
    for line in git(project, 'ls-tree', '-r', config['subtree']).splitlines():
        descriptor, relative = line.split('\t', 1)
        mode, kind, blob = descriptor.split()
        require(kind == 'blob' and mode == '100644', 'Unsupported Ramsey source tree entry')
        path = provider / relative
        require(path.is_file() and not path.is_symlink(), 'Missing/aliased Ramsey source: ' + relative)
        content = path.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        require(actual == blob, 'Ramsey source differs from pinned Git blob: ' + relative)
        expected[relative] = blob
    expected_sources = {p for p in expected if p.endswith('.lean')}
    actual_sources = {p.relative_to(provider).as_posix() for p in provider.rglob('*.lean')}
    require(expected_sources == actual_sources and len(expected_sources) == config['source_modules'],
            'Ramsey provider has extra/missing current source modules')
    require((project / 'lean-toolchain').read_bytes() == (provider / 'lean-toolchain').read_bytes(),
            'Ramsey provider toolchain differs from receiving project')
    require(all(sha256(provider / name) == config['input_sha256'][name] for name in INPUTS),
            'Ramsey provider configuration/toolchain/manifest changed')
    entries = json.loads((project / 'lake-manifest.json').read_text())['packages']
    require(len({p['name'] for p in entries}) == len(entries), 'Duplicate receiving package')
    entry = [p for p in entries if p['name'] == config['package']]
    require(entry == [config['path_entry']], 'Receiving manifest does not bind the registered Ramsey path')
    require([p for p in entries if p['name'] != config['package']] == config['receiving_dependencies'],
            'An existing receiving dependency entry changed')
    upstream = json.loads((provider / 'lake-manifest.json').read_text())['packages']
    require(upstream == config['shared_dependencies'], 'Ramsey shared dependency entries changed')
    return config, provider


def cache_key(project: Path, operating_system: str, architecture: str) -> tuple[str, dict]:
    config, provider = materialized_provider(project)
    identity = {
        'schema_version': 1, 'provider_subtree': config['subtree'],
        'module': config['module'], 'platform': [operating_system, architecture],
        'receiving_inputs': {name: sha256(project / name) for name in INPUTS},
        'provider_inputs': {name: sha256(provider / name) for name in INPUTS},
        'registration_sha256': sha256(project / 'tools/ramsey_provider.json'),
        'guard_sha256': {name: sha256(project / 'tools' / name) for name in
                         ('ramsey_provider.py', 'verify_ramsey_provider.py', 'ramsey_provider_metadata.lean')},
    }
    digest = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return 'cco-ramsey-dependency-v1-' + digest, identity
