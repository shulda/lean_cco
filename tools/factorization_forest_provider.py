"""Exact finite Tree closure, receiving options and licensed binary distribution.

The provider is a lean_lib in the receiving package, not a new Lake dependency.
Its cache identity excludes the changing CCO commit.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import tomllib

from external_provider import INPUTS, git, require, sha256

NAMESPACE = 'AlgebraicAutomata'
DISTRIBUTION = '.lake/factorization-forest-distribution'
GUARDS = ('factorization_forest_provider.py', 'verify_factorization_forest_provider.py',
          'project_cache_metadata.lean', 'project_cache_hashes.lean',
          'verify_project_cache.py', 'external_provider.py', 'mathlib_cache_roots.py')


def specification(project: Path) -> dict:
    config = json.loads((project / 'tools/factorization_forest_provider.json').read_text())
    require(config.get('schema_version') == 1 and config.get('library') == NAMESPACE
            and config.get('directory') == 'vendor/factorization-forest'
            and config.get('module') == NAMESPACE + '.FactorizationForest.Tree'
            and config.get('source_modules') == 14 and config.get('audited_declarations') == 791,
            'Unsupported finite forest provider registration')
    require(all(re.fullmatch('[0-9a-f]{40}', config.get(k, '')) for k in ('commit', 'subtree')),
            'Forest provider needs exact upstream and port subtree pins')
    require(set(config.get('input_sha256', {})) == set(INPUTS),
            'Forest provider needs exact configuration hashes')
    require(len(config.get('receiving_dependencies', [])) == 11,
            'Forest provider must preserve all eleven receiving dependency entries')
    return config


def pinned_files(project: Path, config: dict) -> dict[str, str]:
    result = {}
    for line in git(project, 'ls-tree', '-r', config['subtree']).splitlines():
        descriptor, relative = line.split('\t', 1)
        mode, kind, blob = descriptor.split()
        require(kind == 'blob' and mode == '100644', 'Unsupported forest source tree entry')
        result[relative] = blob
    require(bool(result), 'Empty forest source tree')
    return result


def check_files(directory: Path, expected: dict[str, str], label: str) -> None:
    for relative, blob in expected.items():
        path = directory / relative
        require(path.is_file() and path.resolve() == path.absolute(),
                'Missing/aliased ' + label + ': ' + relative)
        content = path.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        require(actual == blob, label + ' differs from pinned Git blob: ' + relative)


def materialized_provider(project: Path) -> tuple[dict, Path]:
    config = specification(project)
    provider = project / config['directory']
    require(provider.is_dir() and provider.resolve() == provider.absolute(),
            'Forest source must be a private physical vendor directory')
    require(git(project, 'rev-parse', 'HEAD:' + config['directory']) == config['subtree'],
            'Forest provider Git subtree pin mismatch')
    expected = pinned_files(project, config)
    check_files(provider, expected, 'Forest source')
    expected_sources = {p for p in expected if p.endswith('.lean')}
    actual_sources = {p.relative_to(provider).as_posix() for p in provider.rglob('*.lean')
                      if '.lake' not in p.relative_to(provider).parts}
    require(expected_sources == actual_sources, 'Forest provider has extra/missing current source modules')
    require((project / 'lean-toolchain').read_bytes() == (provider / 'lean-toolchain').read_bytes(),
            'Forest provider toolchain differs from receiving project')
    require(all(sha256(provider / name) == config['input_sha256'][name] for name in INPUTS),
            'Forest provider configuration/toolchain/manifest changed')
    receiving = json.loads((project / 'lake-manifest.json').read_text())['packages']
    require(receiving == config['receiving_dependencies'], 'An existing receiving dependency entry changed')
    shared = json.loads((provider / 'lake-manifest.json').read_text())['packages']
    require(receiving[:9] == shared, 'Forest shared dependency entries changed')
    library = [entry for entry in tomllib.loads((project / 'lakefile.toml').read_text()).get('lean_lib', [])
               if entry.get('name') == NAMESPACE]
    options = tomllib.loads((provider / 'lakefile.toml').read_text())['leanOptions']
    require(library == [{'name': NAMESPACE, 'srcDir': config['directory'], 'roots': [config['module']],
                         'globs': [NAMESPACE + '.+'], 'leanOptions': options}],
            'Forest library source roots/compiler options changed')
    provenance = json.loads((provider / 'PROVENANCE.json').read_text())
    require(provenance['commit'] == config['commit'] and provenance['root_module'] == config['module'],
            'Forest original source pin changed')
    require(len(provenance['files']) == config['source_modules'], 'Forest source inventory count changed')
    # Follow actual current imports, rather than assuming that a list of
    # fourteen source hashes alone proves closure completeness.
    from mathlib_cache_roots import imports
    seen = set()
    pending = [config['module']]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = provider / (module.replace('.', '/') + '.lean')
        for imported in imports(source.read_text()):
            if imported.split('.')[0] == NAMESPACE:
                pending.append(imported)
    require(seen == {entry['module'] for entry in provenance['files']},
            'Actual finite forest import closure differs from pinned inventory')
    for entry in provenance['files']:
        source = provider / entry['path']
        require(sha256(source) == entry['ported_sha256'], 'Forest ported source hash changed')
        content = source.read_bytes()
        require(b'CCO compatibility port, 6 November 2026.' in content
                and b"Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved." in content,
                'Forest source is missing original/modification notices')
    require(sha256(provider / 'LICENSE') == provenance['license_sha256'], 'Forest full license changed')
    return config, provider


def distribution_files(project: Path) -> dict[str, str]:
    config, _ = materialized_provider(project)
    # The complete pinned provider distribution preserves the full license,
    # all original and per-file modification notices, provenance and patch.
    return pinned_files(project, config)


def verify_distribution(project: Path, directory: Path | None = None) -> None:
    directory = directory or project / DISTRIBUTION
    expected = distribution_files(project)
    require(directory.is_dir() and directory.resolve() == directory.absolute(),
            'Missing/aliased forest license and provenance distribution')
    check_files(directory, expected, 'Forest distribution')
    actual = {p.relative_to(directory).as_posix() for p in directory.rglob('*') if not p.is_dir()}
    require(actual == set(expected), 'Forest distribution has extra/missing files')


def prepare_distribution(project: Path) -> None:
    config, provider = materialized_provider(project)
    directory = project / DISTRIBUTION
    require(directory.parent.resolve() == directory.parent.absolute() and not directory.is_symlink(),
            'Refusing to write aliased forest distribution')
    if directory.exists():
        # Never write through a nested alias in a restored distribution.
        shutil.rmtree(directory)
    for relative in pinned_files(project, config):
        destination = directory / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(provider / relative, destination)
    verify_distribution(project)


def cache_key(project: Path, operating_system: str, architecture: str) -> tuple[str, dict]:
    config, provider = materialized_provider(project)
    identity = {
        'schema_version': 1, 'upstream_commit': config['commit'], 'port_subtree': config['subtree'],
        'module': config['module'], 'platform': [operating_system, architecture],
        'receiving_inputs': {name: sha256(project / name) for name in INPUTS},
        'provider_inputs': {name: sha256(provider / name) for name in INPUTS},
        'registration_sha256': sha256(project / 'tools/factorization_forest_provider.json'),
        'guard_sha256': {name: sha256(project / 'tools' / name) for name in GUARDS},
    }
    digest = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return 'cco-forest-dependency-v1-' + digest, identity
