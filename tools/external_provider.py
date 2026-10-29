"""The single reviewed, exact-pinned external EPPA package registration."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

INPUTS = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(provider: Path, *args: str) -> str:
    process = subprocess.run(['git', *args], cwd=provider, text=True, capture_output=True)
    require(process.returncode == 0, 'Cannot inspect pinned provider checkout: ' + process.stderr.strip())
    return process.stdout.strip()


def specification(project: Path) -> dict:
    path = project / 'tools/external_provider.json'
    require(path.is_file(), 'Missing explicit external provider registration')
    config = json.loads(path.read_text())
    require(config.get('schema_version') == 1 and config.get('package') == 'AllThoseEPPA'
            and config.get('namespace') == 'AllThoseEPPA'
            and config.get('module') == 'AllThoseEPPA.MainTheorems', 'Unsupported external provider registration')
    require(all(re.fullmatch('[0-9a-f]{40}', config.get(k, '')) for k in ('commit', 'tree')),
            'External provider needs exact source commit and tree pins')
    require(type(config.get('source_modules')) is int and config['source_modules'] > 0,
            'Missing provider source-closure count')
    require(set(config.get('input_sha256', {})) == set(INPUTS)
            and all(re.fullmatch('[0-9a-f]{64}', h) for h in config['input_sha256'].values()),
            'Missing exact provider configuration hashes')
    dependencies = config.get('dependencies', [])
    require(len(dependencies) == 9 and len({p['name'] for p in dependencies}) == 9,
            'Provider must retain the nine reviewed dependency pins')
    return config


def materialized_provider(project: Path) -> tuple[dict, Path]:
    """Check source identity/configuration before reading or trusting artifacts."""
    config = specification(project)
    package = project / '.lake/packages' / config['package']
    require(package.is_dir(), 'Materialize the pinned AllThoseEPPA package before external import traversal')
    provider = package.resolve()
    require(git(provider, 'rev-parse', 'HEAD') == config['commit'], 'External provider commit mismatch')
    require(git(provider, 'rev-parse', 'HEAD^{tree}') == config['tree'], 'External provider tree mismatch')
    require(not git(provider, 'status', '--porcelain', '--untracked-files=no'), 'External provider tracked source changed')
    require(all(sha256(provider / name) == config['input_sha256'][name] for name in INPUTS),
            'External provider configuration/toolchain/manifest changed')
    require((project / 'lean-toolchain').read_bytes() == (provider / 'lean-toolchain').read_bytes(),
            'External provider toolchain is incompatible with this project')
    current = json.loads((project / 'lake-manifest.json').read_text())['packages']
    entries = {p['name']: p for p in current}
    require(len(entries) == len(current), 'Duplicate receiving manifest package')
    entry = entries.get(config['package'], {})
    require(entry.get('rev') == config['commit'] and entry.get('inputRev') == config['commit']
            and entry.get('url') == config['url'] and entry.get('type') == 'git',
            'Receiving manifest does not bind the exact external provider')
    upstream = json.loads((provider / 'lake-manifest.json').read_text())['packages']
    pins = lambda ps: {p['name']: (p['url'], p['rev']) for p in ps}
    expected = pins(config['dependencies'])
    require(pins(upstream) == expected, 'Registered provider dependency pins changed')
    require(all(name in entries and (entries[name]['url'], entries[name]['rev']) == pin
                for name, pin in expected.items()), 'Receiving project changed a shared dependency pin')
    return config, provider


def check_source_blobs(provider: Path, source_files: list[Path]) -> None:
    """Check actual source bytes against HEAD, even with assume-unchanged flags."""
    tree = git(provider, 'ls-tree', '-r', 'HEAD')
    expected = {}
    for line in tree.splitlines():
        descriptor, path = line.split('\t', 1)
        mode, kind, blob = descriptor.split()
        if kind == 'blob':
            expected[path] = blob
    for source in source_files:
        relative = source.relative_to(provider).as_posix()
        content = source.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        require(expected.get(relative) == actual, 'Provider source differs from pinned Git blob: ' + relative)


def cache_key(project: Path, operating_system: str, architecture: str) -> tuple[str, dict]:
    config, provider = materialized_provider(project)
    identity = {
        'schema_version': 1, 'provider_commit': config['commit'], 'provider_tree': config['tree'],
        'module': config['module'], 'platform': [operating_system, architecture],
        'receiving_inputs': {name: sha256(project / name) for name in INPUTS},
        'provider_inputs': {name: sha256(provider / name) for name in INPUTS},
        'registration_sha256': sha256(project / 'tools/external_provider.json'),
    }
    digest = hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return 'cco-eppa-dependency-v1-' + digest, identity
