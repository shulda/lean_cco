#!/usr/bin/env python3
"""Give one local CCO worktree isolated, pinned EPPA source/build outputs.

This is a local cache convenience, not a CI acceptance check. The immutable
runtime seed must already be built. Nine compatible dependencies are shared;
the provider's source checkout and generated outputs are private to this
worktree. Never put AllThoseEPPA in the shared dependency directory.
"""
from __future__ import annotations

import argparse
import fcntl
import json
from pathlib import Path
import shutil
import subprocess


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=path, text=True).strip()


def prepare(project: Path, seed: Path, shared: Path) -> Path:
    config = json.loads((project / 'tools/external_provider.json').read_text())
    name, pin = config['package'], config['commit']
    require = lambda condition, message: condition or (_ for _ in ()).throw(ValueError(message))
    require(git(seed, 'rev-parse', 'HEAD') == pin, 'Provider seed pin mismatch')
    require(git(seed, 'rev-parse', 'HEAD^{tree}') == config['tree'], 'Provider seed tree mismatch')
    require(not git(seed, 'status', '--porcelain', '--untracked-files=no'), 'Provider seed source changed')
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    entries = {p['name']: p for p in manifest['packages']}
    require(entries[name]['rev'] == pin and entries[name]['url'] == config['url'], 'Receiving provider manifest mismatch')
    for p in config['dependencies']:
        require(entries[p['name']]['rev'] == p['rev'] and entries[p['name']]['url'] == p['url'],
                'Receiving dependency pin differs: ' + p['name'])
        require(git(shared / p['name'], 'rev-parse', 'HEAD') == p['rev'],
                'Shared dependency source differs: ' + p['name'])
    require((project / 'lean-toolchain').read_bytes() == (seed / 'lean-toolchain').read_bytes(),
            'Toolchain mismatch')
    require(len(list((seed / '.lake/build/lib/lean' / name).rglob('*.olean'))) == config['source_modules'],
            'Provider seed does not contain the complete API closure')
    packages = project / '.lake/packages'
    packages.parent.mkdir(exist_ok=True)
    if packages.is_symlink():
        require(packages.resolve() == shared.resolve(), 'Unexpected existing package alias')
        packages.unlink()  # unlink ONLY this alias; never change its shared target
    packages.mkdir(exist_ok=True)
    for p in config['dependencies']:
        target = packages / p['name']
        if target.exists():
            require(target.resolve() == (shared / p['name']).resolve(), 'Different existing dependency: ' + p['name'])
        else:
            target.symlink_to(shared / p['name'], target_is_directory=True)
    provider = packages / name
    require(not provider.is_symlink(), 'Provider source/build must be private to this worktree')
    if provider.exists():
        require(git(provider, 'rev-parse', 'HEAD') == pin, 'Existing private provider pin mismatch')
        require(not git(provider, 'status', '--porcelain', '--untracked-files=no'), 'Private provider source changed')
    else:
        # All cooperating local worktree preparations use this advisory lock.
        # Git's repository-wide worktree metadata is the only shared mutation.
        common = Path(git(seed, 'rev-parse', '--git-common-dir'))
        if not common.is_absolute():
            common = seed / common
        with (common.resolve() / 'cco-provider-worktree.lock').open('w') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            subprocess.run(['git', 'worktree', 'add', '--detach', str(provider), pin], cwd=seed,
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    lake = provider / '.lake'
    lake.mkdir(exist_ok=True)
    dep_alias = lake / 'packages'
    if not dep_alias.exists():
        dep_alias.symlink_to(shared, target_is_directory=True)
    else:
        require(dep_alias.resolve() == shared.resolve(), 'Unexpected private-provider dependency path')
    build = lake / 'build'
    if not build.exists():
        subprocess.run(['cp', '-a', '--reflink=auto', str(seed / '.lake/build'), str(build)], check=True)
    require(build.is_dir() and not build.is_symlink(), 'Provider build must be an isolated directory')
    return provider


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--provider-seed', type=Path, required=True)
    parser.add_argument('--dependency-packages', type=Path, required=True)
    args = parser.parse_args()
    try:
        result = prepare(args.project.resolve(), args.provider_seed.resolve(), args.dependency_packages.resolve())
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))
    print('Prepared isolated pinned EPPA package and copied API artifacts:', result)


if __name__ == '__main__':
    main()
