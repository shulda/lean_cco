#!/usr/bin/env python3
"""Validate one exact CI ZIP and restore private build trees plus provider notices.

This repository helper never supplies proof, changes source, calls GitHub,
or replaces the mandatory accepted-source build/cache/axiom checks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import stat
import subprocess
import tarfile
import zipfile

from factorization_forest_provider import DISTRIBUTION, verify_distribution

BUILD_DIRS = (
    '.lake/build',
    '.lake/packages/AllThoseEPPA/.lake/build',
    'vendor/ramsey/.lake/build',
    DISTRIBUTION,
)
INPUTS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'CCO.lean')
ZIP_FILES = {'build.tar.gz', 'checkout-sha.txt', 'input-sha256.txt'}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha256_file(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def clean_name(name):
    require(isinstance(name, str) and name and '\\' not in name and '\0' not in name,
            'Invalid archive member name')
    raw = PurePosixPath(name)
    require(not raw.is_absolute() and '..' not in raw.parts,
            'Absolute/traversing archive member: ' + name)
    normal = posixpath.normpath(name)
    require(normal not in {'', '.'}, 'Empty archive member')
    return normal


def allowed_build(name):
    return any(name == root or name.startswith(root + '/') for root in BUILD_DIRS)


def validate_tar(archive):
    names = set()
    members = archive.getmembers()
    for item in members:
        name = clean_name(item.name)
        require(allowed_build(name), 'Tar member outside build allowlist: ' + name)
        require(name not in names, 'Duplicate tar member: ' + name)
        names.add(name)
        require(item.isdir() or item.isfile() or item.issym() or item.islnk(),
                'Special tar member is forbidden: ' + name)
        if item.issym() or item.islnk():
            target = item.linkname
            require(target and not PurePosixPath(target).is_absolute()
                    and '\\' not in target and '\0' not in target,
                    'Invalid tar link target: ' + name)
            # Symbolic targets are relative to the member; hard links are
            # archive-root-relative, as specified by the tar format.
            full = posixpath.normpath(
                posixpath.join(posixpath.dirname(name), target)
                if item.issym() else target)
            require(allowed_build(full), 'Tar link leaves build allowlist: ' + name)
    require(all(root in names for root in BUILD_DIRS), 'Missing build root in tar')
    # Python's data filter independently checks links and actual extraction
    # locations. Extraction is into a fresh private staging directory only.
    return members


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--zip', required=True, type=Path)
    parser.add_argument('--expected-checkout-sha', required=True)
    parser.add_argument('--expected-project-head', required=True)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--expected-zip-sha256')
    parser.add_argument('--stage', required=True, type=Path)
    parser.add_argument('--restore', action='store_true')
    args = parser.parse_args()
    root = args.project.resolve()
    require(re.fullmatch(r'[0-9a-f]{40}', args.expected_checkout_sha), 'Bad checkout SHA')
    actual_head = subprocess.check_output(
        ['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    require(actual_head == args.expected_project_head, 'Project HEAD changed')
    subprocess.run(['git', '-C', str(root), 'diff', 'HEAD', '--exit-code', '--',
                    'CCO', 'CCO.lean', 'lean-toolchain', 'lake-manifest.json',
                    'lakefile.toml', 'tools', 'vendor'], check=True,
                   stdout=subprocess.DEVNULL)
    stage = args.stage.resolve()
    require(stage.parent == root / '.lake' and not stage.exists()
            and stage.parent.resolve() == stage.parent,
            'Use a fresh stage directly below own physical project .lake')
    digest = sha256_file(args.zip)
    if args.expected_zip_sha256:
        require(digest == args.expected_zip_sha256.removeprefix('sha256:'),
                'Downloaded ZIP digest differs from supplied artifact digest')
    stage.mkdir(mode=0o700, parents=True)
    bundle = stage / 'bundle'
    bundle.mkdir(mode=0o700)
    with zipfile.ZipFile(args.zip) as archive:
        entries = archive.infolist()
        names = set()
        for item in entries:
            name = clean_name(item.filename)
            require(not item.is_dir() and name in ZIP_FILES,
                    'Unexpected artifact ZIP member: ' + name)
            require(name not in names, 'Duplicate artifact ZIP member: ' + name)
            names.add(name)
            require(not stat.S_ISLNK(item.external_attr >> 16), 'ZIP link forbidden')
        require(names == ZIP_FILES, 'Artifact ZIP must contain exactly three bundle files')
        for name in sorted(names):
            with archive.open(name) as source, (bundle / name).open('xb') as target:
                for block in iter(lambda: source.read(1024 * 1024), b''):
                    target.write(block)
    checkout = (bundle / 'checkout-sha.txt').read_text().strip()
    require(checkout == args.expected_checkout_sha, 'Unexpected actual CI checkout SHA')
    actual_inputs = {}
    for line in (bundle / 'input-sha256.txt').read_text().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'Invalid input-sha256 line')
        digest_input, name = match.groups()
        require(name in INPUTS and name not in actual_inputs, 'Unexpected/duplicate input name')
        actual_inputs[name] = digest_input
    expected_inputs = {name: sha256_file(root / name) for name in INPUTS}
    require(actual_inputs == expected_inputs, 'CI pinned/root inputs differ from current project')
    payload = stage / 'payload'
    payload.mkdir(mode=0o700)
    with tarfile.open(bundle / 'build.tar.gz', mode='r:gz') as archive:
        members = validate_tar(archive)
        member_count = len(members)
        regular_size = sum(item.size for item in members if item.isfile())
        archive.extractall(payload, members=members, filter='data')
    for relative in BUILD_DIRS:
        folder = payload / relative
        require(folder.is_dir() and not folder.is_symlink(), 'Build root is not a real directory')
    verify_distribution(root, payload / DISTRIBUTION)
    result = dict(zip_sha256=digest, checkout_sha=checkout, project_head=actual_head,
                  input_sha256=expected_inputs, tar_members=member_count,
                  tar_regular_bytes=regular_size, build_roots=list(BUILD_DIRS),
                  restored=False)
    (stage / 'validated.json').write_text(json.dumps(result, indent=2) + '\n')
    if args.restore:
        # Caller has confirmed no project build writer. Retain every previous
        # output tree for rollback; never touch source or another worktree.
        backups = stage / 'backups'
        backups.mkdir(mode=0o700)
        for relative in BUILD_DIRS:
            destination = root / relative
            require(destination.parent.resolve() == destination.parent,
                    'Destination parent contains a symlink')
            require(not destination.is_symlink(), 'Destination build root is a symlink')
        completed = []
        try:
            for number, relative in enumerate(BUILD_DIRS):
                destination = root / relative
                require(destination.parent.resolve() == destination.parent,
                        'Destination parent contains a symlink')
                require(not destination.is_symlink(), 'Destination build root is a symlink')
                destination.parent.mkdir(parents=True, exist_ok=True)
                backup = backups / str(number)
                had_old = destination.exists()
                if had_old:
                    os.replace(destination, backup)
                try:
                    os.replace(payload / relative, destination)
                except BaseException:
                    if had_old:
                        os.replace(backup, destination)
                    raise
                completed.append((relative, backup, had_old))
        except BaseException:
            for relative, backup, had_old in reversed(completed):
                os.replace(root / relative, payload / relative)
                if had_old:
                    os.replace(backup, root / relative)
            raise
        result['restored'] = True
        result['backup_roots'] = {relative: str(backup) if had_old else None
                                  for relative, backup, had_old in completed}
        (stage / 'restored.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
