#!/usr/bin/env python3
"""Export verified private builds with the complete pinned provider notices.

The caller runs the complete guards/audits first. This archive is a local
compilation seed and never replaces a current-source build or axiom audit.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import tarfile

from external_provider import git, require, sha256
from factorization_forest_provider import DISTRIBUTION, verify_distribution
from restore_verified_build import BUILD_DIRS, INPUTS, validate_tar


def package(project: Path, bundle: Path) -> None:
    verify_distribution(project)
    # Refuse source or build aliases before copying a standalone binary bundle.
    for relative in BUILD_DIRS:
        path = project / relative
        require(path.is_dir() and path.resolve() == path.absolute(), 'Build root is missing/aliased: ' + relative)
    require(bundle.resolve() == bundle.absolute(), 'Aliased export directory')
    bundle.mkdir(parents=True, exist_ok=False)
    (bundle / 'checkout-sha.txt').write_text(git(project, 'rev-parse', 'HEAD') + '\n')
    (bundle / 'input-sha256.txt').write_text(''.join(sha256(project / n) + '  ' + n + '\n' for n in INPUTS))
    archive_path = bundle / 'build.tar.gz'
    # Recovery seeds favor fast export; upload-artifact already avoids a
    # second compression pass. The codec/restore checks are unchanged.
    with tarfile.open(archive_path, 'w:gz', compresslevel=1) as archive:
        for relative in BUILD_DIRS:
            archive.add(project / relative, arcname=relative)
    # Use the same path/link allowlist as restoration. In particular the
    # source/notice copy is inside the archive, not only in CI's checkout.
    with tarfile.open(archive_path, 'r:gz') as archive:
        validate_tar(archive)
    print(f'Exported verified-build seed and complete licensed forest distribution: {bundle}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--bundle', type=Path, required=True)
    args = parser.parse_args()
    try:
        package(args.project.resolve(), args.bundle.absolute())
    except (ValueError, OSError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
