#!/usr/bin/env python3
"""Discard generated CCO artifacts for one bounded clean-build fallback."""
from pathlib import Path
import shutil


def clear_project_artifacts(build: Path) -> list[Path]:
    """Keep packages and non-CCO outputs; never follow artifact symlinks."""
    build = build.resolve()
    # An alias at a namespace's parent cannot be removed by unlinking the
    # namespace itself. Reject before touching anything rather than traversing
    # that parent and deleting outputs in an external location.
    for parent in (build / 'lib', build / 'lib/lean', build / 'ir'):
        if parent.resolve() != parent:
            raise ValueError(f'refusing to clear through aliased artifact parent: {parent}')
    removed: list[Path] = []
    for directory in (build / 'lib/lean', build / 'ir'):
        targets = [directory / 'CCO', *sorted(directory.glob('CCO.*'))]
        for path in targets:
            if path.is_symlink() or path.is_file():
                path.unlink()
                removed.append(path)
            elif path.is_dir():
                shutil.rmtree(path)
                removed.append(path)
    return removed


if __name__ == '__main__':
    try:
        removed = clear_project_artifacts(Path('.lake/build'))
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    print(f'Discarded {len(removed)} generated CCO artifact tree(s)/file(s).')
