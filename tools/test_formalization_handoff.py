"""Handoff reproducibility, changed-file detection and import completeness."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

import build_formalization_handoff as handoff


class HandoffTests(unittest.TestCase):
    def test_snapshot_is_reproducible_and_verifiable(self):
        files, manifest = handoff.collect(handoff.ROOT)
        first = handoff.archive_bytes(files, manifest)
        second = handoff.archive_bytes(files, manifest)
        self.assertEqual(hashlib.sha256(first).digest(), hashlib.sha256(second).digest())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with tarfile.open(fileobj=io.BytesIO(first), mode='r:gz') as archive:
                archive.extractall(root, filter='data')
            count, extracted = handoff.verify(root)
            self.assertEqual(count, len(files))
            self.assertEqual([x['id'] for x in extracted['modules']], list(handoff.MODULES))
            (root / 'formalization/sir/PROOF_NOTES.md').write_text('Changed proof')
            with self.assertRaisesRegex(ValueError, 'changed'):
                handoff.verify(root)

    def test_manifest_rejects_traversal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / handoff.MANIFEST).write_text(json.dumps({
                'format_version': 1, 'files': [{'path': '../outside'}]}))
            with self.assertRaisesRegex(ValueError, 'Invalid'):
                handoff.verify(root)


if __name__ == '__main__':
    unittest.main()
