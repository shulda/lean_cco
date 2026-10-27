"""Ownership, source/claim integrity and a self-contained staged launch."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import build_formalization_handoff as handoff
import check_formalization_coordination as coordination
import prepare_formalization_launch as launch


class CoordinationTests(unittest.TestCase):
    def board(self):
        board = json.loads((coordination.ROOT / coordination.DIRECTORY / 'BOARD.json').read_text())
        # Tests model allocation transitions, not the live assignment state.
        board['phase'], board['public_repository'] = 'PREPARATION', None
        board['projects'] = [{'id': 1, 'state': 'RESERVED'}]
        for package in board['packages']:
            first = package['id'] == 'B001'
            package['state'] = 'PREPARED' if first else 'PLANNED'
            package['owner_project_id'] = 1 if first else None
            package['accepted_commit'] = None
        return board

    def preparation_fixture(self, root):
        files, _ = handoff.collect(coordination.ROOT)
        for name, data in files.items():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        board = self.board()
        (root / coordination.DIRECTORY / 'BOARD.json').write_text(json.dumps(board))
        for name, content in coordination.generated(board).items():
            (root / name).write_text(content)
        return root

    def test_preparation_is_valid_but_not_an_active_launch(self):
        board = self.board()
        self.assertEqual(coordination.validate(coordination.ROOT, board), {1: 'B001'})
        with self.assertRaisesRegex(ValueError, 'not bound'):
            coordination.validate(coordination.ROOT, board, require_launch=True)

    def test_duplicate_ownership_and_false_dependency_are_rejected(self):
        board = self.board()
        second = board['packages'][1]
        second['state'], second['owner_project_id'] = 'PREPARED', 1
        with self.assertRaisesRegex(ValueError, 'more than one'):
            coordination.validate(coordination.ROOT, board)
        board = self.board()
        board['packages'][0]['depends_on'] = ['B002']
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            coordination.validate(coordination.ROOT, board)

    def test_missing_and_duplicate_claims_are_rejected(self):
        board = self.board()
        board['packages'][0]['claims']['raw_exact'].pop()
        with self.assertRaisesRegex(ValueError, 'missing'):
            coordination.validate(coordination.ROOT, board)
        board = self.board()
        board['packages'][1]['claims']['raw_exact'].append('C01')
        with self.assertRaisesRegex(ValueError, 'multiple'):
            coordination.validate(coordination.ROOT, board)

    def test_launch_is_bound_and_runs_from_its_own_snapshot(self):
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / 'launch'
            source = self.preparation_fixture(Path(temporary) / 'preparation')
            manifest = launch.prepare(source, destination, 'example/cco-lean')
            count, checked = handoff.verify(destination)
            self.assertEqual(count, len(manifest['files']))
            board = json.loads((destination / coordination.DIRECTORY / 'BOARD.json').read_text())
            self.assertEqual(board['public_repository'], 'example/cco-lean')
            self.assertEqual(board['packages'][0]['state'], 'ASSIGNED')
            instructions = (destination / coordination.DIRECTORY / 'PROJECT_1_INSTRUCTIONS.md').read_text()
            self.assertIn('https://github.com/example/cco-lean', instructions)
            self.assertNotIn('DOSUD NEURČEN', instructions)
            self.assertEqual(checked['coordination']['phase'], 'READY')
            completed = subprocess.run(
                [sys.executable, 'tools/check_formalization_coordination.py',
                 '--check', '--require-launch'], cwd=destination,
                capture_output=True, text=True)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            with self.assertRaises(FileExistsError):
                launch.prepare(source, destination, 'example/cco-lean')
            with self.assertRaisesRegex(ValueError, 'already bound'):
                launch.prepare(destination, Path(temporary) / 'rebound', 'example/other')

    def test_invalid_repository_does_not_create_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / 'launch'
            with self.assertRaisesRegex(ValueError, 'owner/name'):
                launch.prepare(coordination.ROOT, destination, '../wrong')
            self.assertFalse(destination.exists())

    def test_completed_project_can_wait_without_taking_another_package(self):
        board = self.board()
        board['phase'], board['public_repository'] = 'READY', 'example/cco-lean'
        board['projects'][0]['state'] = 'WAITING'
        package = board['packages'][0]
        package['state'], package['accepted_commit'] = 'ACCEPTED', 'a' * 40
        self.assertEqual(coordination.validate(coordination.ROOT, board, True), {})

    def test_two_peer_assignments_require_the_accepted_shared_core(self):
        board = self.board()
        board['phase'], board['public_repository'] = 'READY', 'example/cco-lean'
        board['projects'] = [{'id': 1, 'state': 'ACTIVE'}, {'id': 2, 'state': 'ACTIVE'}]
        for package, owner in zip(board['packages'][1:3], [1, 2]):
            package['state'], package['owner_project_id'] = 'ASSIGNED', owner
        with self.assertRaisesRegex(ValueError, 'more than one'):
            coordination.validate(coordination.ROOT, board)
        board['packages'][0]['state'] = 'BLOCKED'
        board['packages'][0]['owner_project_id'] = 2
        with self.assertRaisesRegex(ValueError, 'unaccepted'):
            coordination.validate(coordination.ROOT, board)
        core = board['packages'][0]
        core['state'], core['owner_project_id'], core['accepted_commit'] = 'ACCEPTED', 1, 'b' * 40
        self.assertEqual(coordination.validate(coordination.ROOT, board, True), {1: 'B002', 2: 'B003'})
        self.assertIn('STATE.json' if board['protocol_version'] == 2 else 'balíček je B003',
                      coordination.render_instructions(board, 2))


if __name__ == '__main__':
    unittest.main()
