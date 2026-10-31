#!/usr/bin/env python3
"""Validate profiles or emit an append-only proposal for another Chat project.

This never changes GitHub, live STATE, a claim or the active execution mode.
After reviewing the proposal, generate instructions with the normal checker.
"""
import argparse
from copy import deepcopy
import json
from pathlib import Path

import coordination_queue as q


def add_worker(registry, policy, number):
    q.validate_policy(registry, policy)
    q.require(type(number) is int and number > 0 and 'execution_profiles' in policy,
              'Use a positive new Chat number after initial profile deployment')
    actor = f'chat-{number}'
    q.require(actor not in policy['actors'], 'Never reuse an old project or actor number')
    result = deepcopy(policy)
    project = max(result['registered_projects']) + 1
    result['registered_projects'].append(project)
    result['chat_project_actors'][str(project)] = actor
    result['actors'][actor] = {'identity': f'chat-project:cco-{actor}',
        'roles': ['coordinate', 'implement', 'review', 'integrate'],
        'historical_author_projects': [project]}
    chat = result['execution_profiles']['chat']
    chat['project_ids'].append(project)
    chat['default_active_batches'] += 1
    chat['maximum_active_batches'] += 1
    result['revision'] += 1
    manifest = q.execution_profile_manifest(registry, policy, registry, result)
    return result, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--add-chat-worker', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--manifest-output', type=Path)
    args = parser.parse_args()
    directory = q.ROOT / q.DIRECTORY
    registry, policy = [json.loads((directory / f).read_text()) for f in ['BOARD.json', 'AUTONOMY.json']]
    if args.add_chat_worker is None:
        q.validate_policy(registry, policy)
        print(json.dumps({'valid': True, 'policy_revision': policy['revision'],
                          'chat_projects': policy.get('chat_project_actors', {})}))
        return
    q.require(args.output is not None, 'Emit a reviewed policy proposal with --output')
    proposed, manifest = add_worker(registry, policy, args.add_chat_worker)
    args.output.write_text(json.dumps(proposed, indent=2) + '\n')
    if args.manifest_output:
        args.manifest_output.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'published': False, 'proposal': str(args.output),
                      'new_policy_revision': proposed['revision'],
                      'next_step': 'Review policy/instructions PR, lock, exact PR/main CI, promote_profiles.'}))


if __name__ == '__main__':
    main()
