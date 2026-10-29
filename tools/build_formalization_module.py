#!/usr/bin/env python3
"""Validate the bounded human proof module and render its source-linked index.

This checks metadata and provenance, not mathematical truth or Lean readiness.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MODULE = Path('formalization/raw_exact')
RESULTS = {'theorem', 'lemma', 'proposition', 'corollary'}


def blob_sha(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def topological_order(nodes):
    """Deterministic provider-before-consumer order; reject unknowns/cycles."""
    ids = [n['id'] for n in nodes]
    if len(ids) != len(set(ids)):
        raise ValueError('Duplicate module node')
    pending = {n['id']: set(n.get('depends_on', [])) for n in nodes}
    if any(dep not in pending for deps in pending.values() for dep in deps):
        raise ValueError('Unknown module dependency')
    ordered = []
    while pending:
        ready = sorted(n for n, deps in pending.items() if not deps)
        if not ready:
            raise ValueError('Cyclic module dependencies')
        ordered.extend(ready)
        for n in ready:
            del pending[n]
        for deps in pending.values():
            deps.difference_update(ready)
    return ordered


def validate_provider_support(provider, item, exported):
    """Check internal human proof provenance, without creating theorem exports."""
    support = item.get('provider_support_claims')
    usage = item.get('provider_support_usage')
    selected = item.get('provider_claims', exported)
    claims = {c['id']: c for c in provider['claims']}
    def nonempty_ids(values):
        return (isinstance(values, list) and bool(values)
                and all(isinstance(c, str) for c in values)
                and len(values) == len(set(values)))
    if (not nonempty_ids(exported) or not set(exported) <= claims.keys()
            or not nonempty_ids(selected) or not set(selected) <= set(exported)):
        raise ValueError('Internal proof support requires valid selected export claims')
    if not nonempty_ids(support) or not isinstance(usage, str) or not usage.strip():
        raise ValueError('Internal proof support requires unique nonempty claims and explicit usage')
    nodes = (provider['assumptions'] + provider.get('external_providers', [])
             + provider.get('imports', []) + provider['definitions'] + provider['claims'])
    by_id = {n['id']: n for n in nodes}
    ancestors = {}
    for ident in topological_order(nodes):
        deps = by_id[ident].get('depends_on', [])
        ancestors[ident] = set(deps).union(*(ancestors[d] for d in deps))
    eligible = set().union(*(ancestors[c] for c in selected)) & claims.keys()
    if (not set(support) <= eligible or set(support) & set(selected)
            or any(claims[c]['status'] != 'HUMAN_PROOF_EXPANDED' for c in support)):
        raise ValueError('Internal proof support must be proved strict claim ancestors')
    return [claims[c] for c in support]


def validate_external_providers(module):
    """Validate explicit pending external inputs, never compiled local proofs.

    Only the published, versioned arXiv-provider shape currently needed by
    B027 is supported. Activating a compiled adapter requires a separate
    reviewed contract/implementation change, not a metadata status shortcut.
    """
    providers = module.get('external_providers', [])
    if not isinstance(providers, list):
        raise ValueError('External providers must be an explicit list')
    for item in providers:
        if not isinstance(item, dict) or item.get('status') != 'PUBLISHED_THEOREM_LOCAL_BRIDGE_PENDING':
            raise ValueError('External theorem status must retain local bridge obligation')
        if (not isinstance(item.get('id'), str) or not re.fullmatch(r'E[0-9]{2}', item['id'])
                or any(not isinstance(item.get(key), str) or not item[key].strip()
                       for key in ['name', 'statement', 'source_version', 'theorem'])
                or not re.fullmatch(r'[0-9]{4}\.[0-9]{4,5}v[1-9][0-9]*', item['source_version'])
                or not re.fullmatch(r'[1-9][0-9]*(?:\.[0-9]+)*', item['theorem'])):
            raise ValueError('External theorem requires a versioned precise contract')
        if (not isinstance(item.get('depends_on'), list)
                or any(not isinstance(dep, str) or not dep for dep in item['depends_on'])
                or len(item['depends_on']) != len(set(item['depends_on']))):
            raise ValueError('External theorem requires explicit unique dependencies')
        if item.get('source_url') not in {
                f'https://arxiv.org/html/{item["source_version"]}',
                f'https://arxiv.org/abs/{item["source_version"]}'}:
            raise ValueError('External theorem requires its versioned primary source URL')
        ref = item.get('lean_reference')
        if ref is not None:
            qualified = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+'
            if (not isinstance(ref, dict)
                    or not isinstance(ref.get('repository'), str)
                    or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*', ref['repository'])
                    or any(not isinstance(ref.get(key), str)
                           or not re.fullmatch(r'[0-9a-f]{40}', ref[key])
                           for key in ['commit', 'mathlib_commit'])
                    or not isinstance(ref.get('module'), str)
                    or not re.fullmatch(qualified, ref['module'])
                    or ref.get('source_file') != ref['module'].replace('.', '/') + '.lean'
                    or not isinstance(ref.get('lean_version'), str)
                    or not re.fullmatch(r'v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?', ref['lean_version'])
                    or ref.get('bridge_status') != 'NOT_BOUND_TO_CCO_ENCODING'
                    or not isinstance(ref.get('declarations'), list) or not ref['declarations']
                    or any(not isinstance(name, str) or not re.fullmatch(qualified, name)
                           for name in ref['declarations'])
                    or len(ref['declarations']) != len(set(ref['declarations']))):
                raise ValueError('Existing Lean reference must be pinned and retain encoding bridge')


def validate(root, module, declarations):
    sources = {x['file']: x for x in module['source_files']}
    if len(sources) != len(module['source_files']):
        raise ValueError('Duplicate source file')
    raw = {}
    for file, record in sources.items():
        data = (root / file).read_bytes()
        if blob_sha(data) != record['git_blob']:
            raise ValueError(f'Source changed; review contract before repinning: {file}')
        raw[file] = data.decode()
    if module['source_commit'] != declarations['summary']['source_commit']:
        raise ValueError('Catalogue and module source pins differ')
    by_label = {label: d for d in declarations['declarations'] for label in d['labels']}

    def check_anchor(item):
        file, anchor = item['file'], item['anchor']
        if file not in raw or not anchor or anchor not in raw[file]:
            raise ValueError(f'Unknown source anchor: {item}')

    directory = Path('formalization') / module['id']
    notes = (root / directory / 'PROOF_NOTES.md').read_text()
    imports = module.get('imports', [])
    validate_external_providers(module)
    nodes = (module['assumptions'] + module.get('external_providers', []) + imports
             + module['definitions'] + module['claims'])
    order = topological_order(nodes)
    ancestors = {}
    by_node = {n['id']: n for n in nodes}
    for ident in order:
        deps = by_node[ident].get('depends_on', [])
        ancestors[ident] = set(deps).union(*(ancestors[d] for d in deps))
    for firewall in module.get('dependency_firewalls', []):
        if not set(firewall['claims'] + firewall['forbid']) <= by_node.keys():
            raise ValueError('Unknown dependency firewall node')
        if any(ancestors[c] & set(firewall['forbid']) for c in firewall['claims']):
            raise ValueError('Dependency firewall crossed')
    catalogue_labels = set(by_label)
    catalogue_sources = dict(by_label)
    for item in imports:
        label = item['source_label']
        has_internal_support = ('provider_support_claims' in item
                                or 'provider_support_usage' in item)
        if has_internal_support and not item.get('provider_module'):
            raise ValueError('Internal proof support requires a pinned provider module')
        # An equation may already occur as a secondary label inside a
        # catalogued numbered theorem. It still needs the same pinned
        # auxiliary-export checks, rather than a broader provider escape.
        auxiliary_import = label not in catalogue_labels or label.startswith('eq:')
        if auxiliary_import and not item.get('provider_module'):
            raise ValueError(f'Unknown imported source without pinned auxiliary provider: {label}')
        if auxiliary_import and item.get('provider_module'):
            provider = json.loads((root / 'formalization' / item['provider_module'] / 'module.json').read_text())
            matching = [x for x in provider['exports'] + provider.get('auxiliary_exports', [])
                        if x['source_label'] == label]
            if len(matching) != 1 or 'source' not in matching[0]:
                raise ValueError(f'Unknown imported source or ambiguous auxiliary export: {label}')
            export = matching[0]
            source = export['source']
            check_anchor(source)
            provider_sources = [x for x in provider['source_files'] if x['file'] == source['file']]
            if (provider['source_commit'] != module['source_commit']
                    or len(provider_sources) != 1
                    or provider_sources[0]['git_blob'] != sources[source['file']]['git_blob']
                    or source['anchor'] != '\\label{' + label + '}'):
                raise ValueError(f'Imported auxiliary source fingerprint mismatch: {label}')
            selected = item.get('provider_claims')
            support = export['claims']
            provider_claims = {c['id'] for c in provider['claims']}
            if (not isinstance(selected, list) or not selected
                    or len(selected) != len(set(selected))
                    or not support or len(support) != len(set(support))
                    or not set(support) <= provider_claims
                    or not set(selected) <= set(support)):
                raise ValueError(f'Imported auxiliary support claims mismatch: {label}')
            if label in by_label and by_label[label]['file'] != source['file']:
                raise ValueError(f'Ambiguous imported auxiliary source: {label}')
            if label not in catalogue_labels:
                by_label[label] = {'id': label, 'kind': 'equation', 'file': source['file'],
                    'line': raw[source['file']].count('\n', 0, raw[source['file']].index(source['anchor'])) + 1}
        if label not in by_label or by_label[label]['file'] not in sources:
            raise ValueError(f'Unknown imported source declaration: {label}')
        if item['status'] not in {'HUMAN_EXPANDED_NOT_LEAN', 'EXPLICIT_UPSTREAM_NOT_EXPANDED',
                                   'HUMAN_SUPPORT_PROOF_NOT_LEAN'}:
            raise ValueError('Unexpected imported proof status')
        if item.get('provider_module'):
            provider = json.loads((root / 'formalization' / item['provider_module'] / 'module.json').read_text())
            exports = provider['exports'] + (provider.get('auxiliary_exports', []) if auxiliary_import else [])
            if provider['source_commit'] != module['source_commit'] or label not in {
                    x['source_label'] for x in exports}:
                raise ValueError(f'Imported provider module mismatch: {label}')
            if has_internal_support:
                matching = [e for e in exports if e['source_label'] == label]
                if len(matching) != 1:
                    raise ValueError('Internal proof support requires a unique provider export')
                support_claims = validate_provider_support(provider, item, matching[0]['claims'])
                # Bind the named result AND every extracted claim's own source.
                # The immutable catalogue is separate from synthetic auxiliary imports.
                labels = {label}.union(*(set(c['source_labels']) for c in support_claims))
                for support_label in labels:
                    source = catalogue_sources.get(support_label)
                    if source is None:
                        aux = [e for e in provider.get('auxiliary_exports', [])
                               if e['source_label'] == support_label]
                        if len(aux) != 1:
                            raise ValueError('Unknown internal proof support source')
                        source = aux[0]['source']
                        check_anchor(source)
                        if source['anchor'] != '\\label{' + support_label + '}':
                            raise ValueError('Invalid internal proof support source anchor')
                    file = source['file']
                    provider_sources = [s for s in provider['source_files'] if s['file'] == file]
                    if (file not in sources or len(provider_sources) != 1
                            or provider_sources[0]['git_blob'] != sources[file]['git_blob']):
                        raise ValueError('Internal proof support source fingerprint mismatch')
    claim_ids = {c['id'] for c in module['claims']}
    auxiliary = {}
    for item in module.get('auxiliary_exports', []):
        label, source = item['source_label'], item['source']
        check_anchor(source)
        if (label in auxiliary or label in {e['source_label'] for e in module['exports']}
                or source['anchor'] != '\\label{' + label + '}'
                or not item['claims'] or not set(item['claims']) <= claim_ids):
            raise ValueError('Invalid auxiliary source equation')
        auxiliary[label] = source
    for item in module['definitions']:
        check_anchor(item['source'])
    for item in module['definitions'] + module['claims']:
        if f"## {item['notes']}:" not in notes:
            raise ValueError(f'Missing proof note for {item["id"]}')
    for claim in module['claims']:
        if claim['status'] != 'HUMAN_PROOF_EXPANDED':
            raise ValueError('Unexpected proof status; do not infer Lean certification')
        if claim['scope'] not in module.get('scope_vocabulary', ['typed', 'one_original_sort']):
            raise ValueError('Missing typed/one-original-sort qualification')
        if not claim['source_labels'] or any(
                (label not in by_label and label not in auxiliary)
                or (by_label[label]['file'] if label in by_label else auxiliary[label]['file']) not in sources
                for label in claim['source_labels']):
            raise ValueError(f'Unknown claim source label: {claim["id"]}')
    exports = [x['source_label'] for x in module['exports']]
    result_files = module.get('source_result_files', [f for f in sources if f != 'main.tex'])
    if not set(result_files) <= sources.keys():
        raise ValueError('Unknown result source file')
    expected = {d['id'] for d in declarations['declarations']
                if d['file'] in result_files
                and d['kind'] in RESULTS}
    selected = module.get('additional_result_exports', [])
    if len(selected) != len(set(selected)):
        raise ValueError('Duplicate selected additional result')
    for label in selected:
        declaration = by_label.get(label)
        if (declaration is None or declaration['file'] not in sources
                or declaration['file'] in result_files or declaration['kind'] not in RESULTS):
            raise ValueError('Unknown selected additional result')
        expected.add(declaration['id'])
    if set(exports) != expected or len(exports) != len(set(exports)):
        raise ValueError('Source result export map is incomplete or duplicated')
    for export in module['exports']:
        if not export['claims'] or not set(export['claims']) <= claim_ids:
            raise ValueError('Unknown or empty export proof claims')
    tasks = module['tasks']
    task_order = topological_order(tasks)
    assigned = [c for task in tasks for c in task['claims']]
    if set(assigned) != claim_ids or len(assigned) != len(set(assigned)):
        raise ValueError('Implementation tasks do not cover exactly the module claims')
    owner = {c: task['id'] for task in tasks for c in task['claims']}
    ancestors = {}
    by_task = {t['id']: t for t in tasks}
    for ident in task_order:
        deps = by_task[ident]['depends_on']
        ancestors[ident] = set(deps).union(*(ancestors[d] for d in deps))
    for claim in module['claims']:
        task = owner[claim['id']]
        if any(dep in owner and owner[dep] != task and owner[dep] not in ancestors[task]
               for dep in claim['depends_on']):
            raise ValueError(f'Implementation task misses a claim provider: {claim["id"]}')
    if any(task['status'] != 'NOT_STARTED_IN_LEAN' for task in tasks):
        raise ValueError('Update status handling explicitly when Lean implementation begins')
    for feedback in module['article_feedback']:
        check_anchor(feedback['source'])
        if not set(feedback['proof_claims']) <= claim_ids:
            raise ValueError('Unknown feedback proof claim')
    return order, by_label, raw


def render(module, order, by_label, raw):
    lines = [
        '# ' + module.get('index_title', 'RAW exact calculus and joint quotient lifting'), '',
        'Generated from `module.json` by `tools/build_formalization_module.py`.', '',
        f"Source `{module['source_commit']}`. **Human-expanded proof plan; no Lean code.**", '',
        module['scope'], '',
        'The human article remains unchanged. Additional proof details are in',
        '[PROOF_NOTES.md](PROOF_NOTES.md); the cross-track policy is in',
        '[the formalization guide](../README.md). Source hashes are checked before',
        'the index is regenerated. Graph validation is not proof verification.', '',
        '## Source premises', '',
    ]
    for item in module['assumptions']:
        lines += [f"**{item['id']}: {item['name']}.** {item['statement']}", '']
    if module.get('external_providers'):
        lines += ['## Published external theorem providers', '',
                  'These inputs are not new local proof claims or compiled CCO imports.',
                  'Existing Lean APIs still require the explicit representation bridge.', '']
        for item in module['external_providers']:
            lines += [f"**{item['id']}: {item['name']}.** {item['statement']}", '',
                      f"[Primary source, {item['source_version']}, {item['theorem']}]({item['source_url']}). "
                      f"Status: `{item['status']}`.", '']
            if item.get('lean_reference'):
                ref = item['lean_reference']
                lines += [f"Existing Lean: `{ref['repository']}` at `{ref['commit']}`, "
                          f"module `{ref['module']}`; declarations " + ', '.join(f'`{d}`' for d in ref['declarations']) + '.', '',
                          'The adapter to the current CCO encoding remains a receiving-project obligation.', '']
    if module.get('imports'):
        lines += ['## Imported theorem contracts', '',
                  'These are named provider obligations for the receiving Lean project,',
                  'not new axioms or claims of compiled imports.', '',
                  '| ID and source | Contract | Current provider status |', '|---|---|---|']
        for item in module['imports']:
            source = by_label[item['source_label']]
            lines.append(f"| {item['id']}: [`{item['source_label']}`](../../{source['file']}#L{source['line']}) | {item['statement']} | {item['status']} |")
        lines += ['']
        for item in module['imports']:
            if 'provider_support_claims' in item:
                lines += [f"**{item['id']} internal proof support:** "
                          f"{', '.join(item['provider_support_claims'])} in "
                          f"`{item['provider_module']}`. {item['provider_support_usage']}", '',
                          'These are separately extracted proved support claims, not additional',
                          'numbered exports or consequences of the named theorem statement.', '']
    lines += ['## Definitions', '',
              '| ID | Definition | Exact meaning | Source |', '|---|---|---|---|']
    for item in module['definitions']:
        s = item['source']
        line = raw[s['file']].count('\n', 0, raw[s['file']].index(s['anchor'])) + 1
        link = f"[source](../../{s['file']}#L{line})"
        lines.append(f"| {item['id']} | {item['name']} | {item['statement']} | {link} |")
    lines += ['', '## Proof claims and direct dependencies', '',
              'Every row has a human proof expansion. Each still needs an actual Lean',
              module.get('scope_explanation', 'statement and proof. The one-original-sort qualifier is substantive.'), '',
              '| ID and claim | Scope | Direct providers | Proof note |', '|---|---|---|---|']
    for item in module['claims']:
        lines.append(f"| {item['id']}: {item['name']} | {item['scope']} | {', '.join(item['depends_on'])} | {item['notes']} in [notes](PROOF_NOTES.md) |")
    lines += ['', 'The precise quantified contracts are in `module.json`. Provider-before-consumer',
              'order (including definitions and source premises):', '',
              '`' + ' → '.join(order) + '`', '',
              'This order is one valid linearization; it does not require unrelated',
              'branches to be proved sequentially. The full DAG is the `depends_on`',
              'relation in `module.json`.', '',
              '## Main proof branches', '',
              'This is a coarse view of the claim DAG. Edges go from provider to consumer.', '',
              '```mermaid', *module.get('overview_mermaid', ['flowchart TD',
              '  R["Orbitals, relations and words"] --> W["Theta cycles and word Helly"]',
              '  R --> B["Anchored fan cycles and ball Helly"]',
              '  W --> P["Exact products and meet distribution"]',
              '  P --> Q["Actual quotient orbital pullbacks"]',
              '  Q --> C["Fine-colour reconstruction"]',
              '  R --> J["One-sort commutation and mixed joins"]',
              '  Q --> J',
              '  Q --> L["Finite real-point extension"]',
              '  B --> L',
              '  L --> H["Back-and-forth and joint lifting"]',
              '  H --> U["Unary enrichment and age AP"]',
              '  Q --> T["Triangle fullness"]',
              '  B --> T',
              '  Q --> X["Quotient path expansion and CCO"]',
              '  R --> X']),
              '```', '', *module.get('overview_notes', [
              'Colour reconstruction is not an input to lifting. Mixed-join algebra',
              'does not require joint homogeneity. Quotient CCO uses original CCO and',
              'the path expansion, independently of quotient AP.']), '',
              '## Article exports', '',
              '| Existing source result | Sidecar proof claims |', '|---|---|']
    for export in module['exports']:
        label = export['source_label']
        d = by_label[label]
        lines.append(f"| [`{label}`](../../{d['file']}#L{d['line']}) | {', '.join(export['claims'])} |")
    if module.get('auxiliary_exports'):
        lines += ['', 'Auxiliary source equations (not additional numbered results):', '']
        for export in module['auxiliary_exports']:
            source = export['source']
            line = raw[source['file']].count('\n', 0, raw[source['file']].index(source['anchor'])) + 1
            lines.append(f"- [`{export['source_label']}`](../../{source['file']}#L{line}): "
                         + ', '.join(export['claims']))
    if module.get('additional_result_exports'):
        lines += ['', 'Full result coverage is asserted only for `source_result_files`.',
                  'Selected additional results: ' + ', '.join(module['additional_result_exports']) + '.',
                  'Other results in their provider source files are not claimed covered.', '']
    lines += ['', '## Internal implementation milestones', '',
              'These tasks are proof milestones inside larger project assignments;',
              'see the [peer-project allocation](../coordination/BOARD.md).', '',
              'These are implementation tasks, not additional mathematical assumptions.', '',
              '| Task | Earlier tasks | Acceptance |', '|---|---|---|']
    for task in module['tasks']:
        lines.append(f"| {task['id']}: {task['name']} | {', '.join(task['depends_on']) or '—'} | {task['acceptance']} |")
    lines += ['', '## Finite controls', '']
    for control in module['controls']:
        lines += [f"- **{control['id']}.** {control['check']}"]
    lines += ['', f"Run `python {module.get('control_script', 'tools/check_raw_exact_controls.py')}` from the manuscript directory.",
              'The controls do not prove CCO or the general theorems.', '',
              '## Return to the human articles', '']
    lines += ([module['article_feedback_intro'], ''] if module.get('article_feedback_intro') else
              ['No required mathematical repair was found in this scoped pass. These',
               'optional wording clarifications remain queued for a human article pass:', ''])
    for item in module['article_feedback']:
        s = item['source']
        ln = raw[s['file']].count('\n', 0, raw[s['file']].index(s['anchor'])) + 1
        lines += [f"- **{item['id']}** ([source](../../{s['file']}#L{ln})): {item['finding']} {item['proposed_article_change']}"]
    lines += ['', 'The machine ledger records caller effects and affected claims. The source',
              'review used two independent model review passes and parent synthesis;',
              'it is not independent human or formal certification.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--module', default='raw_exact', choices=['raw_exact', 'strong_selectors', 'sir', 'parity_hasse', 'exact_crt', 'canonical_hull', 'real_closure', 'finite_packets', 'rigid_groupoid', 'finite_kernel', 'owner_action', 'owner_master', 'joint_owner', 'acl_owner_geometry', 'finite_lift', 'mi_geometry', 'owner_transversal', 'safe_readings', 'direct_owner_closure', 'hkn_reservoir', 'terminal_powers'])
    args = parser.parse_args()
    directory = Path('formalization') / args.module
    module = json.loads((ROOT / directory / 'module.json').read_text())
    decls = json.loads((ROOT / 'catalogue/declarations.json').read_text())
    order, by_label, raw = validate(ROOT, module, decls)
    text = render(module, order, by_label, raw)
    out = ROOT / directory / 'README.md'
    if args.check:
        if not out.exists() or out.read_text() != text:
            raise SystemExit('Stale module index; run tools/build_formalization_module.py')
    else:
        out.write_text(text)
    print(f"Validated {len(module['definitions'])} definitions, {len(module['claims'])} claims, "
          f"{len(module['exports'])} exports and {len(module['tasks'])} implementation tasks; no Lean proof claimed.")


if __name__ == '__main__':
    main()
