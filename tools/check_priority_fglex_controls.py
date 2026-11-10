#!/usr/bin/env python3
"""B065 source/protocol controls, not a Lean or external-source verification."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
M=json.loads((ROOT/'formalization/priority_fglex/module.json').read_text())
B=json.loads((ROOT/'formalization/coordination/BOARD.json').read_text())
P=json.loads((ROOT/'formalization/coordination/AUTONOMY.json').read_text())
assert M['id']=='priority_fglex' and M['schema_version']==1
assert M['accepted_foundations']['original_source_commit']==B['source_commit']=='490c3f36d85db5a0b3ced0598e6c431825254ec5'
s=M['additive_source']
assert s['commit']=='e4426e22e649bb8774e88fc15e2c626a9d254aa4' and s['git_blob']=='9df581aa567cc0789623c84167329eb9314981d8' and s['file']=='cco-symmetric-eppa/papers/consolidated_working/sections/typed_hereditary_selectors.tex'
assert s['labels']==['lem:typed-gate-incidence','lem:typed-gate-lex','cor:typed-priority-HS']
rows=[x for x in B['packages'] if x['id']=='B065']
assert len(rows)==1 and rows[0]['depends_on']==['B004']
assert [x['id'] for x in M['claims']]==rows[0]['claims']['priority_fglex']==["C01","C02","C03","C04","C05"]
assert B['revision']>=21 and P['revision']>=20 and 'B065' in P['released_packages']
assert (ROOT/rows[0]['spec_file']).is_file()
print('B065 additive source-pins, claims and release PASS; no Lean acceptance inferred')
