# B049 — chat-1 / project 4 — actual claim and receiving progress

- Stable author: `chat-project:cco-chat-1`, actor `chat-1`, project 4, historical authorship retained.
- Previous B050 was independently reviewed by actual `chat-3`, merged as `636d6c89afcb68fe4e0c633e561a0b174a4e9855`, audited on main CI run `41314218664`, and **ACCEPTED** by canonical coordination STATE revision 542.
- B049 `claim_next` request `20261101_chat1_claimnext_after_B050_158b2ad7` returned **applied**, revision **543**, STATE blob `50865ba601463da0f6cfa74dac9f5d74d62a52a6`; owner project 4, branch `chat/chat-1/B049`, initial accepted base `636d6c89afcb68fe4e0c633e561a0b174a4e9855` with exact main CI `41314218664`, audit allowlist.
- Frozen human source `shulda/cycle_constrainedness@490c3f36d85db5a0b3ced0598e6c431825254ec5`, `sections/v27/07_typed_raw_strong_transition.tex`, 12 selected results, 62 claims, 12 definitions, 15 equations, eight tasks. Contract: `formalization/coordination/packages/B049.md`; human notes `formalization/transition_closure/PROOF_NOTES.md`, source map `module.json`.
- Actual ACCEPTED dependencies B003, B011, B038, B040, B050. In particular B050's independent source09 `FibreSAP.original_quotient_semigroup` and `OriginalFullExternalLayer.original_full_cover_external_layer_positive_word` are now on main; no reverse B049 dependency.
- Actual tool capability: GitHub remote read/create/update files, exact branch creation, PR, expected-head merge. No local Lean required. Remote Lean CI must verify every code checkpoint.

## First source07 C01–C05 code

`CCO/TransitionClosure/TypedFreshAtomMotion.lean` adds
`original_fresh_typed_atom_left_in_equiv`: an ORIGINAL real typed atom
`a : Atom i j`, with potentially distinct sorts `i,j`, can have its left
endpoint moved within its ACTUAL nonzero original invariant J-class,
arbitrarily far from a finite tagged forbidden set, while fixing the
right endpoint and exact old atom. This is built from ACCEPTED B050's
proved old J-fibre freshness and B001's actual old AgeSAP stabilizer
orbit theorem over the COMPLETE base of original anchor and right
endpoint; no quotient SAP, enlargement of original group, CCO or extra axiom.

The proof must pass actual branch-head CI before being called green.
Next direct proof obligations: typed J;t;K RAW-diversity vs STRONG menu
identity with BOTH exterior kernels nonzero and pinned actual endpoints,
then the two-factor same-sort J;K identity and identity-factor omission.
Only then build original positive Helly/first-hit interpolation/MI
primality. Subsequent transportation uses actual B040 quotient maps,
with old SAP no-real-collapse discharged separately, and finite
normal-form/cylinder/atomic naming. No source/Mathlib/toolchain pin,
accepted dependency code, or other actor branch is modified.

## Publication protocol

Keep `formalization/coordination/submissions/B049.md` source-to-Lean
mapping current with real signatures, all remaining obligations and exact
CI references. Green WIP checkpoint != submission. Final submit needs all
12 exports, 62 claims, 12 definitions, 15 equations, eight tasks, exact
head Lean build+source-cache/axiom audit, independent non-author review,
valid one-at-a-time integration lock, history-preserving expected-head
merge, green actual main CI and final broker acceptance. Current B049 is
IN_PROGRESS: **not submitted, approved, integrated or accepted**.
