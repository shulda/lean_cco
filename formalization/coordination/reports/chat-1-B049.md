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


## 2026-11-01 typed TSC/TSC2 accepted source-strength Lean checkpoint

**GREEN WIP source code SHA** `e496eec6bd6a497897e6e6d2763719aa97df6497`,
actual remote CI **41318245937**, job **124882785122**: entire
4401-job Lean build, full current-source/cache verification of
1727 CCO modules, and transitive audit of 29317 declarations using
ONLY `propext`, `Classical.choice`, `Quot.sound`.
Broker checkpoint `20261101_chat1_B049_TSC_e496eec_r543_c7ab42fd`
applied at actual STATE **rev 544**, original B049 claim maintained.
The independent old-G homo/SAP, full typed atom, positive STRONG
versus equality-inclusive RAW distinction are preserved; no
hypothetical typed product or artificial unit was added.

**Compiled declarations:**
- `TransitionClosure.TypedFreshAtomMotion.original_fresh_typed_atom_left_in_equiv`
  and `original_fresh_typed_atom_right_in_equiv`: real exact typed
  old atom can move either endpoint inside its original nonzero
  equivalence class, preserving the opposite endpoint, original atom
  and avoiding any finite set of original tagged points. Proven from
  actual full-source stabilizer SAP; this is NOT hidden/quotient SAP.
- `TransitionClosure.TypedRawStrongSaturation.original_raw_typed_J_atom_K_guard_eq_strong`:
  `(J ; {t} ; K)° = J° * {t} * K°` with different sorts i,j allowed,
  both J,K original nonzero equivalences. Real source atom profiles
  and endpoint pairs remain pinned, no CCO/NR2.
- `TransitionClosure.OriginalEquivalenceJoinStrong.original_raw_equiv_equiv_guard_eq_strong`
  and `original_raw_equiv_join_guard_eq_strong`:
  `(J ; K)° = J° * K° = (J∨K)°` with actual old FULL invariant
  `ColourEq.join`, real SAP, no fake STRONG equality step.

**Newer WIP:** `TransitionClosure.TypedIdentityExterior` explicitly
handles all THREE omitted-identity-exterior source cases with original
nonzero J, nonzero K, or neither; the initial remote CI error was a
local reversal of negated equality (`¬u=x`), corrected in
`09772353e9cf98c98771c330e875908326b16b73`. Source appendix
and this progress report are subsequent report-only commits, so
they require their OWN exact-head CI before any next checkpoint.
This work is not submitted or accepted; current slot remains B049.

**Next mathematical branch:** B049 C09 typed strong PC exact domain
from B003, with exact original CCO and finite support-consistent
triangles; then C10 directly constructed old positive-word 2-Helly
without exact-PC shortcuts, then original FULL meet-irreducible
J⋖K first-hit interpolation using now ACCEPTED B050 source09
full quotient STRONG semigroup and positive external cover layer.
The older source preparation explicitly forbids Set-Pasch shortcuts,
unproved quotient SAP, source weakening, or mixing same-sort
commutation with typed letters. Subsequent transport normal forms
must remain on original invariant RAW quotient relations, distinguish
real-point SAP noncollapse from merely invariant transport, and
count actual unary FUNCTIONS rather than expression syntax.

No additional author, accepted provider API, frozen paper, toolchain,
main source, or other project's branch has been changed.
