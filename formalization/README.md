> Public receiving repository: B001 is accepted. These module records are
> mathematical preparation, not a claim that whole modules are formalized.
> Use [protocol 2](coordination/PROTOCOL.md), the release policy and live
> coordination-branch STATE for current work and acceptance.

# Formalization preparation and the human articles

This directory starts the separate formalization-preparation track agreed on
26 October 2026. The human mathematical sources remain `main.tex`, `sections/`
and the eight `articles/` wrappers. They are not to acquire a lemma for every
representation conversion needed by a proof assistant.

**Other projects implement Lean.** This project prepares source snapshots,
contracts, proof decompositions and work orders for them. Read
[HANDOFF.md](HANDOFF.md) for startup, division of work and the required return
ledger. No Lean project or CI is to be created in the source manuscript
repository by this preparation task. In a bound public receiving repository,
B001 explicitly includes creating the Lean project and CI there.

The [peer-project protocol and launch plan](coordination/README.md) assigns
substantial `B` packages to numbered projects. Module `T` tasks remain internal
proof milestones. Start Project 1 with the shared API, actual elementary
proofs and a consumer; test the reporting/integration process before adding
Project 2. The author mediates exceptions with this preparation project.

The first bounded module is [RAW exact geometry](raw_exact/README.md): the
three `sections/exact_foundations/` files, from represented word profiles
through joint lifting and inheritance by actual exact quotient sorts. This
does not cover all of Foundations I, exact CRT or real hulls.

The second bounded module is [STRONG calculus and selectors](strong_selectors/README.md):
the actual SAP diversity algebra, finite PC semantics and joint hereditary
selectors. It separates SAP-only steps, CCO steps and the full sortwise NR2
argument; its general pure-tag engine retains its explicit no-return premise.
RAW Helly is not a prerequisite. SIR and the augmented safe EPPA readings
are separate consumers.

The third module is [SIR](sir/README.md): 13 definitions, 25 claims and all
eight source results. It distinguishes the conditional selected-amalgam
constructor from the source-level provider instantiation; its finite-global
negative branch retains the Hasse theorem as an explicit upstream obligation.
The direct relative-two-sheet example is independent of NR2/HS. These SIR notes come from the source preparation repository. Public
`CCO/` now contains the accepted B001 implementation, not the SIR theorems.

## How the two tracks stay connected

- Keep existing article labels as the mathematical export names. New local
  proof steps have sidecar IDs; they do not become article theorem labels.
- Record exact source blobs, definitions, hypotheses, proof steps and their
  dependencies in the module. A changed source fingerprint requires review,
  rather than silently treating an old contract as current.
- Put witness choices, empty-family cases, quotient representatives, finite
  graph bookkeeping and encoding decisions here. Keep concise mathematical
  explanations in the articles.
- Record every mathematical discovery in the module's `article_feedback`
  ledger. A counterexample, missing premise or changed conclusion needs a
  proposed article repair and a caller check. A routine encoding lemma does
  not. After a repair, update both the article and its sidecar provenance;
  preserve the old version in Git.
- When preparing a publication version, follow the export map and feedback
  ledger. It is unnecessary to reverse a long sequence of Lean-oriented
  edits to recover the human proof: those details live here already.

An empty feedback queue means no required article repair was found in this
bounded pass. It does not certify the full manuscript. The existing archived
pre-cleanup source and the eight working articles remain the publication
return points; this directory is additional material, not a replacement.

## Status and reproducible checks

`module.json` distinguishes source assumptions, definitions, human-expanded
proof claims, source exports, implementation tasks and article feedback.
`README.md` in each module is generated from that record. `PROOF_NOTES.md`
contains the extra mathematical reasoning. Neither graph validation nor the
finite regression controls prove an infinite-source theorem.

From the manuscript directory:

```bash
PYTHONDONTWRITEBYTECODE=1 python tools/build_formalization_module.py --check
PYTHONDONTWRITEBYTECODE=1 python tools/check_raw_exact_controls.py
PYTHONDONTWRITEBYTECODE=1 python tools/build_formalization_module.py --module strong_selectors --check
PYTHONDONTWRITEBYTECODE=1 python tools/check_strong_selector_controls.py
PYTHONDONTWRITEBYTECODE=1 python tools/build_formalization_module.py --module sir --check
PYTHONDONTWRITEBYTECODE=1 python tools/check_sir_controls.py
```

The module checker validates source and note anchors, full source-export
coverage, dependency closure and acyclicity, status vocabulary and the
generated index. The finite controls check the intended distinctions on
small represented structures. Lean import choices and compilable theorem
statements remain future implementation work.

Build a portable, deterministic handoff with
`python tools/build_formalization_handoff.py --output /tmp/CCO-Formalization-Handoff.tar.gz`.
Its file hashes and preflight commands travel with it. This is a source/work
package for a receiving project, not a claim that the imported theorems have
compiled Lean providers.

## Fourth module: sparse graphs, parity and full Hasse

[parity_hasse](parity_hasse/README.md) expands ten definitions, 26 claims and
seven source results. Its full labelled sparse-graph proof derives the tail
bound and gives explicit sufficient size inequalities, so no unexpanded
Erdős provider remains. Original orbital parity and full Hasse use no SAP or
RAW Helly. Relative closure separation and maximal gates are independent
consumers of RAW exact calculus. Only the quotient gate is an involution
graph; its real pullback can be nonfunctional.

SIR's I04 now links to this human-expanded provider. All four modules still
need Lean implementation. The private allocation template has seven planning
envelopes covering 106 claims; live public assignments remain governed by
`lean_cco/main`. Do not overwrite them with this preparation template.

## Fifth module: exact CRT and guarded quotient descent

[exact_crt](exact_crt/README.md) adds ten definitions, 24 claims, five numbered
results and two auxiliary source equations. The abstract commuting-equivalence
CRT, internal finite Birkhoff proof and MI-coordinate lemma are independent
of model theory. The actual exact-lattice instance separately imports RAW
products, different-centre exact-ball Helly and fine-colour readout.

Same-sort descent uses original commutation. Typed descent requires local
intertwining in the selected word presentation; its converse pullback needs
no intertwining. Empty words, empty restriction lists and nontrivial kernels
retain their own identities. No Hasse or selector input is used.

Five modules now contain 130 local proof claims and 47 numbered source
exports, plus two auxiliary equations. The private board has eight planning
envelopes. These preparation counts do not describe Lean proof progress or
change the active public B001 assignment. Canonical real-hull and closure
calculations remain separate preparation targets.

## Sixth module: actual real fibres and canonical hull

[canonical_hull](canonical_hull/README.md) adds fourteen definitions, 36 proof
claims and nineteen result exports. Five full source files give eighteen
results; the actual-fibre CCO lemma is an explicitly selected nineteenth
provider, without pretending to cover the remaining results in its file.

Fibre-closed supports (source exact for Z) are distinct from RAW word-exact
relations. Direct globalisation uses one internal Hasse cover and never
assumes that an intermediate fibre equivalence is already global. The
generic class interval is proved independently and applied afterward.
The unique lift is within [Id,E_T], not among all global equivalences.

An elementary finite Ramsey proof replaces the carrier's unnecessary
infinite-Ramsey invocation. Pseudocomplement and looped Helly lead to the
canonical hull bound without RAW exact Helly, exact CRT or SAP. The actual
one-point fibre can have two points while its canonical hull has four.

## Seventh module: real closure and original SAP geometry

[real_closure](real_closure/README.md) adds thirteen definitions, 34 claims
and eight result exports: all six results of `real_hull/06–07`, plus the
two selected terminal RAW-word/distributivity lemmas. Coordinate and phase
examples have independent proofs and controls. The palette-cost proof now
uses the already prepared actual exact-class Helly instead of Neumann;
F itself need not be exact.

SAP monolith and full-lattice MI reconstruction do not require symmetry or
CCO. Terminal words require symmetric original atoms and full NR2 but no
CCO or SAP; terminal distributivity and compatible incidence add the CCO
exact-geometry provider. These distinctions are enforced by DAG firewalls.

## Eighth module: finite-index packets and exact normalization

[finite_packets](finite_packets/README.md) adds ten definitions, 31 claims,
eight numbered source results and four auxiliary equations. The full
finite_packets section is expanded, including its twin-cell example.
Finite Ramsey replaces infinite Ramsey in the loop criterion. General
crossing index factorization is proved for commuting equivalences before
the minimal-cut H-identities are applied.

The square regularizer and thin translation group are elementary; full
exact quotient-source inheritance is used only in the two source consumers,
retaining its current countability premise. Thin finite packets and absence
of nonidentity finite-class exact kernels remain distinct conditions.

## Ninth module: rigid exact groupoids and phase seeds

[rigid_groupoid](rigid_groupoid/README.md) adds thirteen definitions, 31
claims, nine numbered exports and four auxiliary equations: all seven
rigid-groupoid results plus the explicitly selected simultaneous quotient
blocks and finite affine translate-Helly providers. Other results in those
two provider files are not implicitly covered.

Object identities are quotient kernels, not necessarily original logical
equality. Typed bridge descent retains exactness of the projected endpoint
gates as an explicit premise. Quotient exact convolution is derived from
proved quotient word Helly and actual Peirce, without a hidden reverse
descent or quotient-source inheritance step. Fixed-character phase seeds
are separated from constructing a character which detects a nonidentity
involution and from moving-owner finite projections.

## Tenth module: finite-fibre kernels and finite projections

[finite_kernel](finite_kernel/README.md) adds eleven definitions, 22 claims,
five numbered source exports and eight auxiliary equations. Together with
the previously selected affine lemma, the kernel/CSP source section is now
fully covered; two entire-named-axis/Goursat results are selected from the
simultaneous-quotient file without claiming its remaining results.

The global owner-kernel is identified by an explicit restriction/union
isomorphism. Countable finite projection and linear separation have full
internal proofs, independent of each other. Actual binding marginals need
not equal intrinsic fibre groups; finite projections need not be generated
by their surviving pair marginals. Relative owner homogeneity and full
homogeneous entire named finite sorts are separate positive hypotheses.
A genuine homogeneous S3 binary source shows that merely naming moving
owners can destroy homogeneity.

B017 is independent of the RAW/STRONG/phase mathematics after shared
representation acceptance. It does not provide actual exact-owner lifting.

## Eleventh module: actual finite owner providers and product actions

[owner_action](owner_action/README.md) adds twelve definitions, thirty claims,
six numbered exports and two auxiliary identities. It covers owner_master/01–03,
the complete finite-base provider file and the selected standalone point
lemma. Greatest finite packets, actual joint lifting and fine-colour meet
are reused through explicit foundational imports. Ordinary EPPA remains a
conditional input; the simultaneous master and rooted rank induction are
separate consumers.

Generic finite-base lifting, actual exact-source realization and abstract
product actions have separate hypotheses. The fixed-base corollary allows
arbitrary finite owner sets, while the full packet-closed provider uses
nonempty F_O-closed B. The nonnested target needs no T->O map; only the
nested product target needs that factorization. Its kernel proof does not
use C's point property, and sparse-source EPPA uses its independent exact
owner partial-map extension rule. No group section is assumed.

Eleven modules now contain 314 local claims, 102 numbered exports and twenty
auxiliary equations. Nineteen private planning envelopes include the
independent substantial B018 provider and B019 product/action packages.
B001 is now accepted; the current public protocol 2 queue controls later
claims. Further preparation after these modules:
the simultaneous owner master itself, then joint-owner/rooted consumers.
