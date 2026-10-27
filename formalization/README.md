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
The direct relative-two-sheet example is independent of NR2/HS. No Lean
declarations have been written in this repository.

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
