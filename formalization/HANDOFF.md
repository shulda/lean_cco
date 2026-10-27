# Work order for receiving Lean projects

These notes originate in the manuscript preparation repository. **Other
projects implement Lean.** Do not create a Lean project, toolchain or CI in
that source manuscript repository. In the separate public receiving repository,
Project 1 creates them as part of B001. The bound board and package identify
the receiving destination; a source snapshot by itself is not an activation.

**Receiving-project allocation:** read the [peer-project launch plan](coordination/README.md),
[protocol](coordination/PROTOCOL.md) and [board](coordination/BOARD.md).
Projects have numbered identities, one substantial assigned package each,
and report completion or blockers to the author. This preparation project
owns allocation; no permanent master formalizer is required. B001 tests
the shared API and the coordination process before parallel projects start.

Start with the three source-linked modules:

| Module | Main exports | Prerequisites within this preparation |
|---|---|---|
| [RAW exact](raw_exact/README.md) | Word/ball Helly, exact convolution, actual quotient orbitals and joint ambient lifting | Actual represented homogeneous CCO source; no SAP |
| [STRONG/PC/selectors](strong_selectors/README.md) | SAP injectivization, strong exact calculus, finite PC semantics and named-sort HS | Separate SAP/CCO/NR2 premises; not RAW exact-ball Helly |
| [SIR](sir/README.md) | Selected-amalgam SIR, original-language finite-global obstruction and direct relative-two-sheet example | Positive route consumes STRONG exports and triangle fullness; the negative route separately imports full relative Hasse |

Each module has literal source locators and hashes, definitions, local
claims, a directed dependency graph, a complete source-export map and
implementation task assignments. Read its `PROOF_NOTES.md` as well as the
index; the graph alone is not a proof.

## Initial instructions

1. Check the package manifest and run its Python preflight. These validate
   source identity, metadata and finite controls only.
2. Read the substantial package assigned to your project ID in
   `coordination/BOARD.json`. Module `T` tasks and individual claims are
   internal milestones, not separate project assignments. Inspect the actual
   source proofs and provider contracts. Source labels are stable mathematical
   identifiers, not existing Lean declaration names.
3. Choose Lean representations in the receiving project, compile precise
   statements, and prove the elementary conversion lemmas there. No proposed
   namespace, structure or import in these notes has been compiled.
4. Prove downstream conditional results against explicit provider parameters
   if an upstream proof is not yet available. Keep such parameters visible
   in the resulting theorem. Do not replace the source assumptions by an
   opaque axiom, or count an unproved provider as certified mathematics.
5. Instantiate a source-level headline only after its actual provider
   contracts have been proved and connected. Report conditional proof status
   separately from the instantiated theorem status.

After the shared B001 API is accepted, the RAW and STRONG foundational
streams can be assigned independently. Within STRONG,
finite PC semantics and visible-gate calculus are separate consumers of the
exact calculus. SIR has three separately assignable branches: the positive
conditional constructor, the negative finite-global obstruction, and the
direct relative-two-sheet example. That example violates NR2 and cannot be
obtained by invoking the NR2 selector theorem.

## Interpretation rules that must survive translation

- RAW multiplication is actual relational composition with equality. STRONG
  multiplication uses three distinct real vertices. Never adjoin a logical
  equality atom to a STRONG diversity palette.
- An empty word is RAW Id; an empty restriction list is Top. Strong words
  are positive. Absent multipliers in no-return are identity actions.
- A nonempty exact meet means that its evaluated intersection is nonempty.
- Name all actual pair orbitals on actual quotient carriers. Joint lifts
  assert existence of an original automorphism, not a coherent group section.
- NR2 is checked in the FULL original invariant-equivalence lattice in
  each named sort. A nontrivial pure-tag selector engine keeps its additional
  no-return premise; arbitrary fine-colour permutations are not allowed.
- SIR types fix parameter sets pointwise. Normalize finite sets by adjoining
  their base before evaluating base-path menus. Selected-amalgam naturality
  requires the source base to map ONTO the entire designated target base.
- The global finite-quotient obstruction is in the original one-sort real
  language. No naming of finite sheets or quotient homogeneity is permitted
  as a silent replacement of its hypotheses.

## Required return from a receiving project

Return a small ledger keyed by module/claim/source label, containing:

- actual repository, commit, Lean version and compiled declaration names;
- exact hypotheses and quantified conclusions, with any conditional providers;
- proof status and the validation actually run;
- representation choices that another receiving project must share;
- mathematical repairs, counterexamples or useful simplifications, with
  affected callers and a proposed human-article correction;
- encoding-only lemmas, identified as such so that they stay outside the
  human article.

Do not rewrite the human TeX to mirror Lean implementation structure. Send
mathematical discoveries back through the module's `article_feedback` ledger.
The present notes include independent model reviews, not independent human
or Lean certification. A receiving project remains responsible for checking
that its statements express the intended mathematics.

## Packaging and preflight

From this manuscript directory:

```bash
python tools/build_formalization_handoff.py --output /tmp/CCO-Formalization-Handoff.tar.gz
```

The deterministic archive contains the three modules, their pinned source
files, provider source snapshots, declaration metadata and Python checks.
It is a focused source snapshot, not a compilable copy of the whole article.
Read the included `HANDOFF_MANIFEST.json`, then run:

```bash
python tools/build_formalization_handoff.py --verify .
python tools/build_formalization_module.py --check
python tools/build_formalization_module.py --module strong_selectors --check
python tools/build_formalization_module.py --module sir --check
python tools/check_raw_exact_controls.py
python tools/check_strong_selector_controls.py
python tools/check_sir_controls.py
python tools/check_formalization_coordination.py --check
```

The declaration catalogue contains contextual entries for the wider manuscript;
only files explicitly listed in the manifest are supplied. In particular,
the SIR Hasse input is an explicit upstream obligation, not a fourth fully
expanded foundation module hidden in this package.

The full hash manifest records the initial snapshot. Verify it before the
first implementation edits. Later legitimate board/report/README changes
need not match those initial hashes. Ongoing validation uses module source
pins, the coordination checker and the Lean build. Do not regenerate an old
manifest to conceal a mathematical source change. The
[coordinator runbook](coordination/COORDINATOR_RUNBOOK.md) explains recovery
and the single live public allocation record.
