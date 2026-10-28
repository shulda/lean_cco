# Third active batch: B008

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Current accepted main: `21381f6095d3b2787e3e248e5ea244180a66f06f`, actual main
CI 40719464681, successful build and 4709-declaration allowlist audit.
Observed live STATE revision 44: B005 and B007 IN_PROGRESS, all their
prerequisites ACCEPTED and ancestors of current main; no repairs or lock.

The author explicitly authorized up to three simultaneous batches when useful.
B008 is the lowest released dependency-ready available package. Its only
prerequisite B002 is ACCEPTED at 4206ff772cc3ee334fe530b55dbb0afe8174dfd4,
an ancestor of current main. No submitted or unaccepted sibling API is used.

At this allocation checkpoint both actual branch heads are the current main
21381f6095d3b2787e3e248e5ea244180a66f06f; neither claim has a later public WIP
head. The active allocations are:

| Batch | Implementers | Active work and owned files |
| --- | --- | --- |
| B005 | /root/b005_positive, /root/b005_positive/direct_model | Actual finite selected-span SIR C01–14, independent real two-sheet model C20–25; CCO/SIR/Positive/ and B005 report/consumer |
| B007 | /root/b007_relative | Relative exact closure separation, maximal exact gate and actual quotient C15–26; CCO/ParityHasse/Relative/ and B007 report/consumer |
| B008 | /root/b008_crt, optional its dedicated abstract helper | Abstract finite equivalence CRT, distributive/Birkhoff coordinates, actual exact-lattice and guarded quotient descent C01–24; CCO/ExactCRT/ and B008 report/consumer |

These mathematical implementations have disjoint directories and no dependency
on each other's new results. Each author owns compilation in a separate
worktree and writable project-build directory, reusing only already accepted
dependencies. The packages may be read concurrently from the immutable
mathlib installation. A single root publisher combines only additive root
imports and serializes all actual merges under the existing sole lock.

B008 has a dedicated live implementer, an immediate substantial proof DAG,
and an optional separate helper for its abstract lattice branch. It is active
work, not a backup reservation or a slot freed by submission. Root coordinates
and can implement small disjoint helpers, while /root/independent_review remains
an actual non-author control-only agent for one final whole review per package.
No policy, capacity maximum, contract or accepted-dependency rule is changed.
