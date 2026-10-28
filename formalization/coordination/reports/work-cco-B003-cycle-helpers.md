# B003 C12 support: actual cycle rotation and unique unordered edges

Proof checkpoint `a26722a540fad49057d392fa4359fb895fe59502` on local
`work/b003-rotation`, extending C09 and PCExactness through `67f4533`.
The original source pin, mathematical contracts, toolchain and manifest
are unchanged. Implementation actor: `strong_bridge`. This checkpoint
supplies source-free finite-cycle helpers requested by the independent
C12 implementation; it does not claim the remaining C12 theorem.

`CycleIndexRotation` constructs an ACTUAL equivalence on every positive
finite cyclic ordinal, given by repeated cyclic successor from the chosen
start. It proves successor commutation, zero readout and the precise
last-index identity when the start is chosen just after a cut edge.
`SimpleCycle.rotate` preserves the actual original vertex embedding and
all specified typed atomic edges. `cycleHom_rotate_iff` transports dependent
original-sort point families by `Equiv.piCongrLeft`; it does not identify
sorts or assume any homomorphism. Explicit root/cut boundary lemmas expose
the chosen edge as the literal closing last-to-zero edge.

`CycleEdgeUniqueness.unordered_edge_unique` proves that every unordered
formal edge of a genuine simple cycle occurs at only one cyclic index.
The forward case is vertex-embedding injectivity. A reversed repetition
would be a two-step cyclic return; finite successor injectivity at indices
2 and 0 contradicts the mandatory cycle length at least three. Wrap edges
are included. No artificial two-cycle is inserted or silently counted.

Full root local build: **1024 jobs**, green. The same environment's explicit
`import CCO` checks expose both new helper APIs, C09 and PCExactness.
Transitive audit: **1734 CCO declarations**, including private names,
only `propext`, `Classical.choice`, `Quot.sound`. Explicit helper axiom
prints confirm that allowlist. New modules emit no warnings. The earlier
local boundary-index elaboration experiment is preserved in history;
its two errors were corrected before this validated final checkpoint.

C12 chosen-survivor/simple-path equality and C13 converse canonical-family
and canonical-three-root classification remain open. B003 is still
**IN_PROGRESS**. Exact-head remote CI and genuinely non-author review are
required before any package submission/integration; neither is invented
by this local report.
