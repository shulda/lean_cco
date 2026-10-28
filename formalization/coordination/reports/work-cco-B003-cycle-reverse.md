# B003 C12 orientation: reverse an actual specified simple cycle

Proof checkpoint `60a9356b3b6879b621925c2d7187215c44e83791` on local
`work/b003-cycle-reverse`, preserving the previous finite-simple-line and
cycle-helper history. Source pin, contracts, toolchain and manifest remain
unchanged. Implementation actor: `strong_bridge`.

`CycleIndexReverse` gives an ACTUAL finite reversal equivalence and proves
its precise successor/predecessor relation, including both wraps.
`SimpleCycle.reverse` keeps the genuine old vertex embedding, reverses
all traversal edges with the actual original typed converse, and remains
a genuine specified simple cycle. `cycleHom_reverse_iff` proves semantic
equivalence by dependent original-sort point transport plus BOTH the
diagram and source colour converses. `reverse_edge_endpoints` exposes the
reversed occurrence of every chosen edge at an explicit finite index.

Combined with the already proved rotation API, the new edge of a cut
cycle can be placed in either desired orientation before reading the
remaining genuine old simple path. This avoids assuming that arbitrary
endpoint-separated walks admit a legal recursive reversal.

All public modules are root-imported. Fresh local root build: **1026 jobs**,
green. Actual `import CCO` exposes the new reversal APIs in the SAME
audit environment; transitive audit checks **1798 CCO declarations**,
including private names, only `propext`, `Classical.choice`, `Quot.sound`.
Explicit reversal-theorem axiom print confirms that list. No new warning,
source premise, mathematical axiom or conditional provider is introduced.

This is source-free orientation support for the separate C12 formula
proof. It does not certify the full strict-simple-path identity or the
remaining C13 canonical converse. B003 remains **IN_PROGRESS**; remote
exact-head CI and genuinely non-author review remain required.
