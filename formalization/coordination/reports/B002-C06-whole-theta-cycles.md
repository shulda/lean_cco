# B002 C06 — literal whole-theta cycle classification

Implementation commit: `7671e4bccdecf4435c06ac49da960d2644ac2827`, branch
`work/B002-cycle-classification`, over public B002 checkpoint
`0f366f0a539c020a7a80f822a830f6db25c11ffa` and generic cycle-edge leaf
`d270cd0` (history-preserving equivalent of raw_fan's `a8c7f04`; only the
additive root-import conflict was resolved). This report changes no proof.
All original B002 WIP/history is preserved. B002 remains IN_PROGRESS;
this report does not assert completion of C26/C27 or the whole package.

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Exact contract `raw_exact.C06`, proof note N03, source
`thm:full-typed-exact-balls`: private paths for finite nonempty pairwise
compatible same-endpoint word profiles, merged direct edges, and every
simple cycle is two private paths with an original-source homomorphism.

## Actual construction and semantic witness

The existing `WordThetaSource.lean` supplies the actual typed singleton-menu
word theta (`wordThetaMenus`, `wordThetaOccurrence`, literal far endpoints)
and `wordTheta_cycleHom_of_pairwise`. Its source homomorphism hypothesis is
pairwise actual RAW profile intersection, and no CCO or global Helly result
is used to supply individual cycle witnesses. Existing fan edge/reference
and direct-colour consistency modules supply the source-atom labels and
merge repeated direct edges. The new result completes the separate literal
whole-cycle classification; it does not replace it with Helly existence.

## New source-to-Lean map

- `SimpleCycleDegreeTwo.lean` is raw_fan's shared generic leaf:
  `CycleVertex` means a vertex literally appears in the injective cycle
  enumeration; `CycleEdge` means an actual traversed unoriented edge.
  They do not merely assert that two points lie in the vertex support.
- `WordThetaCycleClassificationPaths.lean` adapts raw_fan's whole-path
  propagation to the existing PrivateFan API. If one genuine interior is
  on a cycle, **every position and every edge** of that original occurrence
  is on that same cycle. It uses the shared genuine degree-two edge lemma.
- `...Support.lean` proves `privateFanFull_support_iff`: the actual full
  typed source diagram has exactly the private fan graph as support,
  including both orientations of every root spoke. This requires no
  pairwise intersection or CCO/Helly hypothesis.
- `...Incidence.lean` proves the actual incoming/outgoing root edges
  exhaust all cycle edges at the root. A one-centre fan cycle must contain
  a private interior, since a simple cycle has at least three distinct
  vertices whereas the terminal-only carrier has at most two.
- `...Branches.lean` handles a selected first edge. Length one is its
  literal merged direct edge; length at least two invokes whole-path
  propagation. No path is assumed injective in the real source.
- `...Choices.lean` constructs the two actual root-incident occurrences
  and proves they differ. Every private occurrence met elsewhere on the
  cycle is one of these two, by its forced first edge and root incidence.
- `...Exhaustion.lean` proves
  `privateFan_one_centre_cycle_two_whole_paths` for any partial diagram on
  this fan carrier whose actual cycle edges are graph edges. It gives two
  distinct positive whole occurrences and **iff equality of both the
  entire cycle vertex support and its entire traversed edge support**
  with the union of those two literal paths. This intermediate is fully
  proved, not an open provider or a graph-shape assumption.
- `WordThetaCycleClassification.lean` instantiates that theorem on the
  actual `privateFanFullDiagram` for `wordThetaMenus`.
  `wordTheta_cycle_two_whole_paths` returns two **distinct original family
  indices** t,u, their positive reduced lengths, and the exact vertex and
  edge iff statements using `wordThetaPathVertex`/`wordThetaPathEdge`.
  Singleton menu slots are explicitly exhausted, so different slots are
  not mistaken for different original indices.

The conclusion classifies the literal unoriented cycle support as two whole
terminal-to-terminal paths; `SimpleCycle` already gives the injective cyclic
order. It does not add an unused rotation/orientation enumeration interface.
The actual CycleHom and the complete shape result concern the SAME concrete
theta diagram and cycle. Under the contract's pairwise compatibility input,
both are supplied by proved source theorems, without a conditional provider.

## Identity, duplicate and boundary cases

The proof does not assume all input words are positive. Only diversity
letters contribute positions/edges; logical identity letters are suppressed
by the established `diversityLength`/`PathPosition` API. A cycle chooses two
positive occurrences itself. `wordTheta_no_cycle_of_subsingleton` handles
empty and singleton families. `wordTheta_no_cycle_of_short_words` excludes
cycles for arbitrary families of zero/one-diversity words, including repeated
merged direct edges. The formal terminals are distinct; their real images
may coincide in RAW homomorphisms, as required by identity outputs. No fake
STRONG equality atom or SAP is introduced.

## Validation

Pinned Lean/Lake 4.34.1 and manifest unchanged. All seven new public modules
are exported from CCO.lean. Full local `lake build` succeeded, **989 jobs**,
including rebuilding the six public joint-lifting modules missing from the
initial isolated cache. This is a full project build of this exact source
checkpoint, not merely a check against imported cached signatures.
The official transitive root axiom audit succeeded for **1,660 CCO
declarations**, zero violations, only `propext`, `Classical.choice`,
`Quot.sound`. No broad Mathlib or tactic import was added.

The exact implementation SHA was sent to the independent non-author reader.
Remote CI and independent approval for a later combined PR3 head are separate
requirements; no stale CI run is reused here. C26's literal two-whole-path
case can reuse this graph result after a proved transfer of its single-edge
cycle, and remains outside this checkpoint until that transfer is supplied.
