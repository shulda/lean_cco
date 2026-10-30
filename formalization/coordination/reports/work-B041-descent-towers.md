# B041 one-sort descent and actual current-stage exact towers

Actual author: `/root/b041_simultaneous/descent_towers`. Source remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`; all source contracts, original
source TeX, accepted APIs, toolchain and dependency pins are unchanged.

The implementation uses accepted B008 descent machinery and B015 safe upward
pullback. Those are existing proofs, not newly allocated mathematical results.
The inherited Source/CCOBranch code in this helper branch is authored by the
B041 owner and private-CCO helper, respectively; this report claims no authorship
of those modules. Only the new Descent/Towers files belong to this stream.

## C01–C10, one original symmetric sort

`Descent.OneSort.invariant_symmetric` and `invariant_commute` discharge the
actual symmetry/commutation arguments using original pair flips. `word_pullback`
uses the actual projected old letters and the same literal quotient palette;
its word-intertwining certificates are proved from original homogeneity, never
passed as an extra premise. Empty words pull back to E; equality letters remain
logical identities. `saturation_formula` records TQ5 with the NONEMPTY whole
exact meet, including the top empty restriction list. `exact_descent` proves the
source statement on literal quotient carriers from precisely E;D;E=D. It removes
the unused, unjustified E≤D parameter of the older convenience wrapper by using
its already proved underlying theorem. No accepted API is edited.

`equivalence_descent` constructs the genuine induced quotient setoid for K≥E,
proves its exact relation equals the represented quotient image, and proves it
full exact. `Descent.Consumers.every_old_exact_descends` supplies all actual
identity-kernel data and saturation for ANY old nonempty exact D, including
old diversity relations which do not contain equality.

## C41–C49, actual finite towers

- `Towers.Flattening` defines the real pulled-back setoid F.comap(quotient J),
  proves J≤H, and constructs the canonical class bijection `[[x]] ↦ [x]` with
  literal commuting projection equations. `double_saturation` proves
  H;J;R;K;L=H;R;L from J≤H and K≤L for every old relation, including equality.
- `Towers.ExactKernel.totalExact` explicitly pulls each current exact kernel
  back using the accepted SAFE quotient-to-original theorem. `total_kernel_data`
  supplies full exactness and original containment. It never imports reverse
  descent. `Orbitals` proves full binary orbital preservation/reflection under
  the canonical flattening maps, with actual equivariant quotient actions.
- `AtomicIso` constructs bijections between actual diversity orbital predicates
  under equivariant carrier equivalences. `SourceIso.AtomicIso` additionally
  records a bijection of EVERY typed atomic palette and the exact optional
  colour equation. `atomicIso` constructs it from actual realized colour
  partitions, rather than assuming a palette identification.
- `ExactTower.Stage` stores actual current source data. A concrete `StepData`
  contains only the chosen current setoids, their nonempty full exact word
  presentations and their literal representation equalities. `Stage.quotient`
  DERIVES countability, homogeneity and semantic HOM CCO using the owner’s actual
  source theorem and the independently proved typed private-path CCO theorem.
  No later source-property, descent, rank, AP, section or flattening provider is
  a tower constructor argument.
- A finite `ExactTower` has a genuine zero constructor and recursively takes
  quotients of its CURRENT source. `pullExact` and `pullExact_relation` explicitly
  lift every final menu through all stages. Pulling back final equality gives
  `totalExact` and `totalExact_represents` for the original total kernel. The
  final projection is onto and its canonical class flattening commutes with
  original projection. Zero-stage source/projection/kernel are actual
  identities. `final_properties` and `final_cycles_general` retain the standing
  properties, including unrestricted formal finite vertex universes.
- `TowerGeometry` proves equivariance, every full binary orbital correspondence,
  and an actual `structureIso` preserving optional atomic colours with bijective
  names. `InitialSource` supplies entry from an arbitrary original atom universe
  (not just the uniform universe used for recursive later stages), explicit
  original total exact presentations, canonical original class flattening, and
  the complete `initialStructureIso` to one direct simultaneous original quotient.
- `Rank` constructs a quotient-diversity-to-old-diversity injection from actual
  real witnesses and original pair homogeneity. A distinct pair swallowed by a
  current kernel witnesses an old diversity atom outside its image. Every typed
  palette weakly decreases, that same-sort palette strictly decreases, and their
  finite ordered-palette sum strictly decreases. The convention counts ordered
  typed diversity atoms throughout; equality is never counted. `kernel_ne_bot_iff`
  verifies that swallowed-pair formulation is exactly nonidentity of a setoid.
  `CanonicalRank` supplies the literal quotient source instance. `TowerGeometry`
  proves total finite-tower rank≤ and rank< if ANY current step is nonidentity;
  `InitialSource.initial_rank_lt` includes the arbitrary original first stage.
- `Towers.Consumers` constructs an actual two-stage current exact tower. It
  checks the literal nested class equation, supplies an explicit original full
  exact presentation of its total kernel, constructs the actual complete atomic
  isomorphism, and checks the genuine zero stage. `FiniteChain` separately proves
  canonical class flattening for arbitrary finite chains of setoids without any
  source, group or exactness assumptions.

Countability in the Stage record is the original standing source hypothesis,
used by joint homogeneity and derived at every subsequent quotient; it is not
an added exactness or capacity premise. All local wrappers preserve empty sort
families, empty words/restriction lists, top/equality kernels, repeated sorts,
and noninjective semantic homomorphisms. No mixed-sort reverse descent,
commutation of typed cross arrows, quotient SAP or group section is asserted.

## Local validation

Exact pinned local Lean/Lake via `runtime/env.sh`, no source or configuration
change: the narrow Descent consumer build passed (897 jobs in its dependency
closure); the finite-tower/actual two-stage consumer build passed (1017 jobs in
its dependency closure). The independent generic FiniteChain and Orbitals
modules also compiled in their earlier narrow builds. These are Lake closure
sizes, not counts of newly compiled modules. No duplicate whole-project build,
Python suite, axiom audit or remote CI is claimed by this helper.

A concrete local generated-artifact inconsistency occurred while extending
Rank: Lake reported the newly changed module built and emitted new-source
warning line numbers, but Rank.olean retained the previous timestamp/bytes and
`#check kernel_ne_bot_iff` could not see the newly introduced theorem (nor its
new Setoid import). Both local artifact-cache settings remained false. Only
this helper’s OWN generated Rank outputs were moved aside to
`runtime/b041-stale-rank`; one targeted consumer rebuild then succeeded and
produced the new Rank.olean (246880 bytes). The original outputs and logs remain
preserved. The final consumer’s separate true mathematical repair used
`Quotient.eq` to identify its composed projection kernel with F.comap(quotient J).
This report does not claim a general cause or a global cache fix.

Public exact-head CI/audit, independent review and accepted-main integration
are owned by root and remain separate final gates.
