# B047 actual finite marked tuple realization and fixed bases

Author `/root/b047_strong_phase/tuple_readout`; source pin
`490c3f36d85db5a0b3ced0598e6c431825254ec5`, effective claim379, base
`bfbf8cf83d590d8d13499ab0e33aa8ea6445eb97`. Scope is
`CCO/PairSafeSplit/Strong/Realization*.lean`. These source-construction
lemmas support the C34–C36 readout and the actual marked SAP proof; they do
not assume either old or marked SAP.

`global_marking_of_legal_tuple` uses the actual `SourcePhase` finite seed
extension for any finite ordinary indexing type. `embed_legal_tuple_limit`
then embeds the actual finite-image chart of that marking into the whole
B044 marked limit. Its quotient carrier retains all repeated tuple points
and every optional old pair colour, including equality. No injectivity of
the supplied tuple, homogeneous seed marking, or new age provider is a
premise. `embed_legal_tuple` transports this construction through the exact
`UnarySource.newEquiv I` into `UnarySource.source I`, with literal old
sort/bit names and full tagged optional colours.

`align_legal_tuple` applies the proved whole-limit finite homogeneity after
recovering the complete equality pattern from tagged colours. It places a
legal tuple over an already specified finite base tuple and preserves that
base exactly, even when tuples or indexing maps repeat. Its embedding
specialization `extend_legal_embedding` derives injectivity from the actual
old induced embedding and supplies the fixed-base finite extensions used
by the separate marked SAP proof.

`RealizationAtoms.lean` proves that an old atom occurs between two actual
child sorts exactly when their endpoint mask allows it. The forward proof
uses the actual source global marking. The reverse proof realizes the old
atom in the original source, verifies both directed pair masks and both
diagonals, and applies the finite tuple construction. This is an actual
source occurrence theorem, rather than formal prefix support alone.

`RealizationTriangles.midpoint_readout` takes fixed actual child endpoints,
an old midpoint of the specified parent sort, and the two allowed optional
pair masks. The endpoint mask follows from the actual source marking.
It verifies the entire three-point legal table, including all reverse and
diagonal entries, and applies `align_legal_tuple` over the two fixed
endpoints. The result is an actual midpoint in the specified child sort
with both original optional colours preserved. Repeated endpoints or
midpoints are allowed. The helper `allows_pair_reverse` treats actual
equality via the identity mask, rather than turning equality into a
diversity atom.

Validation: pinned Lean4.34.1/Lake5 with the repository manifest, private
project/provider outputs and immutable shared dependencies. Narrow
`lake build CCO.PairSafeSplit.Strong.Realization` passed (2479 jobs), then
`lake build CCO.PairSafeSplit.Strong.RealizationAtoms` passed (2480 jobs).
`lake build CCO.PairSafeSplit.Strong.RealizationTriangles` also passed
(2480 jobs, first compile).
Logs are `runtime/b047-tuples-final.log` and
`runtime/b047-tuple-atoms.log`, plus `runtime/b047-tuple-triangles.log`,
outside the Git worktree. Existing style
warnings are nonfatal. No shared import edits, whole-project build, remote
writes, new axioms, `sorry`, new-source SAP assumption, or reviewer-authored
code. The owner retains assembled exact-head build, CI and axiom audit.
