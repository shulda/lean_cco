# B048 actual typed source reconstruction from whole pair names

Author: `/root/b047_pair_safe_split/infinite_type_fibres`.
Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`; B048 public claim STATE388.

The disjoint helper `Full/SourceIso.lean` provides exactly the source data
interface requested by the full source transport author. `SourceIso T S`
contains an actual sort equivalence, equivalences of real point fibres,
equivalences of realized diversity atoms, and equality of all interpreted
optional colours after those atom maps. `SourceIso.whole` is the resulting
whole-carrier equivalence, with literal `whole_apply` and `whole_sort` laws.

`mapColour` is injective, and `whole_tagged_iff` proves exact preservation AND
reflection of the equality partition of all tagged optional colours.
`atom_conv` is derived from actual realized pairs and the colour swap laws;
converse compatibility is not an additional field or premise.

The main constructor `SourceIso.of_pattern e h` recovers all typed data from
ONLY an actual whole-carrier equivalence e and the proved equivalence of the
equality partitions of all actual tagged colours. The construction:

1. Identifies real unary sorts by their diagonal tagged-colour classes.
   Inhabited source sorts and surjectivity of e give a genuine sort bijection.
2. Restricts e to actual point-fibre bijections, using that recovered sort map.
3. Reindexes the target AtomicSource along the sort bijection and reuses the
   accepted `SimultaneousQuotients.Towers.atomicIso` realized-atom construction.
   Equality is retained through the carrier bijection; no diversity atom is
   substituted for logical identity.
4. Proves `of_pattern_whole e h`: the resulting whole equivalence is literally
   e, so the actual full-reduct/pair-prefix comparison commutes as required.

The independent tuple author constructs the actual e+h source instance.
The full source transport author separately handles SAP, semantic CCO, rank
and invariant transport. No such conclusion is assumed in this helper; no
prefix model/history, palette equivalence or principal provider callback is
introduced as a new premise.

Native compiled checkpoints:

- `251f3d23f0eb57cbe012442c535b6429559fcc9d`: SourceIso fields/whole,
  exact tagged-colour transport/reflection and realized converse compatibility.
- `4bac8ae4bd452c3b1de13254e8e101f9c2c59c5e`: actual of_pattern constructor
  and exact whole equivalence law.

Narrow validation `lake build CCO.FullPhaseLift.Full.SourceIso` succeeded
with 749 jobs on pinned Lean4.34.1 and the unchanged manifest/private outputs.
Only this file and this report are authored; prior canonical, unary-expansion
and marked-pairSAP branches are preserved. Root owns assembled build,
exact-head CI/audit and all remote coordination/publication. No axiom/sorry.

The terminal-prefix seam additionally provides `SourceIso.symm`, `trans`
and `compose`, each reconstructed by the proved `of_pattern` constructor.
The equations `symm_whole`, `trans_whole` and `compose_whole` identify their
whole-carrier maps literally with inverse/composition of the supplied maps.
This avoids any additional dependent-coherence/history assumption. The same
narrow target passed with 749 jobs.
