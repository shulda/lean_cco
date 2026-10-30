# B043 actual boundary sources — C23, C24, C26

Actual implementation author: `/root/b043_point_sap/boundaries`.
Source contract: `point_generated_sap`, frozen article `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
No source contract, accepted API, toolchain or dependency pin is changed.

## Actual source and consumer map

- `CCO/PointGeneratedSAP/Examples/Matching.lean`: actual countably infinite
  pure real set Nat and disjoint hidden matching copy Bool×Nat. The ONLY
  unary symbol maps each real to its hidden partner and acts by identity
  off its input sort. Actual well-sorted terms include no hidden-to-real
  inverse. Full real closures are precisely both copies of the original D.
  Every original Nat permutation lifts, and EVERY full expanded
  automorphism is proved to be induced by one unique original permutation.
  Finite original induced injections extend by the accepted finite
  permutation-extension theorem. Actual full stabilizer orbits are infinite
  on either copy outside a finite real-generated closure, including D empty.
  The hidden singleton is closed but is not point-generated. An ACTUAL
  hereditary age SAP span over this orphan base is impossible: preservation
  of the named bijection forces the two real preimages to coincide.
- `MatchingSource.lean`: instantiates the owner's literal `Original` and
  `Interpretation` structures, including its FULL original permutation
  subgroup and genuine homogeneous real reduct. Conjugation along the
  literal original-real-carrier/Nat bijection defines the canonical group
  lift; finite real closure and generation are proved. The actual PGO
  instance uses that SAME original group, with a proved inclusion from the
  literal expanded orbit after the full automorphism characterization.
  The owner's actual proved generic iff yields point-generated SAP. Thus
  C23 separates two actual categories rather than two assumed providers.
- `Constant.lean`: actual infinite pure real Nat with ONE hidden singleton
  and one constant UNARY map, with no nullary symbol. Closures are computed:
  the singleton occurs exactly when D is nonempty. All nonempty real bases
  pass the off-closure orbit test, while the hidden point has singleton
  orbit outside the empty closure. A genuine finite point-generated pair
  has no two disjoint induced copies in ANY actual finite induced target.
- `ConstantSource.lean`: constructs the same FULL-original-Aut canonical
  interpretation and proves its original homogeneity. The nonempty-base
  orbit test is proved directly in the EXACT original group of the generic
  theorem. Its empty orbit is literally a singleton, PGO fails and an actual
  point-generated empty-base span directly refutes SAP; no use of the
  generic converse is required for this failure.
- `Binary.lean`: actual binary operation on Fin3 with independently closed
  singletons {0} and {1}; their generated union contains 2. The generated
  closure is an inductive least closed set. This proves failure of the
  unary closure-union equality for mixed-input generation (C24).

No CCO, symmetry, countability assumption in the generic theorem, global
hidden homogeneity, replacement subgroup, finite surrogate for infinite
orbits, sorry/admit or mathematical axiom is supplied by these consumers.
Concrete example carriers themselves are explicitly countable/infinite.

## Verification and isolation

Exact runtime Lean4.34.1/Lake5 and unchanged receiving manifest were used.
Narrow model build Matching+Constant passed1335jobs; Binary passed373jobs;
actual source-consumer build ConstantSource+MatchingSource+Binary passed
1342jobs. After refreshing all seven generic owner dependency files to
committed `4ba8c3497ec4a05323ef84a15019524554649cfc`, the FINAL combined
MatchingSource+ConstantSource+Binary target passed1345jobs, including the
complete source iff and both actual consumers. The final MatchingSource compile uses the complete owner iff
rather than only its forward implication. Owner generic dependency files
were private untracked source copies solely for compilation, never staged
or committed by this helper. No broad project build, test suite, audit or
GitHub mutation was run; the package owner controls final root imports and
whole-project exact-head/main evidence.
