# B063 C32–C38 actual identity-gate helper checkpoint

Actual implementation helper `/root/b053_resume/b063_loopless`.
Owned source `CCO/AutomaticEPCore/IdentityGate.lean` only.
Source SHA256 `780eb2820b3c2ea48b6e8543870cbdde38d27676930651d16627890b5a6a734b`.
Pinned Lean4.34.1 private direct compilation passes with NO diagnostics;
log `/workspace/scratch/d821f7d92465/b063-identity-check.log`, private
output `/workspace/scratch/d821f7d92465/b063-identity-check.olean`.
No shared root imports/build output, commit, push, report or coordination
record was written by this helper. TerminalLoopless remains unchanged.

## Exact proof/API map

All declarations are under `CCO.AutomaticEPCore`.

- `identity_even_atom_square S H c hEven x y` proves the actual symmetric
  old diversity atom squares to literal real identity when its ACTUAL
  full even-walk equivalence equals bottom.
- `identity_even_atom_functional S H c hEven` constructs the original
  equivariant permutation from the UNIQUE actual c-neighbor of every
  real point. Its inverse is the same function, it is nonidentity, and
  `S.atomRel c x y ↔ h.val x = y` holds on the entire old sort.
- `identity_maximal_gate_functional S H c Y U hY hU maximal` starts with
  genuine `ExactEq` Y and FULL `ColourEq` U, original parity equalities,
  and maximality of bottom among ALL `OriginalGateCandidate` exact
  complements. Maximality first implies Y=bottom, hence even(c)=Id.
  The constructed actual involution makes c bipartite, giving the actual
  FULL parity cover. Every positive exact E either meets U in Y (which
  would contradict bottom maximality) or contains U. Thus the SAME
  actual functional graph is contained in EVERY positive FULL EXACT E.
  U itself is never assumed exact. No source NoOdd premise is added.
- `leastPositiveExact A i` uses the actual
  `ExactEq.completeLattice A.source A.homogeneous A.cco i` and is
  `sInf {E : ExactEq A.source i | bottom < E}`. It is not declared
  positive until a real identity step supplies the needed witness.
- `leastPositiveExact_le` proves leastness among positive EXACT relations.
  `leastPositiveExact_iff` identifies its entire pair relation with the
  literal intersection of ALL positive exact relations. The proof
  enumerates the genuine finite `ExactEq` type and identifies sInf with
  the accepted literal `originalExactGateMeet`, not an arbitrary
  invariant meet or a lattice of selected names.
- `functional_graph_in_leastPositiveExact` places EVERY original
  functional graph contained in every positive exact E into this SAME F.
  `leastPositiveExact_pos_of_functional` derives F>Id from one actual
  nonidentity such graph. F may be Top.
- `functionalSubgroupInside S F` consists of actual original functional
  permutations h with `forall x, F x (h x)`. Closure follows from the
  actual equivalence laws of F. `functionalSubgroupInside_normal S H F`
  uses the proved original functional group's abelianness.
  `functionalSubgroupInside_nontrivial` supplies actual nontriviality
  from a real nonidentity graph in F.
- `original_gate_identity_or_leastPositiveExact A i E` proves that every
  actual FULL EXACT gate E is Id or contains F; it does not quantify
  over nonexact invariant equivalences.
- `certifiedStepOriginalPivot A base hOne step` is the literal old atom
  `s.reduct.atom choice.p choice.p choice.c`, with choice taken from
  THAT `Step` certificate and transported ONLY along the actual unique
  original-sort equality to `base`.
- `certified_identity_step_functional A base hOne step identityGate`
  discharges ALL source inputs of the generic maximal-gate theorem from
  the SAME `Classical.choose step : GateChoice s`, its maximal_old,
  old_even, old_connectivity and the hypothesis that its actual
  `certifiedStepOriginalGate` equals bottom. It returns the actual pivot
  functional h, nonidentity, full graph biconditional, graph inclusion
  in every positive exact E and in F, and F>Id.
  It is UNIFORM over every genuine identity step in the SAME original A.
- `leastPositiveFunctionalSubgroup A i` is the canonical H_F at that
  original source, independent of which identity step proved positivity.
  `certified_identity_step_least_exact` packages actual F positivity,
  exact leastness, H_F nontriviality and H_F normality, with no abstract
  source provider left to assume.

## Important retained phase-selection receiving boundary

The ACTUAL `GateChoice` stores a current original pivot c and a maximal
kernel M. Its `phase` is typed at that SAME kernel but has its OWN
`phase.odd`, `odd_dominant` and `detects=1`. There is NO field equating
`phase.odd` with `MaximalGate.oddArrow`, or saying that the initially
stored c itself has character one.

The implemented identity-step theorem therefore uses stored c only for
the honest positivity witness for F and claims NO character value for it.
The later step-specific u_i used to flip children in C46–C48 must instead
be selected from the ACTUAL phase.odd / full original bridge and its own
actual detects certificate. Parent has identified
`actualPhaseAtSort_maximalGate` as the reconstruction provider retaining
containment in the actual phase odd arrow; it will preserve that seam
in the prefix-action assembly. No source/API change is required by the
proofs delivered here, and no false detects assertion was inserted.

All original-source finite/zero-stage and AP-only distinctions remain.
There is no SAP or infinite-source input, no relation between this exact
F and the finite-packet hull or arbitrary invariant least equivalence,
and no change to a frozen source or accepted API.
