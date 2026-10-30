# B047 actual marked SAP: C22–C33

This is the owner's proof report, not an independent review. It records the
actual marked-age bridge built on accepted main
`bfbf8cf83d590d8d13499ab0e33aa8ea6445eb97`, with frozen mathematical source
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. No contract, accepted API, pin,
manifest or compiler setting is changed.

The principal theorem is
`CCO.PairSafeSplit.SAP.unary_source_sap P cco I sap`. Its target is precisely
`APCharacter.SourceAge.UnarySource.source I`, where `I` is the proved B044
identification of the original reduct with the actual marked Fraïssé limit.
In particular it specializes to the exact B044
`SingleStep.identification B P` and the source of `SingleStep.successor B P`.
Its only SAP premise is `sap : AgeSAP S` for the original source.

## Proof direction

1. `Infinity.finite_invariant_subset_base` derives absence of finite real
   stabilizer-invariant sets off a finite base from original SAP.
   `finite_formulaSet_subset_base` additionally realizes the corresponding
   arbitrary-depth named first-order formula statement. Actual finite
   spoke formulas `typeFormula` and `tupleTypeFormula` define the entire
   realized one-point type, including repeated and empty parameter tuples.
2. `SAP.kernel_ne_identity` shows that an actual nonidentity self-arrow
   cannot have original equality as its full kernel. If the kernel were
   equality, the arrow would assign a unique distinct real point fixed by
   the singleton stabilizer, contradicting old SAP. This stronger direct
   argument applies to every reached sort through its proved nonidentity
   transported odd arrow; it does not assume a new-source property.
3. `Infinity.equivalence_class_infinite` gives infinite classes for every
   nontrivial original invariant equivalence. The key
   `type_class_infinite` proves that a realized old complete type meets its
   own gate class infinitely. If that intersection were finite, choose a
   gate-class point outside that finite intersection and the finite base.
   The intersection is then invariant over the enlarged base and contains
   the original point outside it, a contradiction. The choice is outside
   the assumed finite intersection, not outside the possibly infinite
   entire old type.
4. `SAP.marking_gate_eq` proves literal constancy of any legal global
   marking on every reached gate. `marked_fibre_infinite` combines it with
   the previous intersection theorem; inactive sorts use their forced
   zero bit and old infinite stabilizer orbits.
5. B044 already constructs the actual homogeneous marked Fraïssé source,
   its original reduct identification `I`, and the proved canonical global
   marking `mark I`. Its child points are literal unary subtypes of the
   SAME original points. Therefore an infinite old same-type/same-bit
   fibre lifts directly and injectively to actual new points over any
   finite new base. `SAP.sameType_of_old`, supplied by the terminal worker,
   reflects every old complete pair name plus the literal child bit to
   the complete new one-point type.
6. `unary_source_orbit_infinite` uses B044's proved WHOLE marked homogeneity
   to turn those actual new same-type witnesses into infinite orbits of
   its full automorphism group fixing the given finite base.
   `OwnerTransversal.ageSAP_of_infinite_stabilizer_orbits` supplies one
   simultaneous avoidance automorphism and proves SAP of the ENTIRE
   hereditary relational age. There are no functions, so closure of a
   finite real base is just that base. This is the required whole-age
   criterion, not a hidden point-generated special case.

This uses the canonical reduct identification to perform the finite-chart
transport in C30 directly on actual carriers. It never asserts homogeneity
of an arbitrary free-action seed marking. B044 ordinary AP supplies the
actual homogeneous marked source; its AP theorem is never renamed SAP.
The proof does not use new-source STRONG laws, a STRONG normal form,
phase primality, a sufficiency conclusion or an unaccepted later batch.

## Complete branch map

Names below are relative to `CCO.PairSafeSplit`.

| Claim | Actual proof |
|---|---|
| C22 | `Infinity.finite_invariant_subset_base`, `formulaSet_invariant`, `finite_formulaSet_subset_base`; accepted old off-base orbit infinitude. |
| C23 | `Full.ParityGateData.root_kernel_nontrivial`, `Infinity.equivalence_class_infinite`. |
| C24 | `SAP.kernel_ne_identity`, `reached_kernel_ne_bot`, `reached_kernel_gt_bot`; the proof uses the actual odd self-arrow on each reached gate. |
| C25 | `Infinity.class_has_other`, `equivalence_class_infinite`, instantiated with `SAP.reachedKernelEq`. |
| C26 | `Infinity.typeFibre_iff_orbit`, `typeFibre_avoids`, `typeFormula_realize`, `typeFormula_qf`, `tupleTypeFormula_realize`, `tupleTypeFormula_qf`. |
| C27 | `Infinity.type_class_infinite`. |
| C28 | `SAP.marking_gate_eq`, `marked_fibre_infinite`; `Infinity.constant_markedTypeFibre_infinite` for inactive sorts. |
| C29 | Accepted `APCharacter.SourceAge.actualIdentification`, `UnarySource.source`, `UnarySource.homogeneous` and actual marked-age construction, used without SAP. |
| C30 | Actual lifting map `lift` in `SAP.unary_source_orbit_infinite`, `SAP.oldBase`, `sameType_of_old`. Supplemental `Infinity.exists_old_witnesses` and the SAP-free actual `Strong.Realization.extend_legal_embedding` expose the explicit finite witness transport. |
| C31 | `SAP.unary_source_orbit_infinite`. |
| C32 | `SAP.unary_source_sap`, invoking actual simultaneous-avoidance `OwnerTransversal.ageSAP_of_infinite_stabilizer_orbits`. |
| C33 | The imports and proof body of `SAP.Source` depend only on old SAP, actual original gates/marks, accepted B044 homogeneity/reduct identification and the accepted whole-age orbit criterion. |

## Validation and provenance

Pinned Lean4.34.1 and bundled Lake were loaded through `../runtime/env.sh`.
Scoped target `CCO.PairSafeSplit.SAP.Gates` passed (2,310 jobs),
`CCO.PairSafeSplit.SAP.Markings` passed (2,313 jobs), and
`CCO.PairSafeSplit.SAP.Source` passed (2,494 jobs). All local build sessions
were collected. These incremental target builds are receipts, not an
independent review or final public CI/audit.

The owner implemented Gates (`c9e0165`), Markings (`e228b46`) and Source
(`ab24d8f`). The dedicated infinity/type-fibre helper implemented
`Infinity/TypeFibres.lean`, `MarkedFibres.lean`, `OldWitnesses.lean` and
`Definability.lean` in its isolated `cco-b047-infinity` worktree, retaining
its native history `02a14a4`, `26512d1`, `8a83d7f` and scoped report.
The terminal worker supplied `Terminal/TypeReflection.lean` (`857186d`).
The tuple helper independently supplied the SAP-free actual finite chart
realization and fixed-base extension used by the later path readout.
Every author and helper remains an author for review separation.
