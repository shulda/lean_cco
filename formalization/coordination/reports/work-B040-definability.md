# B040 actual first-order definability gate

Actual author: `/root/b040_transport/shared_actions`.
Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5` and all
mathematical contracts are unchanged. This module is independent of the
generic group-action transport and return implementations.

`CCO/QuotientTransport/Definability.lean` supplies actual
`FirstOrder.Language.Formula (Fin 2)` objects and their realization
theorems. `FormulaDefines` and `HasFormula` transparently mean an actual
parameter-free formula with exactly the stated binary relation; neither
is an oracle or an additional mathematical provider.

- `converseFormula` swaps the two free variables.
- `compFormula` existentially quantifies one actual intermediate point.
  `compFormula_realize` proves literal equality-inclusive composition.
- `transportFormula_realize` proves the actual C13 formula
  `∃ x x', R(x,y) ∧ E(x,x') ∧ R(x',y')`.
- `taggedRelation` interprets a typed relation on the ambient `Sigma X`,
  false off its actual two original sorts. `taggedRelation_comp` proves
  that ambient existential witnesses have the required intermediate sort.
  Thus no untyped witness is silently admitted.
- `typed_transport_has_formula` proves C13 from actual input formulas,
  without a group action, exactness, SAP, CCO or homogeneity premise.
- `typedWord_has_formula` proves C25 for every finite actual `TypedWord`,
  including nil when supplied its named-sort identity formula. This is
  structural induction using the actual formula constructor.

The intended original finite named orbital source gate is fully discharged:

- `namedLanguage` and `namedStructure` are the actual original unary-sort
  and binary optional-pair-colour interpretation on `Sigma X` of an
  `AtomicSource`. There are no functions and no parameter constants.
- `finiteTotalNamedSymbols` proves the whole relation signature finite,
  using the source's finite sort and typed palette instances.
- `pairFormula_none_realize` proves the optional none name is precisely
  logical equality with its original sort guards. It adds no extra
  relation beyond the already named sorting and real diagonal.
- `sourceFormula` is the finite first-order disjunction of the named
  optional pair colours actually occurring in the relation's raw support.
- `sourceFormula_realize` proves its exact meaning for every invariant
  relation using the unchanged B001 original-source pair homogeneity
  theorem. The latter is derived from the actual `HomogeneousSource`;
  no premise assumes the desired formula result. The argument works even
  for an earlier group satisfying this exact pair homogeneity, so applies
  in particular to the intended full original automorphism action.
- `source_identity_has_formula` discharges the empty-prefix case.
  `source_typedWord_has_formula` constructs all finite prefix formulas.
  `source_prefix_transport_has_formula` then constructs every prefix's
  literal `Rᵗ;E;R`, also for a coarser J when J has an actual formula.
  Every invariant J has such a formula in this intended finite source;
  no such conclusion is asserted for an arbitrary subgroup action.

These provide C13/C25 and the formula components of the C14/C26 source
exports. The owner combines them with the independently proved invariant
algebra. No named FULL RAW exact coordinate, noncollapse or group section
is inferred from definability.

Validation: the pinned Lean 4.34.1 and unchanged manifest, with the existing
runtime process shim and Lake artifact restoration disabled, successfully
ran `lake build CCO.QuotientTransport.Definability` (930 jobs). Only this
new module and needed existing dependencies were requested. This helper
does not claim whole-project CI or axiom-audit completion.
