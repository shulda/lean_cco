import CCO.ResetOrder.Hierarchy.ClosedTransitions
import CCO.ResetOrder.Hierarchy.GridBoundary
import CCO.ResetOrder.Hierarchy.NamedTerms
import CCO.ResetOrder.Hierarchy.RelativeReversal
import CCO.ResetOrder.Hierarchy.SortPriority
import CCO.ResetOrder.Hierarchy.TaskDAG

/-! B036 T03 source concordance, pinned source490c3f36d85db5a0b3ced0598e6c431825254ec5.

C13: Lattice.strictCoarserMI_inf and EquivalenceLattice.key_eq_parent_iff.
C14–16: actual CutTransitions.restrict/charting, inverse_chart,
path_independent, Charting.localTasks_synchronized.
C17: upperRank_strict/transport and coarserOrbit_wellFounded.
C18: System.normalizeTasks builds every strict-total order recursively;
QuotientSystem.ClosedObject.system derives its complete key law from actual
quotients. sortOrder combines all sort orders using the one fixed priority.
C19: OrderedEmbedding.ofNamedTerms derives commuting maps from actual old
unary graphs/terms; normalize and normalized_order_iff prove the same vertex
maps are induced embeddings, retaining all old domains/values/relations.
C20–21: normalize_idempotent and Charting.fixed_iff_image identify precisely
the synchronized within-parent, parent-lex image. No global transition
monotonicity or equivariant-coordinate-priority premise appears.
C22–23: reverseOrbit_coarser/local and the actual OrderedEmbedding.reverseOrbit
functor reverse one orbit and recompute later comparisons by the SAME rule.
C24: the declaration below assembles the actual normalization conclusion.
C52: GridBoundary is an actual six-element distributive equivalence lattice
on a sixteen-point original grid, with its actual J quotient and cut swap.
Both orders are strict-total and fibres synchronize, but global monotonicity
fails. This is a mathematical boundary witness, not a bounded provider test.
-/
universe u v w
namespace CCO.ResetOrder.Hierarchy

theorem hierarchical_order_normalization
    {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
    {X : Sigma J → Type v} {S : System H X} {rep : ∀ r, J r}
    (C : Charting.{u,v,w} S rep) {L : OldLanguage (Sigma J)}
    (A : C.OrderedStructure L) :
    A.normalize.data = A.data ∧ A.normalize.normalize = A.normalize ∧
      S.ParentLex A.normalize.orders ∧ C.Synchronized A.normalize.orders :=
  ⟨rfl, A.normalize_idempotent, C.normalize_parentLex A.orders,
    C.normalize_synchronized A.orders⟩

end CCO.ResetOrder.Hierarchy
