import CCO.UnaryHN.IteratedTransfer
import CCO.UnaryHN.LocalFiniteness
import CCO.UnaryHN.Ordered.Amalgamation
import CCO.UnaryHN.OrderedRigidity

/-! The three genuine providers are assembled here: actual HN2.19 ordered
models, actual E02 injectivization, and the proved original unary HN2.11
construction. No theorem-provider callback or canonical-target schema occurs
in the principal restricted-obstruction transfer. -/

universe u v w
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

/-- Original HN local test at ONE uniform prescribed cutoff for every C₀. -/
def UniformlyLocallyFinite {L : Language.{u}} (K R : Class.{u,v} L) (n : ℕ) : Prop :=
  ∀ {P : Type v} [Finite P] (C₀ : Structure L P), R C₀ →
    ∀ {V : Type v} [Finite V] (C : Structure L V),
      C.SingletonValued → (∃ p : V → P, HE C C₀ p) →
      IrreduciblesIn K C → ClosedSmallCompletable K C n → HasCompletion K C

theorem UniformlyLocallyFinite.locallyFinite {L : Language.{u}} {K R : Class.{u,v} L}
    {n : ℕ} (h : UniformlyLocallyFinite K R n) : LocallyFinite K R := by
  intro P hP C₀ hC₀
  exact ⟨n, h C₀ hC₀⟩

theorem uniform_ordered_local_finite_of_obstruction
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hN : RestrictedObstruction K N) :
    UniformlyLocallyFinite (OrderedClass K) (AllOrderedModels L) (obstructionCutoff N) := by
  intro P hP C₀ hC₀ V hV C hSingle hProjection hPieces hTests
  obtain ⟨p, hp⟩ := hProjection
  exact (strong_ordered_completion_at_cutoff hUnary hK hIrr hN C₀ hC₀ C hSingle
    p hp hPieces hTests).to_completion

theorem ordered_ramsey_of_restricted_obstruction
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hN : RestrictedObstruction K N) : Ramsey.{u,v,w} (OrderedClass K) :=
  original_unary_locally_finite_ramsey (unary_withLinearOrder hUnary)
    (orderedClass_finiteHereditarySAP hK) (orderedClass_subset_ambient hK)
    (orderedClass_allIrreducible (fun C => C.SingletonValued))
    (allOrderedModels_ramsey L) (ordered_local_finite_of_obstruction hUnary hK hIrr hN)

/-- Uniform max(1,N) local finiteness AND Ramsey, retaining only the supplied
restricted obstruction premise alongside the source's hereditary SAP class. -/
theorem unary_ordered_transfer
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hN : RestrictedObstruction K N) :
    UniformlyLocallyFinite (OrderedClass K) (AllOrderedModels L) (obstructionCutoff N) ∧
      Ramsey.{u,v,w} (OrderedClass K) :=
  ⟨uniform_ordered_local_finite_of_obstruction hUnary hK hIrr hN,
    ordered_ramsey_of_restricted_obstruction hUnary hK hIrr hN⟩

end CCO.UnaryHN.Native
