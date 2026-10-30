import CCO.UnaryHN.OrderedObstruction
import CCO.UnaryHN.Ordered.Completion

/-! Actual HN local finiteness in the LARGER all-model ordered ambient.
Only the restricted obstruction bound remains a mathematical premise.
The old reduct completion, E02 injection, entire-target order extension and
ordered HE are all constructed by the proved lemmas imported here. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

theorem strong_ordered_completion_at_cutoff
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hN : RestrictedObstruction K N)
    {P V : Type v} [Finite P] [Finite V]
    (C₀ : Structure L.withLinearOrder P) (hC₀ : AllOrderedModels L C₀)
    (C : Structure L.withLinearOrder V) (hSingle : C.SingletonValued)
    (p : V → P) (hp : HE C C₀ p)
    (hPieces : IrreduciblesIn (OrderedClass K) C)
    (hTests : ClosedSmallCompletable (OrderedClass K) C (obstructionCutoff N)) :
    HasStrongCompletion (OrderedClass K) C :=
  ordered_completion hUnary hK hIrr C hSingle C₀ hC₀ p hp hPieces
    (ordered_reduct_completion_of_restricted_tests hN C hSingle hPieces hTests)

/-- The SAME max(1,N) works for every original C₀, including empty carriers.
Candidates may initially be raw one-sorted partial structures. -/
theorem ordered_local_finite_of_obstruction
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hN : RestrictedObstruction K N) :
    LocallyFinite (OrderedClass K) (AllOrderedModels L) := by
  intro P hP C₀ hC₀
  refine ⟨obstructionCutoff N, ?_⟩
  intro V hV C hSingle hProjection hPieces hTests
  obtain ⟨p, hp⟩ := hProjection
  exact (strong_ordered_completion_at_cutoff hUnary hK hIrr hN C₀ hC₀ C hSingle
    p hp hPieces hTests).to_completion

end CCO.UnaryHN.Native
