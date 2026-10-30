import CCO.UnaryHN.Obstruction
import CCO.UnaryHN.Ordered.Forget

/-! The exact restricted obstruction argument, after forgetting ONLY the
displayed order. A witness keeps its original closed carrier and cardinality;
there is no generated-hull or weak-relational-subset replacement. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

theorem ordered_reduct_completion_of_restricted_tests
    {L : Language.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hN : RestrictedObstruction K N)
    {V : Type v} [Finite V] (C : Structure L.withLinearOrder V)
    (hSingle : C.SingletonValued)
    (hPieces : IrreduciblesIn (OrderedClass K) C)
    (hTests : ClosedSmallCompletable (OrderedClass K) C (obstructionCutoff N)) :
    HasCompletion K C.linearOrderReduct :=
  completion_of_restricted_local_tests hN C.linearOrderReduct hSingle
    (ordered_irreducibles_reduct hPieces) (ordered_small_reduct hTests)

theorem unary_withLinearOrder {L : Language.{u}} (h : Unary L) : Unary L.withLinearOrder := h

theorem orderedClass_subset_ambient {L : Language.{u}} {K : Class.{u,v} L}
    (hK : FiniteHereditarySAP K) :
    ∀ {V : Type v} (C : Structure L.withLinearOrder V),
      OrderedClass K C → AllOrderedModels L C :=
  orderedClass_mono (fun C hC => hK.singleton C hC)

end CCO.UnaryHN.Native
