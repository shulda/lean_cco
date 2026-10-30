import CCO.UnaryHN.NativeTransferBasis
import PartiteConstruction.Ramsey.AllThosePartialFiniteModels
import PartiteConstruction.Functional.WeakOperations

/-! The actual free class used INSIDE the HN partite construction is not K.
It consists of genuine partial models whose every actual closed irreducible
already belongs to K.  This is a free-amalgamation class by localization of
irreducibles, even when K itself only has strong amalgamation. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}}

def admissibleClass (K : Class.{u,v} L) : Class.{u,v} L :=
  fun C => C.SingletonValued ∧ IrreduciblesIn K C

theorem admissibleClass_free (K : Class.{u,v} L) :
    FreeAmalgamationClass (admissibleClass K) := by
  refine ⟨?_, ?_⟩
  · intro V W C D hD e
    refine ⟨singletonValued_of_embedding hD.1 e, ?_⟩
    intro X E hE f
    exact hD.2 E hE (e.comp f)
  · intro H E F C Root Left Right Whole sL sR iL iR hL hR hFree
    refine ⟨singletonValued_of_freeAmalgam hL.1 hR.1 hFree, ?_⟩
    intro X Test hTest e
    rcases hFree.irreducible_side hTest e with hLeft | hRight
    · choose q hq using hLeft
      exact hL.2 Test hTest (e.factorWithMap iL q hq)
    · choose q hq using hRight
      exact hR.2 Test hTest (e.factorWithMap iR q hq)

theorem admissibleClass_of_mem {K : Class.{u,v} L} (hK : FiniteHereditarySAP K)
    {V : Type v} {C : Structure L V} (hC : K C) : admissibleClass K C :=
  ⟨hK.singleton C hC, irreduciblesIn_of_mem hK.hereditary hC⟩

end CCO.UnaryHN.Native
