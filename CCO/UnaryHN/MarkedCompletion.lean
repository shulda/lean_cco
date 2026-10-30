import CCO.UnaryHN.NativeTransferBasis

/-! Ordinary K-completions can be extended along an occupied ACTUAL closed
substructure of a K-member.  The root is irreducible by actual hereditary
membership, so its given HE is a full embedding.  Strong amalgamation then
adjoins the entire marked member.  Nothing here assumes that an arbitrary
reducible source HE is injective or globally induced. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {K : Class.{u,v} L}

theorem completion_with_mark (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    {H V W : Type v} {Root : Structure L H} {C : Structure L V}
    {A : Structure L W} (hA : K A)
    (rC : Embedding Root C) (rA : Embedding Root A)
    (hC : HasCompletion K C) :
    ∃ (X : Type v) (_ : Finite X) (Target : Structure L X), K Target ∧
      ∃ (f : V → X) (mark : Embedding A Target),
        HE C Target f ∧ ∀ z, f (rC z) = mark (rA z) := by
  obtain ⟨Y, hY, T, hT, q, hq⟩ := hC
  have hRoot : K Root := hK.hereditary hA rA
  obtain ⟨rT, hrT⟩ := hq.2 Root (hIrr Root hRoot) rC
  obtain ⟨X, hX, Target, hTarget, jT, jA, hAgree, _⟩ :=
    hK.strong hT hA rT rA
  refine ⟨X, hX, Target, hTarget, jT ∘ q, jA,
    jT.isEHNHomomorphismEmbedding.comp hq, ?_⟩
  intro z
  exact (congrArg jT (hrT z).symm).trans (hAgree z)

end CCO.UnaryHN.Native
