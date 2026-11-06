import CCO.TypedOrbitFrames.ActualFreshRepresentatives
import Mathlib.Data.Fintype.EquivFin

/-! A finite actual closed member has a finite list of requests for
EXACTLY its nonreal vertices. Real representatives are not added to A. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

def originalTypedRequestVertex (H : HomogeneousSource S G)
    (r : OriginalTypedQuotientRequest S H) : OriginalCompletedNamedCarrier S H :=
  originalCompletedNamedHiddenNode S H r.2.1 r.2.2

theorem original_nonreal_vertex_has_actual_request
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (b : OriginalCompletedNamedCarrier S H)
    (hb : (originalCompletedStructure S H sap nr2).sort b ∉ originalCompletedRealSorts S H sap nr2) :
    ∃ r : OriginalTypedQuotientRequest S H, originalTypedRequestVertex S H r = b := by
  cases b with
  | inl b => exact False.elim (hb ⟨b.1,rfl⟩)
  | inr b =>
      obtain ⟨i,J,q,hq⟩ := original_completed_hidden_value_has_named_witness S H b
      exact ⟨⟨i,⟨J,q⟩⟩,hq.symm⟩

theorem original_finite_nonreal_request_enumeration
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (A : Set (OriginalCompletedNamedCarrier S H)) (hA : A.Finite) :
    ∃ n : Nat, ∃ r : Fin n → OriginalTypedQuotientRequest S H,
      (∀ j, originalTypedRequestVertex S H (r j) ∈ A) ∧
      ∀ b ∈ A, (originalCompletedStructure S H sap nr2).sort b ∉
        originalCompletedRealSorts S H sap nr2 →
        ∃ j, originalTypedRequestVertex S H (r j) = b := by
  classical
  let B := {b : OriginalCompletedNamedCarrier S H // b ∈ A ∧
    (originalCompletedStructure S H sap nr2).sort b ∉ originalCompletedRealSorts S H sap nr2}
  haveI : Finite A := hA.to_subtype
  haveI : Finite B := Finite.of_injective
    (fun b : B => (⟨b.val,b.property.1⟩ : A)) (fun a b h => Subtype.ext (congrArg (fun z : A => z.val) h))
  letI : Fintype B := Fintype.ofFinite B
  choose request hRequest using fun b : B =>
    original_nonreal_vertex_has_actual_request S H sap nr2 b.val b.property.2
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  refine ⟨Fintype.card B,fun j => request (e j),?_,?_⟩
  · intro j
    rw [hRequest]
    exact (e j).property.1
  · intro b hb hn
    let b' : B := ⟨b,hb,hn⟩
    refine ⟨e.symm b',?_⟩
    exact (hRequest (e (e.symm b'))).trans (congrArg Subtype.val (e.apply_symm_apply b'))

end CCO.TypedOrbitFrames
