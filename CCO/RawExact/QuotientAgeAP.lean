import CCO.AgeAP

/-!
# Actual induced-age AP from finite homogeneity

Move one finite copy by one original automorphism aligning its whole
common induced base with the other, and take their actual finite union.
Additional identifications outside the base are permitted. This supplies
the C25 amalgamation mechanism once genuine actual quotient homogeneity
has been instantiated; it does not infer SAP from AP or CCO.
-/

universe u v w t

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Finite homogeneity supplies AP of the ACTUAL finite induced age by
one automorphism and actual finite union. No SAP premise is used. -/
theorem ageAP_of_homogeneous
    {G : Type t} [Group G] [MulAction G (Sigma X)]
    (H : HomogeneousSource S G) : AgeAP S := by
  refine ⟨?_⟩
  intro C A B eCA eCB
  let source : ↥C.vertices → Sigma X := fun c => (eCA.toEmbedding c).val
  let target : ↥C.vertices → Sigma X := fun c => (eCB.toEmbedding c).val
  let : Finite ↥C.vertices := C.finite_vertices.to_subtype
  have hColour : ∀ c d, taggedColour S (source c) (source d) =
      taggedColour S (target c) (target d) := by
    intro c d
    exact (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d)
  obtain ⟨g, hg⟩ := H.extends_finite_diagram source target hColour
  let D : FiniteInduced (X := X) :=
    ⟨(fun p : Sigma X => g • p) '' A.vertices ∪ B.vertices,
      (A.finite_vertices.image (fun p : Sigma X => g • p)).union B.finite_vertices⟩
  let eAD : InducedEmbedding S A D :=
    { toEmbedding :=
        { toFun := fun a => ⟨g • a.val, Or.inl ⟨a.val, a.property, rfl⟩⟩
          inj' := by
            intro a b hab
            have hsmul : g • a.val = g • b.val := congrArg Subtype.val hab
            have hinv := congrArg (fun p : Sigma X => g⁻¹ • p) hsmul
            apply Subtype.ext
            simpa only [inv_smul_smul] using hinv }
      preserves_sort := fun a => H.preserves_sort g a.val
      preserves_colours := fun a b => (H.preserves_colours g a.val b.val).symm }
  let eBD : InducedEmbedding S B D :=
    { toEmbedding :=
        { toFun := fun b => ⟨b.val, Or.inr b.property⟩
          inj' := by
            intro a b hab
            apply Subtype.ext
            exact congrArg (fun p : ↥D.vertices => p.val) hab }
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
  refine ⟨D, eAD, eBD, ?_⟩
  intro c
  apply Subtype.ext
  exact hg c

end CCO
