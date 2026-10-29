import CCO.Owners.Provider.GenericLanguage

/-!
# Ordinary relational-age EPPA realized over the original finite input

The input age embedding is arbitrary, and all partial maps/automorphisms
preserve relations of ALL arities. Homogeneity proves the anchored witness.
-/

namespace CCO.Owners.Provider.Relational

variable {A : Type*} (S : Structure A)

/-- Ordinary EPPA of the relational age, using finite induced copies in
the ambient structure. The embedding need not be the original inclusion. -/
def OrdinaryEPPA : Prop :=
  ∀ T : Set A, T.Finite → ∃ C : Set A, C.Finite ∧
    ∃ e : T ↪ C, Preserves S Subtype.val Subtype.val e ∧
      ∀ p : Partial S (Subtype.val : T → A),
        ∃ β : Aut S (Subtype.val : C → A),
          ∀ x : p.domain, β.val (e x.val) = e (p.map x)

noncomputable def translateEquiv (g : Aut S id) (C : Set A) :
    C ≃ ((fun x : A => g.val x) '' C) where
  toFun x := ⟨g.val x.val, x.val, x.property, rfl⟩
  invFun x := ⟨g.val.symm x.val, by
    obtain ⟨y, hy, hgy⟩ := x.property
    rw [← hgy, Equiv.symm_apply_apply]
    exact hy⟩
  left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)

theorem translate_preserves (g : Aut S id) (C : Set A) :
    Preserves S Subtype.val Subtype.val (translateEquiv S g C) := by
  intro s t
  exact (Aut.preserves S g) s (fun k => (t k).val)

noncomputable def translateAut (g : Aut S id) (C : Set A)
    (β : Aut S (Subtype.val : C → A)) :
    Aut S (Subtype.val : ((fun x : A => g.val x) '' C) → A) :=
  conjugateAut S Subtype.val Subtype.val (translateEquiv S g C)
    (translate_preserves S g C) β

theorem eppa_over_original (hom : Homogeneous S) (ep : OrdinaryEPPA S)
    (T : Set A) (hT : T.Finite) :
    ∃ C : Set A, C.Finite ∧ ∃ hTC : T ⊆ C,
      ∀ p : Partial S (Subtype.val : T → A),
        ∃ β : Aut S (Subtype.val : C → A),
          ∀ x : p.domain, (β.val ⟨x.val.val, hTC x.val.property⟩).val = (p.map x).val := by
  obtain ⟨C, hC, e, he, hep⟩ := ep T hT
  have hinj : Function.Injective (fun x : T => (e x).val) :=
    Subtype.val_injective.comp e.injective
  obtain ⟨g, hg⟩ := hom T hT (fun x => (e x).val) hinj he
  let D : Set A := (fun x : A => g.val x) '' C
  have hD : D.Finite := hC.image (fun x : A => g.val x)
  have hTD : T ⊆ D := by
    intro x hx
    exact ⟨(e ⟨x,hx⟩).val, (e ⟨x,hx⟩).property, hg ⟨x,hx⟩⟩
  refine ⟨D, hD, hTD, ?_⟩
  intro p
  obtain ⟨β, hβ⟩ := hep p
  refine ⟨translateAut S g C β, ?_⟩
  intro x
  have hx : (translateEquiv S g C).symm ⟨x.val.val, hTD x.val.property⟩ = e x.val := by
    apply (translateEquiv S g C).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (hg x.val).symm
  change (translateEquiv S g C (β.val ((translateEquiv S g C).symm
    ⟨x.val.val, hTD x.val.property⟩))).val = (p.map x).val
  rw [hx, hβ x]
  exact hg (p.map x)

end CCO.Owners.Provider.Relational
