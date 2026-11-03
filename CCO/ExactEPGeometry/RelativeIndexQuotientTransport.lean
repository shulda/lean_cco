import CCO.ParityHasse.Original.RelativeIndices

/-!
# B062 C105: genuine relative index under an exact quotient pullback

The terminality condition concerns the FULL lattice of original invariant
equivalences, not just RAW-exact relations. Its numerical ingredient is
independent of any exactness, AP, SAP, or source homogeneity:

For a surjective quotient projection, if TWO actual equivalence relations
on the original carrier are exactly the inverse images of two quotient
equivalences, the respective relative-class spaces are BIJECTIVE.

This holds without assuming that the two equivalences are nested; the
required nestedness is supplied by the eventual terminality application.
The finite-index and full-cover parts of the source theorem will need
the actual invariant quotient setoids and their order embeddings, not
an assumption that every invariant equivalence is RAW-exact.
-/

universe u v

namespace CCO.ExactEPGeometry

open CCO.ParityHasse.Original

noncomputable section

/-- The quotient does not change the ACTUAL relative classes for any two
equivalences which have genuine whole-relation pullbacks along a
surjective projection. No finite-index, action section, exactness,
amalgamation or quotient SAP is required. -/
noncomputable def relativeClassEquiv_of_surjective_pullback
    {A : Type u} {B : Type v}
    (pi : A → B) (surj : Function.Surjective pi)
    (E F : Setoid A) (U V : Setoid B)
    (hE : ∀ x y, E x y ↔ U (pi x) (pi y))
    (hF : ∀ x y, F x y ↔ V (pi x) (pi y))
    (a : A) :
    RelativeClass E F a ≃ RelativeClass U V (pi a) := by
  let lift : {x : A // F a x} → {y : B // V (pi a) y} :=
    fun x => ⟨pi x.val, (hF a x.val).mp x.property⟩
  have hRespect : ∀ x y : {x : A // F a x},
      (Setoid.comap Subtype.val E) x y →
        (Setoid.comap Subtype.val U) (lift x) (lift y) := by
    intro x y h
    exact (hE x.val y.val).mp h
  let f : RelativeClass E F a → RelativeClass U V (pi a) :=
    Quotient.map lift hRespect
  have hInjective : Function.Injective f := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        change (Quotient.mk _ (lift x) : RelativeClass U V (pi a)) =
          Quotient.mk _ (lift y) at hqr
        have h : (Setoid.comap (fun z : {b : B // V (pi a) b} => z.val) U)
            (lift x) (lift y) := Quotient.exact hqr
        change U (pi x.val) (pi y.val) at h
        exact (hE x.val y.val).mpr h
  have hSurjective : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      obtain ⟨x,hx⟩ := surj y.val
      have hFx : F a x := (hF a x).mpr (by simpa only [hx] using y.property)
      refine ⟨Quotient.mk _ (⟨x,hFx⟩ : {z : A // F a z}), ?_⟩
      apply Quotient.sound
      change U (pi x) y.val
      simpa only [hx] using (U.refl y.val)
  exact Equiv.ofBijective f ⟨hInjective,hSurjective⟩

/-- C105's numerical transport ingredient for EVERY original and
quotient invariant equivalence satisfying the full literal pullback
equations. A proper finite relative index on the quotient has exactly
the same positive value upstairs; no restriction to exact setoids. -/
theorem relativeIndex_eq_of_surjective_pullback
    {A : Type u} {B : Type v}
    (pi : A → B) (surj : Function.Surjective pi)
    (E F : Setoid A) (U V : Setoid B)
    (hE : ∀ x y, E x y ↔ U (pi x) (pi y))
    (hF : ∀ x y, F x y ↔ V (pi x) (pi y))
    (a : A) :
    relativeIndex E F a = relativeIndex U V (pi a) :=
  Nat.card_congr
    (relativeClassEquiv_of_surjective_pullback pi surj E F U V hE hF a)

end
end CCO.ExactEPGeometry
