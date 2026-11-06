import Mathlib.Data.Setoid.Basic

/-!
# B062 C103: true quotient-class equivalence when a named child meets all E-classes

The discarded phase C73–C76 proves that every original E-class
meeting a parent type also meets ANY of its actual phase children.
An actual child's point projection forgets the bit tag. If the
child setoid is the whole pullback of the parent setoid along that
projection, the two class carriers are genuinely equivalent.

This generic lemma packages ONLY that real mathematical obligation:
it requires pairwise pullback equivalence and actual surjectivity on
E-classes, not surjectivity of the point projection. It adds no
section, quotient SAP, exactness, or finite index premise. The
source C103 discharged application has to use the actual discarded
classwise witness, not supply this as a new hypothetical provider.
-/

universe u v

namespace CCO.ExactEPGeometry

noncomputable section

/-- Under genuine pullback of a whole equivalence and onto-CLASSES,
the quotient map is a bijection. The point map itself may be far
from surjective: e.g. a marked child occupies each E-class but
only one old phase bit. -/
noncomputable def quotientClassEquiv_of_classwiseSurjective
    {X : Type u} {Y : Type v}
    (S : Setoid X) (T : Setoid Y)
    (f : X → Y)
    (hPull : ∀ x y, S x y ↔ T (f x) (f y))
    (hClassSurj : ∀ y : Y, ∃ x : X, T y (f x)) :
    Quotient S ≃ Quotient T := by
  let qmap : Quotient S → Quotient T :=
    Quotient.map f (fun _ _ h => (hPull _ _).mp h)
  have hInj : Function.Injective qmap := by
    intro q r h
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        change (Quotient.mk _ (f x) : Quotient T) =
          Quotient.mk _ (f y) at h
        exact (hPull x y).mpr (Quotient.exact h)
  have hSurj : Function.Surjective qmap := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      obtain ⟨x,hxy⟩ := hClassSurj y
      refine ⟨Quotient.mk _ x,?_⟩
      apply Quotient.sound
      exact T.symm hxy
  exact Equiv.ofBijective qmap ⟨hInj,hSurj⟩

end
end CCO.ExactEPGeometry
