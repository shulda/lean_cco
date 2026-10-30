import CCO.FullPhaseLift.BinarySource.FullAlignment
import CCO.FullPhaseLift.BinarySource.TableHomogeneity

/-! The frozen full factor supplied by the chosen-pair lift gives the
ACTUAL binary extension property after full alignment. Every old relation
is retained on the base; the resulting binary map fixes that base exactly.
The lift hypothesis here is structural support, instantiated from A03 by
the receiving source theorem. -/

universe u v w z
namespace CCO.FullPhaseLift.BinarySource
open RelationalCompletion.Relational
open OwnerTransversal.CountableColour
open APCharacter.SourceAge
noncomputable section

theorem finiteExtension_of_frozen_lift
    {L : Language.{u}} {M : Type v} {B : Type w} {C : Type z}
    (U : Structure L M) (hom : U.Homogeneous) (T : Table B C M)
    (invariant : ∀ a : U.Iso U,
      (∀ x, T.owner (a.point x) = T.owner x) ∧
      ∀ x y, T.colour (a.point x) (a.point y) = T.colour x y)
    (lift : ∀ (n m : ℕ) (j : Fin n ↪ Fin m) (p : Fin m ↪ M) (q : Fin n ↪ M),
      (∀ x, T.owner (q x) = T.owner (p (j x))) ∧
        (∀ x y, T.colour (q x) (q y) = T.colour (p (j x)) (p (j y))) →
      ∃ r : Fin m ↪ M,
        (∀ x, T.owner (r x) = T.owner (p x)) ∧
        (∀ x y, T.colour (r x) (r y) = T.colour (p x) (p y)) ∧
        ∀ {k} (R : L.Rel k) xs,
          U.rel R ((r ∘ j) ∘ xs) ↔ U.rel R (q ∘ xs)) :
    FiniteExtension T T := by
  intro n m j p q hnames
  obtain ⟨r,ho,hc,hfull⟩ := lift n m j p q hnames
  have heq : ∀ x y, r (j x) = r (j y) ↔ q x = q y := by
    intro x y
    rw [r.injective.eq_iff,j.injective.eq_iff,q.injective.eq_iff]
  obtain ⟨a,ha⟩ := full_tuple_homogeneous U hom (r ∘ j) q heq hfull
  let s : Fin m ↪ M := r.trans a.point.toEmbedding
  refine ⟨s,?_,?_,?_⟩
  · intro x
    exact ((invariant a).1 (r x)).trans (ho x)
  · intro x y
    exact ((invariant a).2 (r x) (r y)).trans (hc x y)
  · exact ha

end
end CCO.FullPhaseLift.BinarySource
