import CCO.APCharacter.SourceAge.BackAndForth
import CCO.FullPhaseLift.BinarySource.TableHomogeneity

/-! Concrete countable table comparison from actual finite age witnesses
and whole finite tuple motions. Both witness/motion inputs are structural
support instantiated by the marked source constructions. -/

universe u v w z
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open OwnerTransversal.CountableColour APCharacter.SourceAge
noncomputable section

def TupleMotions {B : Type u} {C : Type v} {M : Type w} (T : Table B C M) : Prop :=
  ∀ (n : ℕ) (p q : Fin n ↪ M),
    (∀ x, T.owner (p x) = T.owner (q x)) →
    (∀ x y, T.colour (p x) (p y) = T.colour (q x) (q y)) →
    ∃ e : M ≃ M,
      (∀ x, T.owner (e x) = T.owner x) ∧
      (∀ x y, T.colour (e x) (e y) = T.colour x y) ∧
      ∀ x, e (p x) = q x

def AgeMaps {B : Type u} {C : Type v} {M : Type w} {N : Type z}
    (T : Table B C M) (U : Table B C N) : Prop :=
  ∀ (n : ℕ) (p : Fin n ↪ M), ∃ q : Fin n ↪ N,
    (∀ x, U.owner (q x) = T.owner (p x)) ∧
      ∀ x y, U.colour (q x) (q y) = T.colour (p x) (p y)

theorem finiteExtension_of_age_motions
    {B : Type u} {C : Type v} {M : Type w} {N : Type z}
    (T : Table B C M) (U : Table B C N) (age : AgeMaps T U) (hom : TupleMotions U) :
    FiniteExtension T U := by
  intro n m j p q hnames
  obtain ⟨r,ho,hc⟩ := age m p
  obtain ⟨e,heOwner,heColour,he⟩ := hom n (j.trans r) q
    (fun x => (ho (j x)).trans (hnames.1 x).symm)
    (fun x y => (hc (j x) (j y)).trans (hnames.2 x y).symm)
  refine ⟨r.trans e.toEmbedding,?_,?_,he⟩
  · intro x
    exact (heOwner (r x)).trans (ho x)
  · intro x y
    exact (heColour (r x) (r y)).trans (hc x y)

theorem actual_equiv_of_same_age
    {B : Type u} {C : Type v} {M : Type w} {N : Type z}
    [Countable M] [Countable N] (T : Table B C M) (U : Table B C N)
    (forth : AgeMaps T U) (back : AgeMaps U T)
    (homT : TupleMotions T) (homU : TupleMotions U) :
    ∃ e : M ≃ N, (∀ x, U.owner (e x) = T.owner x) ∧
      ∀ x y, U.colour (e x) (e y) = T.colour x y :=
  equiv_of_finiteExtension T U (finiteExtension_of_age_motions T U forth homU)
    (finiteExtension_of_age_motions U T back homT)

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
