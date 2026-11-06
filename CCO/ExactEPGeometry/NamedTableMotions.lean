import CCO.FullPhaseLift.BinarySource.MarkedComparisonSupport
import CCO.Finite

/-!
# Finite motions of a complete owner/colour table

A table which preserves and reflects the full ACTUAL tagged atomic pair
colour has precisely the finite tuple motions of the source group. This
uses the actual homogeneous finite-tuple extension and actual group action;
no table-homogeneity provider is added in the source consumers.
-/

universe u v w t b c
namespace CCO.ExactEPGeometry
open FullPhaseLift.BinarySource.MarkedComparison
open OwnerTransversal.CountableColour

noncomputable section

/-- A complete representation of actual source pair colours carries
all actual finite source motions, including finite and empty tuples. -/
theorem namedTableMotions_of_completePalette
    {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [MulAction G (Sigma X)]
    (H : HomogeneousSource S G)
    {B : Type b} {C : Type c} (T : Table B C (Sigma X))
    (hPalette : ∀ (q s q' s' : Sigma X),
      taggedColour S q' s' = taggedColour S q s ↔
        T.owner q' = T.owner q ∧ T.owner s' = T.owner s ∧
        T.colour q' s' = T.colour q s) :
    TupleMotions T := by
  intro n p q hOwner hColour
  let p' : ULift.{max u v} (Fin n) → Sigma X := fun i => p i.down
  let q' : ULift.{max u v} (Fin n) → Sigma X := fun i => q i.down
  have hPairs : ∀ i j, taggedColour S (p' i) (p' j) = taggedColour S (q' i) (q' j) := by
    intro i j
    exact (hPalette (q i.down) (q j.down) (p i.down) (p j.down)).mpr
      ⟨hOwner i.down,hOwner j.down,hColour i.down j.down⟩
  obtain ⟨g,hg⟩ := H.extends_finite_diagram p' q' hPairs
  let e : Sigma X ≃ Sigma X := MulAction.toPerm g
  refine ⟨e,?_,?_,?_⟩
  · intro x
    exact ((hPalette x x (g • x) (g • x)).mp (H.preserves_colours g x x)).1
  · intro x y
    exact ((hPalette x y (g • x) (g • y)).mp (H.preserves_colours g x y)).2.2
  · intro i
    exact hg ⟨i⟩

end
end CCO.ExactEPGeometry
