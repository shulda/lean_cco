import CCO.Finite
import CCO.Supports
import Mathlib.Algebra.Group.Action.Sigma

/-!
# Compatibility of the actual finite homogeneous source and typed group actions

Here the action on the tagged real universe is the canonical Sigma action
coming from the family of original-sort actions. Therefore the same
automorphisms, rather than two unrelated actions, preserve the actual
fine-colour predicates. This is the necessary bridge for RAW orbitals.
-/

namespace CCO.AtomicSource

variable {ι : Type*} {X : ι → Type*}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

theorem colourInvariant_of_homogeneous
    (H : HomogeneousSource (S := S) G) {i j : ι} :
    S.ColourInvariant (G := G) (i := i) (j := j) := by
  intro g x y
  have h := H.preserves_colours g (⟨i, x⟩ : Sigma X) (⟨j, y⟩ : Sigma X)
  simpa only [taggedColour, Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using h

end CCO.AtomicSource
