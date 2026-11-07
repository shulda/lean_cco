import CCO.UnarySupport.UnaryBoundaries

/-!
# A reducible OLD source can have coincident HE target images

This is a genuine finite partial unary source and an actual
homomorphism-embedding, rather than just a noninjective set map.  Its two
identity-unary orphan points lie in different free factors.  Reflection
on irreducibles, including the empty support, does not identify them.
-/

namespace CCO.GuardedOldSeams

open UnarySupport UnarySupport.Structure UnarySupport.Boundaries

def orphanCollapse : Hom (identityUnary Bool) (identityUnary Unit) where
  point _ := ()
  sort_eq _ := rfl
  map_func _ _ _ _ := rfl
  map_rel R := Empty.elim R

theorem orphanCollapse_is_HE : orphanCollapse.HomEmbedding := by
  intro S hS hirr
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy _
    exact identity_irreducible_subsingleton S hS hirr hx hy
  · intro R
    exact Empty.elim R
  · intro F x hx y hy
    exact ⟨x, hx, rfl, Subsingleton.elim _ _⟩

/-- C19/C68: equality introduced by an HE target is not literal source
equality and cannot supply a missing OLD unary-coordinate seam. -/
theorem target_coincidence_is_not_old_equality :
    ¬ (identityUnary Bool).Irreducible ∧ orphanCollapse.HomEmbedding ∧
      orphanCollapse.point false = orphanCollapse.point true ∧
      (false : Bool) ≠ true :=
  ⟨fun h => h.false identitySplit, orphanCollapse_is_HE, rfl, Bool.false_ne_true⟩

/-- This example has only positive-arity relation symbols (vacuously),
so its HE claim includes the empty source support without a nullary gap. -/
theorem orphan_language_positive :
    ∀ R : (unarySignature Unit).Rel, 0 < (unarySignature Unit).arity R :=
  fun R => Empty.elim R

end CCO.GuardedOldSeams
