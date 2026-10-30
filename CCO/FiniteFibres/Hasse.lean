import CCO.FiniteFibres.Automorphisms
import CCO.FiniteFibres.Group.FiniteCover

/-! The actual finite-target Hasse export uses FULL Aut(T), its proved
2-power order and only optional target transitivity. -/
namespace CCO.FiniteFibres
open Group.Correspondence
variable {C : Type*} (T : Target C)

/-- `cor:hasse`: every cover in the FULL invariant-equivalence lattice has
exactly two lower classes inside EVERY upper class. Homogeneity is absent. -/
theorem finite_hasse_index_two (cco : SemanticCCO T)
    (trans : ∀ x y : Fin T.size, ∃ g : Aut T, g • x = y)
    (a : Fin T.size) {U V : InvEq (Aut T) (Fin T.size)} (h : U ⋖ V) :
    Nat.card (RelativeClass U V h.le a) = 2 := by
  obtain ⟨n,hn⟩ := automorphism_two_group T cco
  exact Group.cover_relative_card_two hn trans a h

end CCO.FiniteFibres
