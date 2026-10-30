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

/-- C33/C43 without homogeneity: the actual full invariant chain gives
a power of two, and the independent bit code bounds that exponent. -/
theorem transitive_target_card (cco : SemanticCCO T)
    (trans : ∀ x y : Fin T.size,∃ g : Aut T,g • x = y) (a : Fin T.size) :
    ∃ m : Nat,T.size = 2^m ∧ m ≤ Nat.card (Occurring T) := by
  obtain ⟨n,hn⟩ := automorphism_two_group T cco
  let chain := Group.invariantSaturatedChain (G := Aut T) (A := Fin T.size)
  have hs := Group.chain_card_two_power hn trans a chain
  have hcard : T.size = 2^chain.length := by simpa only [Nat.card_fin] using hs
  refine ⟨chain.length,hcard,?_⟩
  have hb := cardinal_le_bits T cco
  rw [hcard] at hb
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

end CCO.FiniteFibres
