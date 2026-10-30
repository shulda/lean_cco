import CCO.FiniteFibres.Boundaries.DifferenceExamples
import CCO.FiniteFibres.Boundaries.DifferencePalette
import CCO.FiniteFibres.Boundaries.Nontransitive

/-! Direct consumers of the actual boundary structures and the accepted
arbitrary-palette atomic diagram interface. None supplies the positive
finite symmetric-target theorem with a missing provider. -/
namespace CCO.FiniteFibres.Boundaries

theorem directed_three_atomic_completion {n : ℕ}
    (D : RelationalCompletion.Atomic.Diagram (Difference.palette DirectedThree.Point) n)
    (hc : ∀ C : RelationalCompletion.Atomic.SimpleCycle D,
      Difference.AtomicDiagram.CycleHom D C) :
    ∃ f : Fin n → DirectedThree.Point, Difference.AtomicDiagram.Hom D f :=
  Difference.AtomicDiagram.semanticCCO D hc

theorem infinite_palette_atomic_completion {n : ℕ}
    (D : RelationalCompletion.Atomic.Diagram (Difference.palette InfinitePalette.Point) n)
    (hc : ∀ C : RelationalCompletion.Atomic.SimpleCycle D,
      Difference.AtomicDiagram.CycleHom D C) :
    ∃ f : Fin n → InfinitePalette.Point, Difference.AtomicDiagram.Hom D f :=
  Difference.AtomicDiagram.semanticCCO D hc

/-- C44: directed HOM CCO really has a full automorphism group of order 3.
The actual atom witnesses failure of the symmetry premise. -/
theorem directed_three_counterexample :
    DirectedThree.source.Homogeneous ∧ Difference.SemanticCCO DirectedThree.Point ∧
    Nat.card DirectedThree.source.Aut = 3 ∧
    (¬∃ k : ℕ, Nat.card DirectedThree.source.Aut = 2^k) ∧
    DirectedThree.source.binary DirectedThree.forward 0 1 ∧
    ¬DirectedThree.source.binary DirectedThree.forward 1 0 :=
  ⟨DirectedThree.homogeneous,DirectedThree.semanticCCO,DirectedThree.fullAut_card,
    DirectedThree.fullAut_not_power_two,DirectedThree.not_symmetric⟩

/-- C50: all claims concern the SAME actual countable infinite structure,
its full group, its genuine symmetric atoms, and its real anchor closure. -/
theorem infinite_palette_counterexample :
    Countable InfinitePalette.Point ∧ Infinite InfinitePalette.Point ∧
    InfinitePalette.source.Homogeneous ∧ Difference.SemanticCCO InfinitePalette.Point ∧
    (∀ (a : Difference.Atom InfinitePalette.Point) x y,
      InfinitePalette.source.binary a x y ↔ InfinitePalette.source.binary a y x) ∧
    (∀ a : InfinitePalette.Point, (Difference.realAcl InfinitePalette.Point {a}).Infinite) :=
  ⟨inferInstance,inferInstance,InfinitePalette.homogeneous,InfinitePalette.semanticCCO,
    InfinitePalette.every_atom_symmetric,InfinitePalette.singleton_realAcl_infinite⟩

namespace GenericGroupScope

abbrev Four := Multiplicative (ZMod 4)
def quarter : Four := Multiplicative.ofAdd 1

theorem card_power_two : Nat.card Four = 2^2 := by
  change Nat.card (ZMod 4) = 2^2
  rw [Nat.card_eq_fintype_card,ZMod.card]
  decide

/-- C46: power-of-two group order alone does not assert exponent two. -/
theorem not_exponent_two : quarter^2 ≠ 1 := by
  rw [pow_two]
  change ((1 : ZMod 4)+1) ≠ 0
  decide

instance trivialAction : MulAction Four Unit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A legitimate nonfaithful auxiliary action; the positive generic action
and coset support must not acquire the faithfulness of actual full Aut(F). -/
theorem nonfaithful_auxiliary_action :
    quarter ≠ 1 ∧ ∀ x : Unit, quarter • x = x := by
  constructor
  · change (1 : ZMod 4) ≠ 0
    decide
  · intro x
    rfl

end GenericGroupScope
end CCO.FiniteFibres.Boundaries
