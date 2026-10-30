import CCO.UnaryHN.NativeTransferBasis
import Mathlib.Data.Fin.VecNotation

/-! A concrete one-sorted, function-free language with the two positive
binary colors R (same equivalence class, distinct) and B (different class).
The completed class contains ALL finite equivalence-colored networks. -/
universe u v
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

abbrev language : Language where
  RelSymbol := Bool
  FuncSymbol := Empty
  relArity _ := 2
  funcArity := Empty.elim

abbrev Diagram (V : Type u) := Structure language V

def network {V : Type u} (E : Setoid V) : Diagram V where
  rel color xs := if color then ¬ E.r (xs 0) (xs 1)
    else E.r (xs 0) (xs 1) ∧ xs 0 ≠ xs 1
  func F := Empty.elim F

def completed : Class.{0,u} language := fun {V} C =>
  Finite V ∧ ∃ E : Setoid V, C = network E

theorem completed_network {V : Type u} [Finite V] (E : Setoid V) :
    completed (network E) := ⟨inferInstance, E, rfl⟩

theorem unary : Unary language := fun F => Empty.elim F

theorem singleton {V : Type u} (C : Diagram V) : C.SingletonValued :=
  fun F => Empty.elim F

theorem every_set_closed {V : Type u} (C : Diagram V) (S : Set V) : C.IsClosed S :=
  fun F => Empty.elim F

theorem network_irreflexive {V : Type u} (E : Setoid V) (color : Bool) (x : V) :
    ¬ (network E).rel color ![x, x] := by
  cases color
  · exact fun h => h.2 rfl
  · exact fun h => h (E.refl x)

theorem network_coverage {V : Type u} (E : Setoid V) {x y : V} (h : x ≠ y) :
    ∃ color, (network E).rel color ![x, y] := by
  classical
  by_cases he : E.r x y
  · exact ⟨false, he, h⟩
  · exact ⟨true, he⟩

/-- Actual finite hereditary closure, through full induced embeddings. -/
theorem completed_hereditary : Hereditary (completed.{u}) := by
  intro V W C D hD e
  obtain ⟨hW, E, rfl⟩ := hD
  refine ⟨Finite.of_injective e e.injective, E.comap e, ?_⟩
  cases C with
  | mk rel func =>
    congr 1
    · funext color xs
      apply propext
      have h := e.map_rel_iff color xs
      cases color with
      | false =>
        change rel false xs ↔ E.r (e (xs 0)) (e (xs 1)) ∧ xs 0 ≠ xs 1
        simpa only [network, Function.comp_apply, Bool.false_eq_true, ↓reduceIte,
          e.injective.ne_iff] using h.symm
      | true =>
        change rel true xs ↔ ¬ E.r (e (xs 0)) (e (xs 1))
        exact h.symm
    · funext F
      exact Empty.elim F

/-- Complete binary coverage proves genuine free-amalgamation irreducibility. -/
theorem network_irreducible {V : Type u} (E : Setoid V) : (network E).Irreducible := by
  classical
  intro H A B C Root Left Right Whole sL sR iL iR hFree e
  by_cases hLeft : ∀ x, ∃ a, e x = iL a
  · exact Or.inl hLeft
  · right
    by_contra hRight
    push_neg at hLeft hRight
    obtain ⟨x, hx⟩ := hLeft
    obtain ⟨y, hy⟩ := hRight
    have hxy : x ≠ y := by
      intro h
      subst y
      rcases hFree.covers (e x) with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact hx a ha
      · exact hy b hb
    obtain ⟨color, hColor⟩ := network_coverage E hxy
    have hRel := (e.map_rel_iff color ![x, y]).mpr hColor
    rcases (hFree.rel_iff color (e ∘ ![x, y])).mp hRel with
      ⟨xs, _, heq⟩ | ⟨ys, _, heq⟩
    · exact hx (xs 0) (congrFun heq 0)
    · exact hy (ys 1) (congrFun heq 1)

theorem completed_irreducible : AllIrreducible (completed.{u}) := by
  rintro V C ⟨_, E, rfl⟩
  exact network_irreducible E

end CCO.UnaryHN.Native.ObstructionBoundaries
