import CCO.UnaryHN.ObstructionBoundaries.Basic
import Mathlib.Tactic.FinCases

/-! Genuine native free decomposition across a missing binary edge. Thus
an actual irreducible subobject has complete positive pair coverage; this
is proved from the free-amalgamation definition, not assumed as a shortcut. -/
universe u
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

def Linked {V : Type u} (C : Diagram V) (x y : V) : Prop :=
  ∃ color, C.rel color ![x, y] ∨ C.rel color ![y, x]

theorem binary_tuple_eta {V : Type u} (xs : Fin 2 → V) : ![xs 0, xs 1] = xs := by
  funext i
  fin_cases i <;> rfl

private def between {V : Type u} (C : Diagram V) (S T : Set V) (h : S ⊆ T) :
    Embedding (C.induce S (every_set_closed C S)) (C.induce T (every_set_closed C T)) where
  toFun x := ⟨x.val, h x.property⟩
  injective := fun _ _ hh => Subtype.ext (congrArg (fun z : T => z.val) hh)
  map_rel_iff _ _ := Iff.rfl
  map_func F := Empty.elim F

private def leftSet {V : Type u} (x : V) : Set V := {z | z ≠ x}
private def rootSet {V : Type u} (x y : V) : Set V := {z | z ≠ x ∧ z ≠ y}

private def rootLeft {V : Type u} (C : Diagram V) (x y : V) :=
  between C (rootSet x y) (leftSet x) (fun _ h => h.1)
private def rootRight {V : Type u} (C : Diagram V) (x y : V) :=
  between C (rootSet x y) (leftSet y) (fun _ h => h.2)
private def intoLeft {V : Type u} (C : Diagram V) (x : V) :=
  inclusion C (leftSet x) (every_set_closed C _)

private theorem binary_tuple_side {V : Type u} (C : Diagram V) {x y : V}
    (hxy : x ≠ y) (hNo : ¬ Linked C x y) (color : Bool) (xs : Fin 2 → V)
    (hRel : C.rel color xs) :
    (∀ i, xs i ≠ x) ∨ (∀ i, xs i ≠ y) := by
  classical
  have hNoXY : ¬ C.rel color ![x, y] := fun h => hNo ⟨color, Or.inl h⟩
  have hNoYX : ¬ C.rel color ![y, x] := fun h => hNo ⟨color, Or.inr h⟩
  by_cases h0 : xs 0 = x
  · right
    have h1 : xs 1 ≠ y := by
      intro hy
      have ht : xs = ![x, y] := by rw [← binary_tuple_eta xs, h0, hy]
      exact hNoXY (ht ▸ hRel)
    intro i
    fin_cases i
    · exact h0 ▸ hxy
    · exact h1
  · by_cases h1 : xs 1 = x
    · right
      have hy : xs 0 ≠ y := by
        intro h
        have ht : xs = ![y, x] := by rw [← binary_tuple_eta xs, h, h1]
        exact hNoYX (ht ▸ hRel)
      intro i
      fin_cases i
      · exact hy
      · exact h1 ▸ hxy
    · left
      intro i
      fin_cases i
      · exact h0
      · exact h1

/-- Both sides and the overlap are literal induced closed substructures of
C, with exactly their original relation diagrams. -/
private theorem missing_edge_free {V : Type u} (C : Diagram V) {x y : V}
    (hxy : x ≠ y) (hNo : ¬ Linked C x y) :
    IsFreeAmalgam (rootLeft C x y) (rootRight C x y) (intoLeft C x) (intoLeft C y) where
  covers := by
    intro z
    by_cases hz : z ≠ x
    · exact Or.inl ⟨⟨z, hz⟩, rfl⟩
    · have hzx : z = x := not_ne_iff.mp hz
      exact Or.inr ⟨⟨z, hzx ▸ hxy⟩, rfl⟩
  overlap := by
    intro a b
    constructor
    · intro h
      change a.val = b.val at h
      refine ⟨⟨a.val, a.property, ?_⟩, ?_, ?_⟩
      · exact h ▸ b.property
      · rfl
      · exact Subtype.ext h.symm
    · rintro ⟨z, rfl, rfl⟩
      rfl
  rel_iff := by
    intro color xs
    constructor
    · intro hRel
      rcases binary_tuple_side C hxy hNo color xs hRel with hL | hR
      · exact Or.inl ⟨fun i => ⟨xs i, hL i⟩, hRel, rfl⟩
      · exact Or.inr ⟨fun i => ⟨xs i, hR i⟩, hRel, rfl⟩
    · rintro (⟨ys, hRel, hEq⟩ | ⟨ys, hRel, hEq⟩)
      · rw [hEq]
        exact hRel
      · rw [hEq]
        exact hRel
  func_iff F := Empty.elim F

/-- Every two distinct points in the image of any actual irreducible
source have a displayed positive binary edge in one orientation. -/
theorem irreducible_image_linked {V W : Type u} (C : Diagram V) (E : Diagram W)
    (hE : E.Irreducible) (e : Embedding E C) {a b : W} (hab : a ≠ b) :
    Linked C (e a) (e b) := by
  classical
  by_contra hNo
  have hxy := e.injective.ne hab
  rcases hE (missing_edge_free C hxy hNo) e with hL | hR
  · obtain ⟨z, hz⟩ := hL a
    exact z.property hz.symm
  · obtain ⟨z, hz⟩ := hR b
    exact z.property hz.symm

end CCO.UnaryHN.Native.ObstructionBoundaries
