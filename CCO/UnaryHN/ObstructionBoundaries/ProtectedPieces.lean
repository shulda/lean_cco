import CCO.UnaryHN.ObstructionBoundaries.FreeSplit
import CCO.UnaryHN.ObstructionBoundaries.Path

/-! The protected irreducibles of every n≥4 obstruction are ACTUAL completed
networks. The proof first derives positive pair coverage by a genuine free
split, then uses triangle-freeness of the n-cycle to localize the pieces. -/
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

theorem linked_path_iff {n : ℕ} (x y : Fin n) :
    Linked (path n) x y ↔ Adjacent x y ∨ Endpoints x y := by
  constructor
  · rintro ⟨color, h | h⟩ <;> cases color
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact ⟨false, Or.inl h⟩
    · exact ⟨true, Or.inl h⟩

theorem path_colors_disjoint {n : ℕ} (hn : 4 ≤ n) {x y : Fin n}
    (hR : (path n).rel false ![x, y]) : ¬ (path n).rel true ![x, y] := by
  change Adjacent x y at hR
  change ¬ Endpoints x y
  unfold Adjacent at hR
  unfold Endpoints
  omega

theorem path_no_triangle {n : ℕ} (hn : 4 ≤ n) {x y z : Fin n}
    (hxy : Linked (path n) x y) (hyz : Linked (path n) y z)
    (hxz : Linked (path n) x z) : False := by
  rw [linked_path_iff] at hxy hyz hxz
  unfold Adjacent Endpoints at hxy hyz hxz
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  omega

private theorem diagram_ext {V : Type*} {C D : Diagram V}
    (h : ∀ color xs, C.rel color xs ↔ D.rel color xs) : C = D := by
  cases C with
  | mk cr cf =>
    cases D with
    | mk dr df =>
      have hr : cr = dr := funext (fun color => funext (fun xs => propext (h color xs)))
      have hf : cf = df := funext (fun F => Empty.elim F)
      cases hr
      cases hf
      rfl

/-- This tests arbitrary actual induced irreducibles, not just chosen
singletons or declared edges. Their positive binary diagram is already K. -/
theorem path_irreducibles_completed {n : ℕ} (hn : 4 ≤ n) :
    IrreduciblesIn completed (path n) := by
  intro V C hC e
  have hFinite : Finite V := Finite.of_injective e e.injective
  have hLoop : ∀ color x, ¬ C.rel color ![x, x] := by
    intro color x h
    exact path_irreflexive (by omega) color (e x) ((e.map_rel_iff color _).mpr h)
  have hSymm : ∀ color x y, C.rel color ![x, y] → C.rel color ![y, x] := by
    intro color x y h
    have hp := (e.map_rel_iff color ![x, y]).mpr h
    apply (e.map_rel_iff color ![y, x]).mp
    cases color
    · exact hp.symm
    · exact hp.symm
  have hNoBoth : ∀ x y, C.rel false ![x, y] → ¬ C.rel true ![x, y] := by
    intro x y hR hB
    exact path_colors_disjoint hn ((e.map_rel_iff false _).mpr hR)
      ((e.map_rel_iff true _).mpr hB)
  have hSmall : ∀ x y z : V, x = y ∨ y = z ∨ x = z := by
    intro x y z
    by_cases hxy : x = y
    · exact Or.inl hxy
    · by_cases hyz : y = z
      · exact Or.inr (Or.inl hyz)
      · by_cases hxz : x = z
        · exact Or.inr (Or.inr hxz)
        · exact False.elim (path_no_triangle hn
            (irreducible_image_linked (path n) C hC e hxy)
            (irreducible_image_linked (path n) C hC e hyz)
            (irreducible_image_linked (path n) C hC e hxz))
  let E : Setoid V := {
    r := fun x y => x = y ∨ C.rel false ![x, y]
    iseqv := ⟨fun x => Or.inl rfl, by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (hSymm false x y h), by
      intro x y z hxy hyz
      rcases hSmall x y z with h | h | h
      · exact h ▸ hyz
      · exact h ▸ hxy
      · exact Or.inl h⟩ }
  refine ⟨hFinite, E, diagram_ext ?_⟩
  intro color xs
  rw [← binary_tuple_eta xs]
  cases color
  · change C.rel false ![xs 0, xs 1] ↔
      (xs 0 = xs 1 ∨ C.rel false ![xs 0, xs 1]) ∧ xs 0 ≠ xs 1
    constructor
    · intro h
      exact ⟨Or.inr h, fun heq => hLoop false (xs 0) (heq ▸ h)⟩
    · rintro ⟨heq | h, hne⟩
      · exact False.elim (hne heq)
      · exact h
  · change C.rel true ![xs 0, xs 1] ↔
      ¬ (xs 0 = xs 1 ∨ C.rel false ![xs 0, xs 1])
    constructor
    · intro hB h
      rcases h with hEq | hR
      · exact hLoop true (xs 0) (hEq ▸ hB)
      · exact hNoBoth _ _ hR hB
    · intro h
      have hne : xs 0 ≠ xs 1 := fun heq => h (Or.inl heq)
      obtain ⟨c, hp | hp⟩ := irreducible_image_linked (path n) C hC e hne
      · have hc := (e.map_rel_iff c ![xs 0, xs 1]).mp hp
        cases c
        · exact False.elim (h (Or.inr hc))
        · exact hc
      · have hc := hSymm c _ _ ((e.map_rel_iff c ![xs 1, xs 0]).mp hp)
        cases c
        · exact False.elim (h (Or.inr hc))
        · exact hc

end CCO.UnaryHN.Native.ObstructionBoundaries
