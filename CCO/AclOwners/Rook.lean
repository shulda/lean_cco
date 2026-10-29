import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Basic

/-! The two-equivalence rook argument and its finite-family consumer.
No finiteness, nonempty clique, source, palette or action premise is used.
The index type need only be nonempty to name a vacuous exceptional index. -/

universe u v
namespace CCO.AclOwners

variable {M : Type u}

/-- Every ordered pair of a set is in one equivalence relation. -/
def Concentrated (E : Setoid M) (Z : Set M) : Prop :=
  ∀ x ∈ Z, ∀ y ∈ Z, E x y

/-- C14: a set covered pairwise by TWO equivalences is contained pairwise
in one of them. Empty and singleton sets satisfy the same statement. -/
theorem two_equivalence_rook (E F : Setoid M) (Z : Set M)
    (hpair : ∀ x ∈ Z, ∀ y ∈ Z, E x y ∨ F x y) :
    Concentrated E Z ∨ Concentrated F Z := by
  classical
  by_cases hF : Concentrated F Z
  · exact Or.inr hF
  · left
    have hex : ∃ x ∈ Z, ∃ y ∈ Z, ¬ F x y := by
      by_contra hn
      apply hF
      intro x hx y hy
      by_contra hxy
      exact hn ⟨x,hx,y,hy,hxy⟩
    obtain ⟨x,hx,y,hy,hxy⟩ := hex
    have hExy : E x y := (hpair x hx y hy).resolve_right hxy
    have hxz : ∀ z ∈ Z, E x z := by
      intro z hz
      by_contra hxz
      have hFxz : F x z := (hpair x hx z hz).resolve_left hxz
      have hEyz : ¬ E y z := fun hyz => hxz (E.trans hExy hyz)
      have hFyz : F y z := (hpair y hy z hz).resolve_left hEyz
      exact hxy (F.trans hFxz (F.symm hFyz))
    intro a ha b hb
    exact E.trans (E.symm (hxz a ha)) (hxz b hb)

/-- Concentration gives the class containment for EVERY selected root in
that set. No arbitrary root has to be chosen for an empty set. -/
theorem concentrated_subset_class (E : Setoid M) (Z : Set M)
    (h : Concentrated E Z) {z : M} (hz : z ∈ Z) : Z ⊆ {x | E z x} :=
  fun x hx => h z hz x hx

/-- A pairwise family of rook alternatives has at most one unconcentrated
index. The index family may be infinite; nonemptiness is used only when
all indices are concentrated and an exceptional name is requested. -/
theorem all_but_one_concentrated {I : Type v} [Nonempty I]
    (R : I → Setoid M) (Z : Set M)
    (hpair : ∀ i j : I, i ≠ j → Concentrated (R i) Z ∨ Concentrated (R j) Z) :
    ∃ i₀ : I, ∀ j : I, j ≠ i₀ → Concentrated (R j) Z := by
  classical
  by_cases hall : ∀ i : I, Concentrated (R i) Z
  · exact ⟨Classical.choice inferInstance,fun j _ => hall j⟩
  · obtain ⟨i₀,hi₀⟩ := Classical.not_forall.mp hall
    exact ⟨i₀,fun j hj => (hpair j i₀ hj).resolve_right hi₀⟩

/-- The class form keeps the SAME selected root for every nonexceptional
coordinate. -/
theorem all_but_one_root_classes {I : Type v} [Nonempty I]
    (R : I → Setoid M) (Z : Set M)
    (hpair : ∀ i j : I, i ≠ j → Concentrated (R i) Z ∨ Concentrated (R j) Z) :
    ∃ i₀ : I, ∀ j : I, j ≠ i₀ → ∀ z ∈ Z, Z ⊆ {x | R j z x} := by
  obtain ⟨i₀,hi₀⟩ := all_but_one_concentrated R Z hpair
  exact ⟨i₀,fun j hj z hz => concentrated_subset_class (R j) Z (hi₀ j hj) hz⟩

end CCO.AclOwners
