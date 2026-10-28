import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Abel

/-! Finite translate Helly forces an affine subgroup coset. The explicit
maximal affine-subspace argument uses subgroup cardinality instead of rank;
adjoining an outside vector constructs exactly the two cosets K and a+K.
No relational source or exact-menu premise enters this elementary lemma. -/

universe u
namespace CCO.RigidGroupoid.Phase

variable {V : Type u} [AddCommGroup V]

/-- All finite families of translates, with all pair intersections retained.
For nonempty A the self-pairs are automatic, so this is ordinary pairwise
intersection Helly, including the empty family. -/
def TranslateHelly (A : Set V) : Prop :=
  ∀ F : Finset V,
    (∀ u ∈ F, ∀ v ∈ F, ∃ x, x + u ∈ A ∧ x + v ∈ A) →
    ∃ z, ∀ w ∈ F, z + w ∈ A

private def enlarge (K : AddSubgroup V) (a : V)
    (h2 : ∀ x : V, x + x = 0) : AddSubgroup V where
  carrier := {x | x ∈ K ∨ x + a ∈ K}
  zero_mem' := Or.inl K.zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (K.add_mem hx hy)
    · exact Or.inr (by simpa only [add_assoc] using K.add_mem hx hy)
    · apply Or.inr
      convert K.add_mem hx hy using 1 <;> abel
    · apply Or.inl
      have hh := K.add_mem hx hy
      have he : (x + a) + (y + a) = x + y := by
        calc
          _ = x + y + (a + a) := by abel
          _ = x + y := by rw [h2, add_zero]
      rwa [he] at hh
  neg_mem' := by
    intro x hx
    have hn : -x = x := by
      calc
        -x = -x + (x + x) := by rw [h2, add_zero]
        _ = x := by rw [← add_assoc, neg_add_cancel, zero_add]
    simpa only [hn] using hx

theorem affine_coset_of_translate_helly [Finite V]
    (h2 : ∀ x : V, x + x = 0) (A : Set V) (hA : A.Nonempty)
    (hHelly : TranslateHelly A) :
    ∃ (z : V) (K : AddSubgroup V), A = {x | x - z ∈ K} := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (z : V) (K : AddSubgroup V), (∀ k ∈ K, z + k ∈ A) ∧ Nat.card K = n
  obtain ⟨a0, ha0⟩ := hA
  let K0 : AddSubgroup V := ⊥
  have hseed : P (Nat.card K0) := by
    refine ⟨a0, K0, ?_, rfl⟩
    intro k hk
    have hk0 : k = 0 := hk
    simpa only [hk0, add_zero] using ha0
  have hbound (K : AddSubgroup V) : Nat.card K ≤ Nat.card V :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  obtain ⟨z, K, hK, hcard⟩ := Nat.findGreatest_spec (hbound K0) hseed
  have hmax (L : AddSubgroup V) (w : V) (hw : ∀ k ∈ L, w + k ∈ A) :
      Nat.card L ≤ Nat.card K := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound L) ⟨w, L, hw, rfl⟩
  have hsub : ∀ a : V, z + a ∈ A → a ∈ K := by
    intro a ha
    by_contra haK
    let W := enlarge K a h2
    have hKW : ∀ x ∈ K, x ∈ W := fun _ hx => Or.inl hx
    have haW : a ∈ W := Or.inr (by rw [h2]; exact K.zero_mem)
    let F : Finset V := (Set.toFinite (W : Set V)).toFinset
    have hF (x : V) : x ∈ F ↔ x ∈ W := Set.Finite.mem_toFinset _
    obtain ⟨w, hw⟩ := hHelly F (by
      intro u hu v hv
      have huv := W.add_mem ((hF u).mp hu) ((hF v).mp hv)
      change u + v ∈ K ∨ (u + v) + a ∈ K at huv
      rcases huv with huv | huv
      · refine ⟨z + u, ?_, ?_⟩
        · simpa only [add_assoc, h2, add_zero] using hK 0 K.zero_mem
        · simpa only [add_assoc] using hK (u + v) huv
      · refine ⟨z + a + u, ?_, ?_⟩
        · simpa only [add_assoc, h2, add_zero] using ha
        · convert hK ((u + v) + a) huv using 1 <;> abel)
    have hlarge : Nat.card W ≤ Nat.card K :=
      hmax W w (fun k hk => hw k ((hF k).mpr hk))
    let inc : K → W := fun k => ⟨k.val, hKW k.val k.property⟩
    have hinj : Function.Injective inc := by
      intro k l h
      exact Subtype.ext (congrArg (fun y : W => y.val) h)
    have hc : Nat.card K = Nat.card W :=
      le_antisymm (Nat.card_le_card_of_injective inc hinj) hlarge
    have hsurj := (Nat.bijective_iff_injective_and_card inc).mpr ⟨hinj, hc⟩
    obtain ⟨k, hk⟩ := hsurj.2 ⟨a, haW⟩
    have hka : k.val = a := congrArg (fun y : W => y.val) hk
    exact haK (hka ▸ k.property)
  refine ⟨z, K, ?_⟩
  ext x
  have he : z + (x - z) = x := by abel
  constructor
  · intro hx
    exact hsub (x - z) (he.symm ▸ hx)
  · intro hx
    exact he ▸ hK (x - z) hx

theorem affine_coset_of_f2_translate_helly [Module (ZMod 2) V] [Finite V]
    (A : Set V) (hA : A.Nonempty) (hHelly : TranslateHelly A) :
    ∃ (z : V) (K : AddSubgroup V), A = {x | x - z ∈ K} := by
  apply affine_coset_of_translate_helly (A := A) (hA := hA) (hHelly := hHelly)
  intro x
  calc
    x + x = (1 + 1 : ZMod 2) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]

end CCO.RigidGroupoid.Phase
