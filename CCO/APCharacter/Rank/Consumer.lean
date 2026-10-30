import CCO.APCharacter.Rank.Orbitals
import CCO.APCharacter.Rank.Potential
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! The numerical decrease is instantiated on the actual occurring palettes
of the constructed unary source, including unchanged inactive sorts. -/
universe u v w t
namespace CCO.APCharacter.Rank
open scoped BigOperators
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (β : ι → Type t) (tag : ∀ i, X i → β i)
variable [∀ i, Fintype (β i)] (inhabited : ∀ c, Nonempty (Point β tag c))

noncomputable def childWeight (i : ι) : ℕ :=
  ∑ b : β i, 3 ^ Nat.card ((source S β tag inhabited).Atom ⟨i,b⟩ ⟨i,b⟩)

theorem active_weight_le (i : ι) (hcard : Fintype.card (β i) = 2)
    (a : S.Atom i i) (missing : ∀ b : β i, ¬ Occurs S β tag ⟨i,b⟩ ⟨i,b⟩ a) :
    childWeight S β tag inhabited i ≤ 2 * 3 ^ (Nat.card (S.Atom i i) - 1) := by
  classical
  calc
    childWeight S β tag inhabited i ≤ ∑ _b : β i, 3 ^ (Nat.card (S.Atom i i) - 1) := by
      apply Finset.sum_le_sum
      intro b _
      exact pow_le_pow_right' (by decide)
        (child_card_le_pred S β tag inhabited ⟨i,b⟩ a (missing b))
    _ = _ := by simp [hcard, Nat.mul_comm]

theorem inactive_weight (i : ι) (hcard : Fintype.card (β i) = 1) :
    childWeight S β tag inhabited i = 3 ^ Nat.card (S.Atom i i) := by
  classical
  letI : Subsingleton (β i) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  simp [childWeight,inactive_card,hcard]

/-- This is ACR for the actual child-source cardinalities, not supplied ranks.
Whole-expanded homogeneity identifies these palettes with actual pair orbitals
by `same_old_colour_iff_orbit` and `child_colour_is_actual_orbital`. -/
theorem actual_palette_rank_drop (A : Finset ι) (hA : A.Nonempty)
    (active_two : ∀ i ∈ A, Fintype.card (β i) = 2)
    (inactive_one : ∀ i ∉ A, Fintype.card (β i) = 1)
    (lost : ∀ i ∈ A, ∃ a : S.Atom i i,
      ∀ b : β i, ¬ Occurs S β tag ⟨i,b⟩ ⟨i,b⟩ a) :
    letI := S.finiteSort
    potential (fun c : Child β => Nat.card ((source S β tag inhabited).Atom c c)) ≤
      potential (fun i => Nat.card (S.Atom i i)) - ∑ i ∈ A, 3 ^ Nat.card (S.Atom i i) +
        ∑ i ∈ A, 2 * 3 ^ (Nat.card (S.Atom i i) - 1) ∧
    potential (fun i => Nat.card (S.Atom i i)) - ∑ i ∈ A, 3 ^ Nat.card (S.Atom i i) +
        ∑ i ∈ A, 2 * 3 ^ (Nat.card (S.Atom i i) - 1) <
      potential (fun i => Nat.card (S.Atom i i)) := by
  classical
  letI := S.finiteSort
  let k := fun i => Nat.card (S.Atom i i)
  have hk : ∀ i ∈ A, 1 ≤ k i := by
    intro i hi
    obtain ⟨a,_⟩ := lost i hi
    letI := S.finiteAtom
    letI : Nonempty (S.Atom i i) := ⟨a⟩
    exact Nat.card_pos
  have hbound : potential (fun c : Child β => Nat.card ((source S β tag inhabited).Atom c c)) ≤
      upperPotential A k := by
    change (∑ c : Child β, 3 ^ Nat.card ((source S β tag inhabited).Atom c c)) ≤ _
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ∈ A
    · simp only [if_pos hi]
      obtain ⟨a,ha⟩ := lost i hi
      exact active_weight_le S β tag inhabited i (active_two i hi) a ha
    · simp only [if_neg hi]
      exact (inactive_weight S β tag inhabited i (inactive_one i hi)).le
  have hACR := exact_character_rank_drop A k (fun i => k i - 1) (fun i => k i - 1)
    hA hk (by intros; rfl) (by intros; rfl)
  have heq : refinedPotential A k (fun i => k i - 1) (fun i => k i - 1) = upperPotential A k := by
    simp only [refinedPotential,upperPotential,two_mul]
  rw [heq] at hACR
  exact ⟨hbound.trans hACR.1,hACR.2⟩

/-- Complete standalone rank assertion: old and new cardinalities count
genuine diversity orbitals, with recognition justified by homogeneity of
the entire sources.  There is no AP, SAP or CCO hypothesis. -/
theorem homogeneous_character_rank_drop
    {G₀ G₁ : Type*} [Group G₀] [Group G₁]
    [∀ i, MulAction G₀ (X i)] [∀ c, MulAction G₁ (Point β tag c)]
    (H₀ : HomogeneousSource S G₀)
    (H₁ : HomogeneousSource (source S β tag inhabited) G₁)
    (A : Finset ι) (hA : A.Nonempty)
    (active_two : ∀ i ∈ A, Fintype.card (β i) = 2)
    (inactive_one : ∀ i ∉ A, Fintype.card (β i) = 1)
    (lost : ∀ i ∈ A, ∃ a : S.Atom i i,
      ∀ b : β i, ¬ Occurs S β tag ⟨i,b⟩ ⟨i,b⟩ a) :
    letI := S.finiteSort
    (∀ i (a : S.Atom i i), ∃ x y : X i,
      S.atomRel a x y ∧ S.atomRel a = GroupActions.orbital (G := G₀) x y) ∧
    (∀ c (a : (source S β tag inhabited).Atom c c), ∃ x y : Point β tag c,
      (source S β tag inhabited).atomRel a x y ∧
      (source S β tag inhabited).atomRel a = GroupActions.orbital (G := G₁) x y) ∧
    (potential (fun c : Child β => Nat.card ((source S β tag inhabited).Atom c c)) ≤
      potential (fun i => Nat.card (S.Atom i i)) - ∑ i ∈ A, 3 ^ Nat.card (S.Atom i i) +
        ∑ i ∈ A, 2 * 3 ^ (Nat.card (S.Atom i i) - 1)) ∧
    (potential (fun i => Nat.card (S.Atom i i)) - ∑ i ∈ A, 3 ^ Nat.card (S.Atom i i) +
        ∑ i ∈ A, 2 * 3 ^ (Nat.card (S.Atom i i) - 1) <
      potential (fun i => Nat.card (S.Atom i i))) := by
  letI := S.finiteSort
  exact ⟨fun _ a => S.diversity_atom_is_orbital_of_homogeneous H₀ a,
    fun _ a => child_colour_is_actual_orbital S β tag inhabited H₁ a,
    actual_palette_rank_drop S β tag inhabited A hA active_two inactive_one lost⟩

end CCO.APCharacter.Rank
