import CCO.PairHomogeneity
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Finset.Image

/-!
# The original real two-class obstruction

The named finite parameter set is fixed POINTWISE in `PointwiseType`.
Only the singleton consequences of SIR existence, invariance and
empty-base stationarity are used. They are recorded explicitly, without
assuming disjointness, free amalgamation, SAP, or countability.
-/

universe u v w

namespace CCO.SIR.Negative

variable {G A : Type*} [Group G] [MulAction G A]

/-- Transport of a finite real set by an actual automorphism. -/
def transport (g : G) (B : Finset A) : Finset A :=
  B.map (MulAction.toPerm g).toEmbedding

/-- Equality of singleton types over individually named real parameters. -/
def PointwiseType (B : Finset A) (x y : A) : Prop :=
  ∃ g : G, (∀ b ∈ B, g • b = b) ∧ g • x = y

/-- The three singleton consequences needed from any real finite-set SIR.
This is a reduct of the SIR axioms, rather than a positive SIR constructor. -/
structure EmptyBaseSingletonAxioms
    (I : Finset A → Finset A → Finset A → Prop) : Prop where
  existence : ∀ B : Finset A, ∃ x : A, I {x} ∅ B
  invariance : ∀ (g : G) (U C B : Finset A), I U C B →
    I (transport g U) (transport g C) (transport g B)
  stationarity : ∀ (B : Finset A) (x y : A),
    PointwiseType (G := G) ∅ x y → I {x} ∅ B → I {y} ∅ B →
      PointwiseType (G := G) B x y

/-- Invariance of an actual equivalence works in both directions. -/
theorem invariant_setoid_iff (E : Setoid A)
    (hE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (g : G) (x y : A) : E (g • x) (g • y) ↔ E x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using hE g⁻¹ (g • x) (g • y) h
  · exact hE g x y

/-- The abstract class-swap obstruction. The automorphism preserves the
representative pair as a set, while stationarity fixes each name. -/
theorem no_singleton_axioms_of_two_class_swap
    (E : Setoid A)
    (hInv : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (a₀ a₁ : A) (hne : ¬ E a₀ a₁)
    (hclasses : ∀ x, E x a₀ ∨ E x a₁)
    (σ : G) (hσ₀ : σ • a₀ = a₁) (hσ₁ : σ • a₁ = a₀)
    (I : Finset A → Finset A → Finset A → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  classical
  intro hI
  let B : Finset A := {a₀, a₁}
  obtain ⟨x, hx⟩ := hI.existence B
  have hB : transport σ B = B := by
    simp [transport, B, hσ₀, hσ₁, Finset.pair_comm]
  have hσx : I {σ • x} ∅ B := by
    simpa only [transport, Finset.map_singleton, Finset.map_empty, Equiv.coe_toEmbedding,
      MulAction.toPerm_apply] using
      (show I (transport σ {x}) (transport σ ∅) B from by
        rw [← hB]
        exact hI.invariance σ {x} ∅ B hx)
  have htype : PointwiseType (G := G) ∅ x (σ • x) :=
    ⟨σ, by simp, rfl⟩
  obtain ⟨τ, hτ, hτx⟩ := hI.stationarity B x (σ • x) htype hx hσx
  have ht₀ : τ • a₀ = a₀ := hτ a₀ (by simp [B])
  have ht₁ : τ • a₁ = a₁ := hτ a₁ (by simp [B])
  rcases hclasses x with h₀ | h₁
  · have hs₁ : E (σ • x) a₁ := by simpa only [hσ₀] using hInv σ x a₀ h₀
    have hs₀ : E (σ • x) a₀ := by simpa only [hτx, ht₀] using hInv τ x a₀ h₀
    exact hne (E.trans (E.symm hs₀) hs₁)
  · have hs₀ : E (σ • x) a₀ := by simpa only [hσ₁] using hInv σ x a₁ h₁
    have hs₁ : E (σ • x) a₁ := by simpa only [hτx, ht₁] using hInv τ x a₁ h₁
    exact hne (E.trans (E.symm hs₀) hs₁)

section OriginalSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable [∀ i : ι, MulAction G (X i)]

/-- C15: actual two-point homogeneity in the original symmetric diversity
language extends the swap; the true singleton diagonal is retained. -/
theorem original_representative_swap (H : HomogeneousSource S G)
    {i : ι} (a₀ a₁ : X i) :
    ∃ σ : G, σ • a₀ = a₁ ∧ σ • a₁ = a₀ :=
  S.pair_flip_of_homogeneous H a₀ a₁

/-- The representative swap interchanges their ENTIRE invariant classes.
This makes the global action on the two classes explicit. -/
theorem original_global_class_swap (H : HomogeneousSource S G)
    {i : ι} (E : Setoid (X i))
    (hInv : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (a₀ a₁ : X i) :
    ∃ σ : G, σ • a₀ = a₁ ∧ σ • a₁ = a₀ ∧
      (∀ x, E (σ • x) a₀ ↔ E x a₁) ∧
      (∀ x, E (σ • x) a₁ ↔ E x a₀) := by
  obtain ⟨σ, hσ₀, hσ₁⟩ := original_representative_swap S H a₀ a₁
  refine ⟨σ, hσ₀, hσ₁, ?_, ?_⟩
  · intro x
    simpa only [hσ₁] using invariant_setoid_iff E hInv σ x a₁
  · intro x
    simpa only [hσ₀] using invariant_setoid_iff E hInv σ x a₀

/-- C16: the standing source supplies the required global class swap.
The type conclusion is over the POINTWISE named representative pair. -/
theorem original_two_class_obstruction (H : HomogeneousSource S G)
    {i : ι} (E : Setoid (X i))
    (hInv : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (a₀ a₁ : X i) (hne : ¬ E a₀ a₁)
    (hclasses : ∀ x, E x a₀ ∨ E x a₁)
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  obtain ⟨σ, hσ₀, hσ₁⟩ := original_representative_swap S H a₀ a₁
  exact no_singleton_axioms_of_two_class_swap E hInv a₀ a₁ hne hclasses σ hσ₀ hσ₁ I

end OriginalSource

end CCO.SIR.Negative
