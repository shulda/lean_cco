import CCO.GroupActions

/-!
# Prescribed point lifting from an orbit-covering seed

The conjugation argument uses arbitrary group actions, with no finiteness,
source homogeneity, faithfulness or splitting hypothesis (B018 C12).
-/

namespace CCO.Owners.Provider

variable {K Γ D B : Type*} [Group K] [Group Γ]
variable [MulAction K D] [MulAction Γ B]

/-- Prescribed lifts on an orbit-covering seed give prescribed lifts at
every point, including points added after the seed was selected. -/
theorem prescribedLift_of_seed (ρ : K →* Γ) (π : D → B)
    (equivariant : ∀ g x, π (g • x) = ρ g • π x)
    (A₀ : Set D)
    (cover : ∀ x : D, ∃ g : K, g • x ∈ A₀)
    (seedLift : ∀ a ∈ A₀, ∀ a' ∈ A₀, ∀ γ : Γ,
      γ • π a = π a' → ∃ k : K, ρ k = γ ∧ k • a = a') :
    GroupActions.PrescribedLift ρ π := by
  intro x y γ hγ
  obtain ⟨g, hg⟩ := cover x
  obtain ⟨h, hh⟩ := cover y
  let δ : Γ := ρ h * γ * (ρ g)⁻¹
  have hδ : δ • π (g • x) = π (h • y) := by
    rw [equivariant g x, equivariant h y]
    simp only [δ, mul_smul, inv_smul_smul, hγ]
  obtain ⟨k, hk, hka⟩ := seedLift (g • x) hg (h • y) hh δ hδ
  refine ⟨h⁻¹ * k * g, ?_, ?_⟩
  · simp [map_mul, map_inv, hk, δ, mul_assoc]
  · simpa only [mul_smul, inv_smul_smul] using congrArg (h⁻¹ • ·) hka

/-- On a nonempty surjective quotient, the same actual seed construction
supplies an onto owner action and a fibre-transitive kernel. -/
theorem seed_owner_action [Nonempty D]
    (ρ : K →* Γ) (π : D → B) (surjective : Function.Surjective π)
    (equivariant : ∀ g x, π (g • x) = ρ g • π x)
    (A₀ : Set D)
    (cover : ∀ x : D, ∃ g : K, g • x ∈ A₀)
    (seedLift : ∀ a ∈ A₀, ∀ a' ∈ A₀, ∀ γ : Γ,
      γ • π a = π a' → ∃ k : K, ρ k = γ ∧ k • a = a') :
    Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π :=
  (GroupActions.prescribed_action_point_lifting ρ π surjective equivariant).mpr
    (prescribedLift_of_seed ρ π equivariant A₀ cover seedLift)

end CCO.Owners.Provider
