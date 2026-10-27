import CCO.TypedRelation

/-!
# Unconditional elementary group-action exports

Neither quotient lifting nor actual orbital pullback assumes homogeneity, SAP,
CCO, faithful actions or any section of the group homomorphism.
-/

universe u v w z

namespace CCO
namespace GroupActions

variable {K Γ Y B : Type*} [Group K] [Group Γ]
variable [MulAction K Y] [MulAction Γ B]

def FibreTransitive (ρ : K →* Γ) (π : Y → B) : Prop :=
  ∀ x y, π x = π y → ∃ k : K, ρ k = 1 ∧ k • x = y

def PrescribedLift (ρ : K →* Γ) (π : Y → B) : Prop :=
  ∀ x y γ, γ • π x = π y →
    ∃ k : K, ρ k = γ ∧ k • x = y

/-- Prescribed-action point lifting, exactly as in the pinned source:
onto homomorphism plus fibrewise kernel transitivity iff arbitrary
prescribed output-group motions lift on points. -/
theorem prescribed_action_point_lifting [Nonempty Y]
    (ρ : K →* Γ) (π : Y → B)
    (surjπ : Function.Surjective π)
    (equivπ : ∀ k y, π (k • y) = ρ k • π y) :
    (Function.Surjective ρ ∧ FibreTransitive ρ π) ↔
      PrescribedLift ρ π := by
  constructor
  · rintro ⟨surjρ, hfib⟩ x y γ hγ
    obtain ⟨k₀, hk₀⟩ := surjρ γ
    have hπ : π (k₀ • x) = π y := by
      rw [equivπ, hk₀]
      exact hγ
    obtain ⟨k₁, hk₁, hk₁x⟩ := hfib (k₀ • x) y hπ
    refine ⟨k₁ * k₀, ?_, ?_⟩
    · simp [hk₁, hk₀]
    · simpa only [mul_smul] using hk₁x
  · intro hlift
    constructor
    · intro γ
      obtain ⟨x⟩ := ‹Nonempty Y›
      obtain ⟨y, hy⟩ := surjπ (γ • π x)
      obtain ⟨k, hk, _⟩ := hlift x y γ hy.symm
      exact ⟨k, hk⟩
    · intro x y hxy
      have h : (1 : Γ) • π x = π y := by
        simpa only [one_smul] using hxy
      obtain ⟨k, hk, hmove⟩ := hlift x y 1 h
      exact ⟨k, hk, hmove⟩

variable {G A C Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G C]
variable [MulAction G Q] [MulAction G R]

/-- An *actual* ordered pair orbit for the diagonal group action. -/
def orbital (a : A) (b : C) : A → C → Prop :=
  fun x y => ∃ g : G, g • a = x ∧ g • b = y

/-- Full pullback of any represented output relation. -/
def pullback (τ : A → Q) (σ : C → R)
    (Θ : Q → R → Prop) : A → C → Prop :=
  fun x y => Θ (τ x) (σ y)

def kernel (τ : A → Q) : A → A → Prop :=
  fun x y => τ x = τ y

/-- Equality-inclusive RAW saturation `ker τ ; O ; ker σ`,
with both intermediate witnesses exposed. -/
def saturation (τ : A → Q) (σ : C → R)
    (O : A → C → Prop) : A → C → Prop :=
  fun x y => ∃ u v, kernel τ x u ∧ O u v ∧ kernel σ v y

theorem orbital_nonempty (a : A) (b : C) :
    orbital (G := G) a b a b := by
  exact ⟨1, one_smul G a, one_smul G b⟩

theorem orbital_invariant (a : A) (b : C)
    {x : A} {y : C} (h : orbital (G := G) a b x y)
    (g : G) : orbital (G := G) a b (g • x) (g • y) := by
  obtain ⟨k, rfl, rfl⟩ := h
  refine ⟨g * k, ?_, ?_⟩
  · exact mul_smul g k a
  · exact mul_smul g k b

/-- The full pullback of an output orbit is precisely the RAW product
of the two *actual* fibre kernels with one actual original orbital.
No invented quotient atom or choice of representative is used. -/
theorem orbital_pullback
    (τ : A → Q) (σ : C → R)
    (equivτ : ∀ g x, τ (g • x) = g • τ x)
    (equivσ : ∀ g y, σ (g • y) = g • σ y)
    (a : A) (b : C) :
    pullback τ σ (orbital (G := G) (τ a) (σ b)) =
      saturation τ σ (orbital (G := G) a b) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨g, hgτ, hgσ⟩
    refine ⟨g • a, g • b, ?_, ?_, ?_⟩
    · change τ x = τ (g • a)
      rw [equivτ]
      exact hgτ.symm
    · exact ⟨g, rfl, rfl⟩
    · change σ (g • b) = σ y
      rw [equivσ]
      exact hgσ
  · rintro ⟨u, v, hu, ⟨g, hga, hgb⟩, hv⟩
    refine ⟨g, ?_, ?_⟩
    · rw [← equivτ g a, hga]
      exact hu.symm
    · rw [← equivσ g b, hgb]
      exact hv

/-- For an inhabited, transitive original sort, an output orbital
whose pullback contains no distinct pair forces both quotient maps
to be injective. This states the same-sort part of the diagonal
exception without identifying two differently tagged root sorts. -/
theorem no_diversity_injective
    {A Q R : Type*} [MulAction G A]
    [MulAction G Q] [MulAction G R]
    (τ : A → Q) (σ : A → R)
    (equivτ : ∀ g x, τ (g • x) = g • τ x)
    (equivσ : ∀ g x, σ (g • x) = g • σ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y)
    (a b : A)
    (hDiag : ∀ x y : A,
      orbital (G := G) (τ a) (σ b) (τ x) (σ y) → x = y) :
    Function.Injective τ ∧ Function.Injective σ := by
  have hab : a = b := by
    apply hDiag
    exact ⟨1, by simp, by simp⟩
  subst b
  constructor
  · intro x x' heq
    obtain ⟨g, hg⟩ := trans a x
    have hx : x = g • a := hg.symm
    have horb : orbital (G := G) (τ a) (σ a) (τ x') (σ (g • a)) := by
      refine ⟨g, ?_, ?_⟩
      · rw [← equivτ g a, ← hx]
        exact heq.symm
      · rfl
    have h1 := hDiag x' (g • a) horb
    have h2 : x = g • a := hx
    exact h1.trans h2.symm
  · intro x y heq
    obtain ⟨g, hg⟩ := trans a x
    have hx : x = g • a := hg.symm
    have horb : orbital (G := G) (τ a) (σ a) (τ (g • a)) (σ y) := by
      refine ⟨g, ?_, ?_⟩
      · rfl
      · rw [← equivσ g a, ← hx]
        exact heq.symm
    have h1 := hDiag (g • a) y horb
    exact hx.trans h1

end GroupActions
end CCO
