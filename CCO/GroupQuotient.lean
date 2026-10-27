import CCO.GroupActions

/-!
# Actual orbital pullback: output-orbital partition and the empty-diversity case

These arguments are statements about *actual* group orbits and *actual*
fibre kernels.  In particular, `orbital` is never an invented atomic
colour and `saturation` keeps equality witnesses.
-/

namespace CCO.GroupActions

section OrbitalPartition

variable {G U V : Type*} [Group G]
variable [MulAction G U] [MulAction G V]

theorem orbital_eq_of_mem (a : U) (b : V) (x : U) (y : V)
    (h : orbital (G := G) a b x y) :
    orbital (G := G) a b = orbital (G := G) x y := by
  rcases h with ⟨g, rfl, rfl⟩
  funext u v
  apply propext
  constructor
  · rintro ⟨k, hku, hkv⟩
    refine ⟨k * g⁻¹, ?_, ?_⟩
    · simpa only [mul_smul, inv_smul_smul] using hku
    · simpa only [mul_smul, inv_smul_smul] using hkv
  · rintro ⟨k, hku, hkv⟩
    refine ⟨k * g, ?_, ?_⟩
    · simpa only [mul_smul] using hku
    · simpa only [mul_smul] using hkv

theorem orbital_eq_of_common_pair
    (a a' x : U) (b b' y : V)
    (h : orbital (G := G) a b x y)
    (h' : orbital (G := G) a' b' x y) :
    orbital (G := G) a b = orbital (G := G) a' b' := by
  calc
    orbital (G := G) a b = orbital (G := G) x y :=
      orbital_eq_of_mem a b x y h
    _ = orbital (G := G) a' b' :=
      (orbital_eq_of_mem a' b' x y h').symm

end OrbitalPartition

section Quotients

variable {G A B Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G B]
variable [MulAction G Q] [MulAction G R]

theorem output_orbital_pullbacks_partition_on_overlap
    (τ : A → Q) (σ : B → R)
    (q q' : Q) (r r' : R) (x : A) (y : B)
    (h : pullback τ σ (orbital (G := G) q r) x y)
    (h' : pullback τ σ (orbital (G := G) q' r') x y) :
    pullback τ σ (orbital (G := G) q r) =
      pullback τ σ (orbital (G := G) q' r') := by
  exact congrArg (pullback τ σ)
    (orbital_eq_of_common_pair q q' (τ x) r r' (σ y) h h')

theorem output_orbital_pullbacks_cover
    (τ : A → Q) (σ : B → R) (x : A) (y : B) :
    ∃ q : Q, ∃ r : R,
      pullback τ σ (orbital (G := G) q r) x y := by
  exact ⟨τ x, σ y, orbital_nonempty (G := G) (τ x) (σ y)⟩

theorem root_orbital_has_unique_output_orbit
    (τ : A → Q) (σ : B → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (a : A) (b : B) :
    ∀ x y, orbital (G := G) a b x y →
      pullback τ σ (orbital (G := G) (τ a) (σ b)) x y := by
  rintro x y ⟨g, rfl, rfl⟩
  exact ⟨g, (equivτ g a).symm, (equivσ g b).symm⟩

/-- Every actual output pair orbit, not just one selected named orbit,
has the equality-inclusive saturation description. -/
theorem any_output_orbital_pullback
    (τ : A → Q) (σ : B → R)
    (surjτ : Function.Surjective τ)
    (surjσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    ∃ a : A, ∃ b : B,
      pullback τ σ (orbital (G := G) q r) =
        saturation τ σ (orbital (G := G) a b) := by
  obtain ⟨a, ha⟩ := surjτ q
  obtain ⟨b, hb⟩ := surjσ r
  refine ⟨a, b, ?_⟩
  subst q
  subst r
  exact orbital_pullback τ σ equivτ equivσ a b

end Quotients

section SameRoot

variable {G A Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G Q] [MulAction G R]

theorem kernel_is_equality_iff_injective (τ : A → Q) :
    (∀ x y, kernel τ x y ↔ x = y) ↔ Function.Injective τ := by
  constructor
  · intro h x y hxy
    exact (h x y).mp hxy
  · intro h x y
    constructor
    · intro hxy
      exact h hxy
    · intro hxy
      exact congrArg τ hxy

/-- The output orbit of an actual same-point pair is exactly the
cross-output graph of the two equivariant maps, even when Q and R
have different types. -/
theorem same_point_output_graph
    (τ : A → Q) (σ : A → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y)
    (a : A) :
    orbital (G := G) (τ a) (σ a) =
      (fun q r => ∃ x : A, q = τ x ∧ r = σ x) := by
  funext q r
  apply propext
  constructor
  · rintro ⟨g, hq, hr⟩
    refine ⟨g • a, ?_, ?_⟩
    · exact ((equivτ g a).trans hq).symm
    · exact ((equivσ g a).trans hr).symm
  · rintro ⟨x, hq, hr⟩
    obtain ⟨g, hg⟩ := trans a x
    refine ⟨g, ?_, ?_⟩
    · calc
        g • τ a = τ (g • a) := (equivτ g a).symm
        _ = τ x := congrArg τ hg
        _ = q := hq.symm
    · calc
        g • σ a = σ (g • a) := (equivσ g a).symm
        _ = σ x := congrArg σ hg
        _ = r := hr.symm

/-- Full iff for the exceptional empty-diversity pullback on a single
root sort. The kernels are genuine identities exactly when both quotient
maps are injective, and the exceptional output orbital is the graph of
the same original root, not a formal identity of Q and R. -/
theorem empty_diversity_pullback_iff
    (τ : A → Q) (σ : A → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (trans : ∀ x y : A, ∃ g : G, g • x = y)
    (a b : A) :
    (∀ x y : A, x ≠ y →
      ¬ pullback τ σ (orbital (G := G) (τ a) (σ b)) x y) ↔
      (Function.Injective τ ∧ Function.Injective σ ∧
        orbital (G := G) (τ a) (σ b) =
          (fun q r => ∃ x : A, q = τ x ∧ r = σ x)) := by
  constructor
  · intro hEmpty
    have hDiag : ∀ x y : A,
        orbital (G := G) (τ a) (σ b) (τ x) (σ y) → x = y := by
      intro x y h
      by_contra hxy
      exact hEmpty x y hxy h
    have hab : a = b :=
      hDiag a b (orbital_nonempty (G := G) (τ a) (σ b))
    have hinj := no_diversity_injective τ σ equivτ equivσ trans a b hDiag
    refine ⟨hinj.1, hinj.2, ?_⟩
    subst b
    exact same_point_output_graph τ σ equivτ equivσ trans a
  · rintro ⟨hinjτ, hinjσ, hGraph⟩ x y hxy hOrbit
    rw [hGraph] at hOrbit
    obtain ⟨z, hxz, hyz⟩ := hOrbit
    apply hxy
    exact (hinjτ hxz).trans (hinjσ hyz).symm

end SameRoot

end CCO.GroupActions

namespace CCO

theorem cross_sort_real_points_distinct {ι : Type*} {X : ι → Type*}
    {i j : ι} (h : i ≠ j) (a : X i) (b : X j) :
    (⟨i, a⟩ : Sigma X) ≠ ⟨j, b⟩ := by
  intro heq
  exact h (congrArg Sigma.fst heq)

end CCO
