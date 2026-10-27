import CCO.RawExact.QuotientRequests

/-!
# B002 C14: actual invariant saturated relations descend to quotient orbits

An invariant equality-inclusive RAW relation that is saturated with respect
to two actual quotient kernels is a union of actual output pair orbits.
No fictitious quotient-colour tables, abstract equivalence representatives,
SAP or exact-Helly provider are required for this statement.
-/

namespace CCO.RawExact

section QuotientDescent

variable {G A B Q R : Type*} [Group G]
variable [MulAction G A] [MulAction G B]
variable [MulAction G Q] [MulAction G R]

theorem kernel_saturation_transfer
    (τ : A → Q) (σ : B → R)
    (D : A → B → Prop)
    (hSat : saturate (GroupActions.kernel τ) D
      (GroupActions.kernel σ) = D)
    (x : A) (y : B) (u : A) (v : B)
    (hxy : D x y)
    (hx : τ x = τ u) (hy : σ y = σ v) :
    D u v := by
  rw [← hSat]
  exact ⟨y, ⟨x, hx.symm, hxy⟩, hy⟩

/-- C14 actual-orbital descent: the original RAW relation is precisely
the union of all quotient pair orbits that it meets. Output orbitals are
defined by the actual diagonal group action, not by a new colour axiom. -/
theorem invariant_saturated_descends_to_orbits
    (τ : A → Q) (σ : B → R)
    (equivτ : ∀ g x, τ (g • x) = g • τ x)
    (equivσ : ∀ g y, σ (g • y) = g • σ y)
    (D : A → B → Prop)
    (hInv : ∀ g x y, D x y → D (g • x) (g • y))
    (hSat : saturate (GroupActions.kernel τ) D
      (GroupActions.kernel σ) = D) :
    D = (fun u v => ∃ x y, D x y ∧
      GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ x) (σ y)) u v) := by
  funext u v
  apply propext
  constructor
  · intro huv
    exact ⟨u, v, huv, GroupActions.orbital_nonempty (G := G) (τ u) (σ v)⟩
  · rintro ⟨x, y, hxy, ⟨g, hτ, hσ⟩⟩
    apply kernel_saturation_transfer τ σ D hSat
      (g • x) (g • y) u v (hInv g x y hxy)
    · exact (equivτ g x).trans hτ
    · exact (equivσ g y).trans hσ

/-- An actual orbit pullback itself has the two kernel closure laws.
This is a downstream consumer of B001's exact orbit-pullback theorem and
our C14 saturation calculus. -/
theorem output_orbit_kernel_saturated
    (τ : A → Q) (σ : B → R)
    (equivτ : ∀ g x, τ (g • x) = g • τ x)
    (equivσ : ∀ g y, σ (g • y) = g • σ y)
    (a : A) (b : B) :
    saturate (GroupActions.kernel τ)
      (GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)))
      (GroupActions.kernel σ) =
      GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)) := by
  have hJ : RawSymmetric.EquivRel (GroupActions.kernel τ) :=
    kernel_equiv τ
  have hK : RawSymmetric.EquivRel (GroupActions.kernel σ) :=
    kernel_equiv σ
  have hOrbit := (equivariant_orbit_pullback τ σ equivτ equivσ a b)
  rw [hOrbit]
  change saturate (GroupActions.kernel τ)
      (saturate (GroupActions.kernel τ)
        (GroupActions.orbital (G := G) a b)
        (GroupActions.kernel σ))
      (GroupActions.kernel σ) =
    saturate (GroupActions.kernel τ)
      (GroupActions.orbital (G := G) a b)
      (GroupActions.kernel σ)
  have hLeft := (saturate_idempotent
    (GroupActions.kernel τ)
    (GroupActions.orbital (G := G) a b)
    (GroupActions.kernel σ) hJ hK).1
  have hRight := (saturate_idempotent
    (GroupActions.kernel τ)
    (GroupActions.orbital (G := G) a b)
    (GroupActions.kernel σ) hJ hK).2
  unfold saturate
  rw [TRel.comp_assoc]
  rw [hLeft]
  exact hRight

end QuotientDescent
end CCO.RawExact
