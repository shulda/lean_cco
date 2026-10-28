import CCO.RawExact.ActualMixedMaps

/-!
# Actual nested quotient orbital and finite partial-map reductions

A genuine commuting equivariant projection from a finer quotient to a
coarser quotient gives nested real kernels. The original symmetric
source algebra then discharges the mixed-orbit reduction provider in
C17. All actual finite-domain coverage and agreement conditions remain.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]

/-- C17 actual orbital reduction from a commuting projection of
actual equivariant quotient maps. No exactness or Helly is needed
for this same-sort symmetric algebraic statement. -/
theorem actual_nested_orbit_reduction_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    {Q K : Type*} [MulAction G Q] [MulAction G K]
    (τ : X i → Q) (κ : X i → K) (π : Q → K)
    (ontoτ : Function.Surjective τ) (ontoκ : Function.Surjective κ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (equivπ : ∀ (g : G) q, π (g • q) = g • π q)
    (comm : ∀ x, π (τ x) = κ x) :
    ∀ (q q' : Q) (k k' : K),
      GroupActions.orbital (G := G) q k q' k' ↔
        GroupActions.orbital (G := G) (π q) k (π q') k' := by
  apply mixed_orbit_reduction_of_saturation τ κ κ π id
    ontoτ ontoκ equivτ equivκ equivκ equivπ (fun _ _ => rfl) comm (fun _ => rfl)
  intro a b
  rw [← saturate_kernels τ κ (GroupActions.orbital (G := G) a b),
    ← saturate_kernels κ κ (GroupActions.orbital (G := G) a b)]
  rw [actual_pair_orbital_of_homogeneous S H a b]
  have hNested : ∀ x y, GroupActions.kernel τ x y → GroupActions.kernel κ x y := by
    intro x y hxy
    change κ x = κ y
    rw [← comm x, ← comm y]
    exact congrArg π hxy
  have invK : ∀ (g : G) x y,
      GroupActions.kernel κ x y → GroupActions.kernel κ (g • x) (g • y) := by
    intro g x y hxy
    change κ (g • x) = κ (g • y)
    rw [equivκ, equivκ, hxy]
  exact (actual_nested_mixed_of_homogeneous S H
    (GroupActions.kernel τ) (GroupActions.kernel κ)
    (kernel_equiv τ) (kernel_equiv κ) hNested invK (S.colour a b)).1

/-- The full C17 finite-domain clause with the actual orbital
reduction discharged. The coarser partial map covers EVERY projected
finer-domain point and agrees there, not merely on an overlap. -/
theorem actual_nested_partial_maps_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    {Q K : Type*} [MulAction G Q] [MulAction G K]
    (τ : X i → Q) (κ : X i → K) (π : Q → K)
    (ontoτ : Function.Surjective τ) (ontoκ : Function.Surjective κ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (equivπ : ∀ (g : G) q, π (g • q) = g • π q)
    (comm : ∀ x, π (τ x) = κ x)
    (p : FinitePartialMap Q) (gamma : FinitePartialMap K)
    (hCover : ∀ a ∈ p.domain, π a ∈ gamma.domain)
    (hAgree : ∀ a ∈ p.domain, π (p.send a) = gamma.send (π a))
    (hGamma : gamma.PreservesOrbit (G := G)) :
    ∀ a ∈ p.domain, ∀ k ∈ gamma.domain,
      GroupActions.orbital (G := G) a k =
        GroupActions.orbital (G := G) (p.send a) (gamma.send k) :=
  nested_mixed_orbits_preserved p gamma π
    (actual_nested_orbit_reduction_of_homogeneous S H τ κ π
      ontoτ ontoκ equivτ equivκ equivπ comm)
    hCover hAgree hGamma

end CCO.RawExact
