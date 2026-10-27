import CCO.RawExact.PartialMaps
import CCO.RawExact.QuotientRequests

/-!
# B002 C16: mixed-pair orbit reduction on actual equivariant quotients

This module turns equality of two *real* RAW saturation relations into
equivalence of quotient pair orbits, with all quotient-map surjectivity,
equivariance and projection compatibility visible. Source-level
same-sort join algebra from B001/B002 supplies the saturation equality.
Neither partial-map compatibility nor quotient lifting uses a section.
-/

universe u v w

namespace CCO.RawExact

section OrbitReduction

variable {G A Q R K : Type*} [Group G]
variable [MulAction G A] [MulAction G Q]
variable [MulAction G R] [MulAction G K]

/-- The converse of orbital projection holds if and only if the relevant
original-fibre saturations agree; the forward implication requires only
that both quotient projections commute with the original action. -/
theorem mixed_orbit_reduction_of_saturation
    (τ : A → Q) (σ : A → R) (κ : A → K)
    (πQ : Q → K) (πR : R → K)
    (ontoτ : Function.Surjective τ)
    (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (equivπQ : ∀ (g : G) x, πQ (g • x) = g • πQ x)
    (equivπR : ∀ (g : G) x, πR (g • x) = g • πR x)
    (commQ : ∀ x : A, πQ (τ x) = κ x)
    (commR : ∀ x : A, πR (σ x) = κ x)
    (hSat : ∀ a b : A,
      GroupActions.saturation τ σ
        (GroupActions.orbital (G := G) a b) =
      GroupActions.saturation κ κ
        (GroupActions.orbital (G := G) a b)) :
    MixedOrbitReduction (G := G) πQ πR := by
  intro q q' r r'
  constructor
  · rintro ⟨g, hgq, hgr⟩
    refine ⟨g, ?_, ?_⟩
    · calc
        g • πQ q = πQ (g • q) := (equivπQ g q).symm
        _ = πQ q' := congrArg πQ hgq
    · calc
        g • πR r = πR (g • r) := (equivπR g r).symm
        _ = πR r' := congrArg πR hgr
  · intro hproj
    obtain ⟨a, rfl⟩ := ontoτ q
    obtain ⟨b, rfl⟩ := ontoσ r
    obtain ⟨a', rfl⟩ := ontoτ q'
    obtain ⟨b', rfl⟩ := ontoσ r'
    have hκ : GroupActions.pullback κ κ
        (GroupActions.orbital (G := G) (κ a) (κ b)) a' b' := by
      change GroupActions.orbital (G := G)
        (κ a) (κ b) (κ a') (κ b')
      simpa only [commQ, commR] using hproj
    have hκsat : GroupActions.saturation κ κ
        (GroupActions.orbital (G := G) a b) a' b' := by
      rw [← GroupActions.orbital_pullback κ κ equivκ equivκ a b]
      exact hκ
    have hτσsat : GroupActions.saturation τ σ
        (GroupActions.orbital (G := G) a b) a' b' := by
      rw [hSat a b]
      exact hκsat
    have hτσ : GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)) a' b' := by
      rw [GroupActions.orbital_pullback τ σ equivτ equivσ a b]
      exact hτσsat
    exact hτσ

end OrbitReduction

section ActualJoin

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The actual one-sort symmetric source supplies the C16 mixed
quotient-orbit reduction from exact kernel maps and their common join.
Exactness is NOT needed for the join algebra itself; no unproved
abstract colour-table representation is used. -/
theorem actual_mixed_orbit_reduction_of_join
    (HS : HomogeneousSource S G) {i : ι}
    (E H : X i → X i → Prop)
    (hE : RawSymmetric.EquivRel E)
    (hH : RawSymmetric.EquivRel H)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invH : ∀ (g : G) x y, H x y → H (g • x) (g • y))
    {Q R K : Type*}
    [MulAction G Q] [MulAction G R] [MulAction G K]
    (τ : X i → Q) (σ : X i → R) (κ : X i → K)
    (πQ : Q → K) (πR : R → K)
    (ontoτ : Function.Surjective τ)
    (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (equivπQ : ∀ (g : G) x, πQ (g • x) = g • πQ x)
    (equivπR : ∀ (g : G) x, πR (g • x) = g • πR x)
    (commQ : ∀ x : X i, πQ (τ x) = κ x)
    (commR : ∀ x : X i, πR (σ x) = κ x)
    (kerτ : GroupActions.kernel τ = E)
    (kerσ : GroupActions.kernel σ = H)
    (kerκ : GroupActions.kernel κ = RawSymmetric.compose E H) :
    MixedOrbitReduction (G := G) πQ πR := by
  apply mixed_orbit_reduction_of_saturation τ σ κ πQ πR
    ontoτ ontoσ equivτ equivσ equivκ equivπQ equivπR commQ commR
  intro a b
  rw [← saturate_kernels τ σ (GroupActions.orbital (G := G) a b),
      ← saturate_kernels κ κ (GroupActions.orbital (G := G) a b)]
  rw [kerτ, kerσ, kerκ]
  rw [actual_pair_orbital_of_homogeneous S HS a b]
  have hJoin := (actual_mixed_join_of_homogeneous S HS E H
    hE hH invE invH (S.colour a b)).1
  exact hJoin

/-- Complete C16 finite-domain clause, consuming the real group-action
orbital reduction instead of silently postulating quotient homogeneity.
The common J-map must cover and agree with BOTH full projected domains. -/
theorem actual_mixed_partial_maps_of_join
    (HS : HomogeneousSource S G) {i : ι}
    (E H : X i → X i → Prop)
    (hE : RawSymmetric.EquivRel E)
    (hH : RawSymmetric.EquivRel H)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invH : ∀ (g : G) x y, H x y → H (g • x) (g • y))
    {Q R K : Type*}
    [MulAction G Q] [MulAction G R] [MulAction G K]
    (τ : X i → Q) (σ : X i → R) (κ : X i → K)
    (πQ : Q → K) (πR : R → K)
    (ontoτ : Function.Surjective τ)
    (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (equivπQ : ∀ (g : G) x, πQ (g • x) = g • πQ x)
    (equivπR : ∀ (g : G) x, πR (g • x) = g • πR x)
    (commQ : ∀ x : X i, πQ (τ x) = κ x)
    (commR : ∀ x : X i, πR (σ x) = κ x)
    (kerτ : GroupActions.kernel τ = E)
    (kerσ : GroupActions.kernel σ = H)
    (kerκ : GroupActions.kernel κ = RawSymmetric.compose E H)
    (p : FinitePartialMap Q) (q : FinitePartialMap R)
    (γ : FinitePartialMap K)
    (hCompat : CompatibleViaCommon p q γ πQ πR)
    (hGamma : γ.PreservesOrbit (G := G))
    (hQ : p.PreservesOrbit (G := G))
    (hR : q.PreservesOrbit (G := G)) :
    p.PreservesOrbit (G := G) ∧ q.PreservesOrbit (G := G) ∧
      (∀ a ∈ p.domain, ∀ b ∈ q.domain,
        GroupActions.orbital (G := G) a b =
          GroupActions.orbital (G := G) (p.send a) (q.send b)) := by
  have hReduction := actual_mixed_orbit_reduction_of_join S HS E H
    hE hH invE invH τ σ κ πQ πR
    ontoτ ontoσ equivτ equivσ equivκ equivπQ equivπR
    commQ commR kerτ kerσ kerκ
  exact joint_orbit_compatibility p q γ πQ πR
    hReduction hCompat hGamma hQ hR

end ActualJoin

end CCO.RawExact
