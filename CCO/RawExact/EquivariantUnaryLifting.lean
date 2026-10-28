import CCO.RawExact.ActualJointLifting

/-!
# C22: the same original lift preserves every actual equivariant unary map

One actual pair-orbital witness for (x, τ x) forces commutation with τ.
Consequently the original automorphism obtained in C21 preserves the
expanded unary language globally, with the same finite displayed domain.
-/

universe u v w z t r

namespace CCO.RawExact

/-- Preservation of actual pair orbitals forces preservation of every
actual equivariant unary map, without a new representative or section. -/
theorem pair_orbit_maps_commute_with_equivariant_unary
    {G A B : Type*} [Group G] [MulAction G A] [MulAction G B]
    (eA : A → A) (eB : B → B)
    (hPair : ∀ a b, GroupActions.orbital (G := G) a b (eA a) (eB b))
    (τ : A → B) (equivτ : ∀ (g : G) a, τ (g • a) = g • τ a) :
    ∀ a, eB (τ a) = τ (eA a) := by
  intro a
  obtain ⟨g, hga, hgb⟩ := hPair a (τ a)
  calc
    eB (τ a) = g • τ a := hgb.symm
    _ = τ (g • a) := (equivτ g a).symm
    _ = τ (eA a) := congrArg τ hga

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- C22 equivariant unary enrichment uses exactly the same original
ambient automorphism as the binary finite joint lift. Every named unary
map is preserved on the whole joint structure. A partial isomorphism of
finite functionally closed induced substructures supplies such a binary
finite map by forgetting symbols, on exactly its original vertices. -/
theorem actual_joint_unary_lifting_of_exact_ball_helly
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {J : Type z} [Finite J]
    (Q : J → Type v) [∀ j, MulAction G (Q j)]
    (root : J → ι) (π : ∀ j, X (root j) → Q j)
    (ontoπ : ∀ j, Function.Surjective (π j))
    (equivπ : ∀ j (g : G) c, π j (g • c) = g • π j c)
    (E : ∀ j, NonemptyExact S (root j) (root j))
    (hE : ∀ j, GroupActions.kernel (π j) = evaluate S (E j).words)
    (f : FiniteJointPartialIso G (JointFamily X Q))
    {T : Type r} (domainSort codomainSort : T → ι ⊕ J)
    (τ : ∀ t : T, JointFamily X Q (domainSort t) → JointFamily X Q (codomainSort t))
    (equivτ : ∀ t (h : G) a, τ t (h • a) = h • τ t a) :
    ∃ (g : OriginalAutomorphism S) (q : ∀ j, Q j ≃ Q j),
      (∀ j (x : X (root j)), q j (π j x) = π j (g.equiv (root j) x)) ∧
      (∀ p ∈ f.domain, jointEquiv g.equiv q p.1 p.2 = f.send p) ∧
      (∀ t a, jointEquiv g.equiv q (codomainSort t) (τ t a) =
        τ t (jointEquiv g.equiv q (domainSort t) a)) := by
  obtain ⟨g, q, hπ, hPair, hExt⟩ :=
    actual_joint_lifting_of_exact_ball_helly S H hHelly Q root π ontoπ equivπ E hE f
  refine ⟨g, q, hπ, hExt, ?_⟩
  intro t
  exact pair_orbit_maps_commute_with_equivariant_unary
    (jointEquiv g.equiv q (domainSort t)) (jointEquiv g.equiv q (codomainSort t))
    (hPair (domainSort t) (codomainSort t)) (τ t) (equivτ t)

end CCO.RawExact
