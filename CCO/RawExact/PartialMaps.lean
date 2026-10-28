import CCO.RawExact.MixedJoins
import CCO.GroupQuotient

/-!
# B002 C16–C17: precise finite mixed-orbital partial-map compatibility

The pair-orbit reduction to a common quotient is a separate mathematical
hypothesis. For actual one-sort invariant equivalences it is supplied
by the mixed-join algebra together with the actual quotient pullback,
not by merely agreeing on an overlap of partial domains.
-/

universe u v w t

namespace CCO.RawExact

/-- A finite partial injection of *actual* quotient points. The total
function is only used on the displayed finite domain. -/
structure FinitePartialMap (A : Type u) where
  domain : Finset A
  send : A → A
  injOn : Set.InjOn send (↑domain : Set A)

namespace FinitePartialMap

variable {G : Type t} [Group G]
variable {A : Type u} [MulAction G A]

/-- The actual complete within-sort binary orbital is preserved for
all ordered pairs in the displayed domain, including the diagonal. -/
def PreservesOrbit (f : FinitePartialMap A) : Prop :=
  ∀ x y, x ∈ f.domain → y ∈ f.domain →
    GroupActions.orbital (G := G) x y =
      GroupActions.orbital (G := G) (f.send x) (f.send y)

end FinitePartialMap

section Mixed

variable {G : Type t} [Group G]
variable {A : Type u} {B : Type v} {K : Type w}
variable [MulAction G A] [MulAction G B] [MulAction G K]

/-- C16's *exact* finite-domain condition. The common partial quotient
map covers BOTH entire projected domains, with pointwise compatibility;
agreement only where the original two domains meet is insufficient. -/
def CompatibleViaCommon
    (p : FinitePartialMap A) (q : FinitePartialMap B)
    (gamma : FinitePartialMap K)
    (πA : A → K) (πB : B → K) : Prop :=
  (∀ a ∈ p.domain, πA a ∈ gamma.domain ∧
      πA (p.send a) = gamma.send (πA a)) ∧
  (∀ b ∈ q.domain, πB b ∈ gamma.domain ∧
      πB (q.send b) = gamma.send (πB b))

/-- A statement of the genuine full mixed-orbit collapse: the original
mixed pair orbit is **equivalent** to the orbit of both J-projections.
For exact quotient sorts this follows from J=E∨H and E;a;H=J;a;J;
here it is a visible provider, not an unproved global instance. -/
def MixedOrbitReduction (πA : A → K) (πB : B → K) : Prop :=
  ∀ (a a' : A) (b b' : B),
    GroupActions.orbital (G := G) a b a' b' ↔
      GroupActions.orbital (G := G)
        (πA a) (πB b) (πA a') (πB b')

/-- C16 partial-map mechanism: one *shared* partial J-isomorphism,
covering both projected domains, forces preservation of every mixed
pair orbital. No choice of a group automorphism is required. -/
theorem mixed_orbits_preserved_of_common
    (p : FinitePartialMap A) (q : FinitePartialMap B)
    (gamma : FinitePartialMap K)
    (πA : A → K) (πB : B → K)
    (hReduce : MixedOrbitReduction (G := G) πA πB)
    (hCompat : CompatibleViaCommon p q gamma πA πB)
    (hGamma : gamma.PreservesOrbit (G := G)) :
    ∀ a ∈ p.domain, ∀ b ∈ q.domain,
      GroupActions.orbital (G := G) a b =
        GroupActions.orbital (G := G) (p.send a) (q.send b) := by
  intro a ha b hb
  obtain ⟨haK, hAgreeA⟩ := hCompat.1 a ha
  obtain ⟨hbK, hAgreeB⟩ := hCompat.2 b hb
  have hOrbK : GroupActions.orbital (G := G)
      (πA a) (πB b) (πA (p.send a)) (πB (q.send b)) := by
    rw [hAgreeA, hAgreeB]
    rw [hGamma (πA a) (πB b) haK hbK]
    exact GroupActions.orbital_nonempty (G := G)
      (gamma.send (πA a)) (gamma.send (πB b))
  have hMixed : GroupActions.orbital (G := G)
      a b (p.send a) (q.send b) :=
    (hReduce a (p.send a) b (q.send b)).mpr hOrbK
  exact GroupActions.orbital_eq_of_mem a b (p.send a) (q.send b) hMixed

/-- With each input already a within-sort partial orbital isomorphism,
the union of the two tagged maps preserves the complete joint orbital
language: the missing mixed case is exactly the preceding theorem. -/
theorem joint_orbit_compatibility
    (p : FinitePartialMap A) (q : FinitePartialMap B)
    (gamma : FinitePartialMap K)
    (πA : A → K) (πB : B → K)
    (hReduce : MixedOrbitReduction (G := G) πA πB)
    (hCompat : CompatibleViaCommon p q gamma πA πB)
    (hGamma : gamma.PreservesOrbit (G := G))
    (hA : p.PreservesOrbit (G := G))
    (hB : q.PreservesOrbit (G := G)) :
    p.PreservesOrbit (G := G) ∧
      q.PreservesOrbit (G := G) ∧
      (∀ a ∈ p.domain, ∀ b ∈ q.domain,
        GroupActions.orbital (G := G) a b =
          GroupActions.orbital (G := G) (p.send a) (q.send b)) :=
  ⟨hA, hB, mixed_orbits_preserved_of_common p q gamma πA πB
    hReduce hCompat hGamma⟩

/-- C17 specializes to a finer sort A and its coarser sort K:
every projected finer-domain element MUST be in the coarser domain,
and the two maps agree there. The coarser map is used on both sides. -/
theorem nested_mixed_orbits_preserved
    (p : FinitePartialMap A) (gamma : FinitePartialMap K)
    (π : A → K)
    (hReduce : ∀ (a a' : A) (k k' : K),
      GroupActions.orbital (G := G) a k a' k' ↔
        GroupActions.orbital (G := G) (π a) k (π a') k')
    (hCover : ∀ a ∈ p.domain, π a ∈ gamma.domain)
    (hAgree : ∀ a ∈ p.domain, π (p.send a) = gamma.send (π a))
    (hGamma : gamma.PreservesOrbit (G := G)) :
    ∀ a ∈ p.domain, ∀ k ∈ gamma.domain,
      GroupActions.orbital (G := G) a k =
        GroupActions.orbital (G := G) (p.send a) (gamma.send k) := by
  apply mixed_orbits_preserved_of_common p gamma gamma π id
  · intro a a' k k'
    exact hReduce a a' k k'
  · constructor
    · intro a ha
      exact ⟨hCover a ha, hAgree a ha⟩
    · intro k hk
      exact ⟨hk, rfl⟩
  · exact hGamma

end Mixed

end CCO.RawExact
