import CCO.RawExact.CanonicalQuotients
import CCO.RawExact.ZeroWordBoundary

/-!
# No zero-length restriction on an actual quotient diversity edge

An invariant actual quotient orbital whose pullback is contained in real
equality forces both quotient projections to be injective. Canonical
quotient sorts with those kernels are the same sort, so a diversity edge
cannot have that pullback. Thus every word in its exact presentation has
positive diversity length. No extra nonduplicate-sort provider is assumed.
-/

universe v w t

namespace CCO.RawExact

variable {A : Type v}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]

/-- A nonempty actual orbital pullback contained in equality has
identity kernels on both sides. Original transitivity supplies every
diagonal pair; equivariance then detects every kernel identification. -/
theorem orbital_pullback_subset_equality_injective
    (H : HomogeneousSource S G)
    {Q R : Type*} [MulAction G Q] [MulAction G R]
    (τ : A → Q) (σ : A → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) x, σ (g • x) = g • σ x)
    (q : Q) (r : R)
    (hSubset : ∀ x y : A,
      GroupActions.orbital (G := G) q r (τ x) (σ y) → x = y) :
    Function.Injective τ ∧ Function.Injective σ := by
  obtain ⟨a, ha⟩ := ontoτ q
  obtain ⟨b, hb⟩ := ontoσ r
  have hBase : GroupActions.orbital (G := G) q r (τ a) (σ b) := by
    rw [ha, hb]
    exact GroupActions.orbital_nonempty (G := G) q r
  have hab : a = b := hSubset a b hBase
  subst b
  have hDiagonal : ∀ x : A,
      GroupActions.orbital (G := G) q r (τ x) (σ x) := by
    intro x
    obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H () a x
    have hMove := GroupActions.orbital_invariant q r hBase g
    simpa only [← equivτ g a, ← equivσ g a, hg] using hMove
  constructor
  · intro x y hxy
    apply hSubset x y
    rw [hxy]
    exact hDiagonal y
  · intro x y hxy
    apply hSubset x y
    rw [← hxy]
    exact hDiagonal x

/-- C26's actual source positivity lemma. Canonical actual quotient
sorts, rather than duplicate presentation labels, make equality of
identity kernels imply equality of the named quotient sorts themselves. -/
theorem actual_quotient_edge_word_positive
    (H : HomogeneousSource S G)
    {family : Finset (Setoid A)}
    [∀ k : CanonicalQuotients.Index family, CanonicalQuotients.Invariant G k.val]
    (k l : CanonicalQuotients.Index family)
    (q : CanonicalQuotients.Carrier k) (r : CanonicalQuotients.Carrier l)
    (hDiverse : (⟨k, q⟩ : Sigma (@CanonicalQuotients.Carrier A family)) ≠ ⟨l, r⟩)
    (D : NonemptyExact S () ())
    (hD : evaluate S D.words =
      GroupActions.pullback (CanonicalQuotients.projection k)
        (CanonicalQuotients.projection l)
        (GroupActions.orbital (G := G) q r))
    (word : RawWord S () ()) (hWord : word ∈ D.words) :
    0 < diversityLength S word := by
  by_contra hPos
  have hZero : diversityLength S word = 0 := by omega
  have hSubset : ∀ x y : A,
      GroupActions.orbital (G := G) q r
        (CanonicalQuotients.projection k x) (CanonicalQuotients.projection l y) → x = y := by
    intro x y hxy
    have hEval : evaluate S D.words x y := by
      rw [hD]
      exact hxy
    have hTag := (zeroLength_relation_iff_tagged_eq S word hZero x y).mp (hEval word hWord)
    exact eq_of_heq (Sigma.mk.inj hTag).2
  have hInjective := orbital_pullback_subset_equality_injective S H
    (CanonicalQuotients.projection k) (CanonicalQuotients.projection l)
    (CanonicalQuotients.projection_surjective k) (CanonicalQuotients.projection_surjective l)
    (CanonicalQuotients.projection_equivariant k) (CanonicalQuotients.projection_equivariant l)
    q r hSubset
  have hSort := CanonicalQuotients.sort_eq_of_injective_projections k l
    hInjective.1 hInjective.2
  subst l
  obtain ⟨a, ha⟩ := CanonicalQuotients.projection_surjective k q
  obtain ⟨b, hb⟩ := CanonicalQuotients.projection_surjective k r
  have hab : a = b := hSubset a b (by
    rw [ha, hb]
    exact GroupActions.orbital_nonempty (G := G) q r)
  have hqr : q = r := ha.symm.trans ((congrArg (CanonicalQuotients.projection k) hab).trans hb)
  exact hDiverse (congrArg (fun z : CanonicalQuotients.Carrier k =>
    (⟨k, z⟩ : Sigma (@CanonicalQuotients.Carrier A family))) hqr)

end CCO.RawExact
