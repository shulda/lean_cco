import CCO.RawExact.CanonicalQuotients
import CCO.RawExact.QuotientSourcePalette
import CCO.RawExact.QuotientHomogeneousSource
import CCO.RawExact.QuotientTriangleFullness

/-!
# Actual canonical exact quotient source properties

Canonical labels are actual setoids of one original sort, as prescribed
by pinned C26–C28. Their actual actions, kernels and original-source
properties are constructed from the original assumptions and actual
full-exact relation data. No duplicate identity copies are introduced.
-/

universe v w t z

namespace CCO.RawExact.CanonicalQuotients

variable {A : Type v}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]

/-- The actual quotient action is constructed from proved exact-kernel
invariance. It does not require a separate invariant-kernel provider. -/
@[instance_reducible] def action (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family)
    (k : Index family) : MulAction G (Carrier k) := by
  letI : Invariant G k.val := ExactData.invariant S H E k
  infer_instance

theorem equivariant_projection (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ (k : Index family) (g : G) (x : A),
      projection k (g • x) = g • projection k x := by
  intro k g x
  rfl

theorem exact_kernel {family : Finset (Setoid A)} (E : ExactData S family)
    (k : Index family) :
    GroupActions.kernel (projection k) = evaluate S (E.exact k).words :=
  (projection_kernel k).trans (E.represents k).symm

include S in
theorem nonempty_carrier {family : Finset (Setoid A)} (k : Index family) :
    Nonempty (Carrier k) := by
  obtain ⟨a⟩ := S.nonemptySort ()
  exact ⟨projection k a⟩

theorem countable_carrier [Countable A]
    {family : Finset (Setoid A)} (k : Index family) : Countable (Carrier k) :=
  (projection_surjective k).countable

/-- The entire finite named quotient universe is countable, not only
each individual actual quotient carrier. -/
theorem countable_tagged [Countable A]
    (family : Finset (Setoid A)) :
    Countable (Sigma (fun k : Index family => Carrier k)) := by
  classical
  let : Encodable (Index family) := Encodable.ofCountable _
  let : ∀ k : Index family, Encodable (Carrier k) :=
    fun k => Encodable.ofCountable (Carrier k)
  infer_instance

theorem transitive_carrier (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ (k : Index family) (x y : Carrier k), ∃ g : G, g • x = y := by
  intro k x y
  obtain ⟨a, rfl⟩ := projection_surjective k x
  obtain ⟨b, rfl⟩ := projection_surjective k y
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H () a b
  exact ⟨g, congrArg (projection k) hg⟩

/-- The canonical actual quotient age has C24 triangle fullness under
the original source CCO. This finite statement uses its actual pair
orbitals directly and needs neither countability nor quotient CCO. -/
theorem triangle_fullness (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ {V : Type v} [Finite V] (D : ActualOrbitalDiagram G (fun k : Index family => Carrier k) V),
      D.TrianglesLegal →
      ∃ point : ∀ p, Carrier (D.sort p),
        (∀ p q, D.relation p q (point p) (point q)) ∧
        Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma (fun k : Index family => Carrier k))) := by
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  intro V _ D hTriangles
  exact actual_quotient_triangle_fullness_of_CCO S H cco (fun k : Index family => Carrier k)
    (fun _ => ()) projection projection_surjective
    (equivariant_projection S H E) E.exact (exact_kernel S E) D hTriangles


/-- The full C24 source quantifiers: finite formal vertex types live in
an arbitrary universe independent of the original carrier. The proved
underlying finite induction is already universe-general, so no new
provider or stronger original CCO premise is required. The original
`triangle_fullness` specialization is retained above. -/
theorem triangle_fullness_general (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ {V : Type z} [Finite V] (D : ActualOrbitalDiagram G (fun k : Index family => Carrier k) V),
      D.TrianglesLegal →
      ∃ point : ∀ p, Carrier (D.sort p),
        (∀ p q, D.relation p q (point p) (point q)) ∧
        Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma (fun k : Index family => Carrier k))) := by
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  intro V _ D hTriangles
  exact actual_quotient_triangle_fullness_of_CCO S H cco (fun k : Index family => Carrier k)
    (fun _ => ()) projection projection_surjective
    (equivariant_projection S H E) E.exact (exact_kernel S E) D hTriangles


/-- The actual canonical finite orbital source, with no abstract
quotient-colour table or extra invariant-kernel provider. -/
noncomputable def source (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    AtomicSource (Index family) (fun k => Carrier k) := by
  letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  exact QuotientPalette.actualQuotientAtomicSource (i := ()) (fun k : Index family => Carrier k)
    S H projection projection_surjective (equivariant_projection S H E)

theorem source_colour_eq_iff_orbital (H : HomogeneousSource S G)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    ∀ {k l : Index family} (x : Carrier k) (y : Carrier l)
      (x' : Carrier k) (y' : Carrier l),
      (source S H E).colour x y = (source S H E).colour x' y' ↔
        GroupActions.orbital (G := G) x y x' y' := by
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  intro k l x y x' y'
  exact QuotientPalette.actualQuotientAtomicSource_colour_eq_iff_orbital (i := ())
    (fun k : Index family => Carrier k) S H projection projection_surjective
    (equivariant_projection S H E) x y x' y'

/-- Actual source homogeneity is supplied by proved original C21
lifting, including arbitrary finite tuples with repeated values. -/
theorem homogeneous [Countable A] (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    letI : ∀ k : Index family, MulAction G (Carrier k) := action S H E
    HomogeneousSource (source S H E) G := by
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  exact actual_quotient_homogeneous_of_CCO S H cco
    (fun k : Index family => Carrier k) (fun _ => ()) projection
    projection_surjective (equivariant_projection S H E)
    E.exact (exact_kernel S E) (source S H E) (source_colour_eq_iff_orbital S H E)

/-- C25 actual canonical quotient-age AP, with the actual palette and
its homogeneity instantiated. No representation or AP provider remains. -/
theorem ageAP [Countable A] (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S)
    {family : Finset (Setoid A)} (E : ExactData S family) :
    AgeAP (source S H E) := by
  let : ∀ k : Index family, MulAction G (Carrier k) := action S H E
  exact ageAP_of_homogeneous (source S H E) (homogeneous S H cco E)

end CCO.RawExact.CanonicalQuotients
