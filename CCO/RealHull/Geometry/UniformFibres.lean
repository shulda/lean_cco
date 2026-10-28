import CCO.RealHull.Geometry.Globalisation

/-! The spoke SET, not an anchor configuration, controls the canonical fixer.
One finite realised instance forces every instance with the same spoke set
to be a conjugate whole class with the same two-power size. No map of anchors
is asserted. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable (A B : Finset M) (q : ↥A → Atom S) (r : ↥B → Atom S)
variable {G : Type t} [Group G] [MulAction G M]

theorem square_intersection_same_spokes (hP : Set.range q = Set.range r) :
    {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} =
      {c : Atom S | ∀ b : ↥B, c ∈ square S (r b)} := by
  ext c
  constructor
  · intro hc b
    have hh : r b ∈ Set.range q := hP.symm ▸ (show r b ∈ Set.range r from ⟨b,rfl⟩)
    obtain ⟨a,ha⟩ := hh
    exact ha ▸ hc a
  · intro hc a
    have hh : q a ∈ Set.range r := hP ▸ (show q a ∈ Set.range q from ⟨a,rfl⟩)
    obtain ⟨b,hb⟩ := hh
    exact hb ▸ hc b

theorem spokeFixer_same_spokes (H : HomogeneousSource S G) (hP : Set.range q = Set.range r) :
    fibreSpokeFixer S A q H = fibreSpokeFixer S B r H := by
  unfold fibreSpokeFixer
  rw [hP]

variable [Nonempty (FibreSet S A q)] [Nonempty (FibreSet S B r)]

theorem same_spokes_palette_eq (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    [Finite (FibreSet S A q)] (hP : Set.range q = Set.range r) :
    {c : Atom S | ∀ b : ↥B, c ∈ square S (r b)} = (fibreSpokeFixer S B r H).val := by
  exact (square_intersection_same_spokes S A B q r hP).symm.trans
    ((finite_fibre_palette_eq S A q H cco).trans
      (congrArg (fun R : Support S => R.val) (spokeFixer_same_spokes S A B q r H hP)))

theorem same_spokes_uniform_conjugacy (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)]
    (hP : Set.range q = Set.range r) :
    ∃ g : G, (∀ y : M, y ∈ FibreSet S A q ↔ g • y ∈ FibreSet S B r) ∧
      Finite (FibreSet S B r) ∧
      ∃ n : Nat, Nat.card (FibreSet S A q) = 2^n ∧
        Nat.card (FibreSet S B r) = 2^n ∧ n ≤ Nat.card (Atom S) := by
  obtain ⟨x⟩ := ‹Nonempty (FibreSet S A q)›
  obtain ⟨z⟩ := ‹Nonempty (FibreSet S B r)›
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () x.val z.val
  have hT := same_spokes_palette_eq S A B q r H cco hP
  have hR := spokeFixer_same_spokes S A B q r H hP
  have hmove (y : M) : y ∈ FibreSet S A q ↔ g • y ∈ FibreSet S B r := by
    rw [finite_fibre_global_class S A q H cco x y,
      fibre_class_of_palette_containment S B r H hT.le z (g • y)]
    change col S x.val y ∈ plus S (fibreSpokeFixer S A q H).val ↔
      col S z.val (g • y) ∈ plus S (fibreSpokeFixer S B r H).val
    rw [← hR]
    have hi := col_invariant S H g x.val y
    rw [hg] at hi
    rw [hi]
  let e : FibreSet S A q ≃ FibreSet S B r := {
    toFun := fun y => ⟨g • y.val,(hmove y.val).mp y.property⟩
    invFun := fun y => ⟨g⁻¹ • y.val,(hmove (g⁻¹ • y.val)).mpr (by
      simpa only [smul_inv_smul] using y.property)⟩
    left_inv := fun y => Subtype.ext (inv_smul_smul g y.val)
    right_inv := fun y => Subtype.ext (smul_inv_smul g y.val)
  }
  have hfin : Finite (FibreSet S B r) := Finite.of_injective e.symm e.symm.injective
  obtain ⟨n,hn,hbound⟩ := finite_fibre_size_power_two S A q H cco
  exact ⟨g,hmove,hfin,n,hn,(Nat.card_congr e).symm.trans hn,hbound⟩

end CCO.RealHull.Geometry
