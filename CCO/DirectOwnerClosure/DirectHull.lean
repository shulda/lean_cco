import CCO.DirectOwnerClosure.Basic

/-! C01--C07: the older direct canonical-hull argument.  Only the accepted
algebraic-implies-finite-hull implication is used.  Neither the greatest
finite packet nor the spoke connectivities are assumed exact. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

theorem packet_class_finite (x : M) : {y : M | packet S H x y}.Finite := by
  exact Set.finite_coe_iff.mp
    ((finiteIndex_bottom_iff_finite_classes S (packet S H)).mp (finiteIndex_sigma S H ⊥) x)

theorem packetHull_finite [DecidableEq M] (A : Finset M) : (packetHull S H A).Finite := by
  have he : packetHull S H A = ⋃ a ∈ (A : Set M), {y | packet S H a y} := by
    ext y
    simp only [packetHull,Set.mem_setOf_eq,Set.mem_iUnion,Finset.mem_coe]
    constructor <;> rintro ⟨a,ha,hy⟩ <;> exact ⟨a,ha,hy⟩
  rw [he]
  exact A.finite_toSet.biUnion (fun a _ => packet_class_finite S H a)

/-- C01: the finite packet target is preserved by every full original
automorphism fixing the real parameters. -/
theorem packetHull_subset_real_acl [DecidableEq M] (A : Finset M) :
    packetHull S H A ⊆ algebraicClosure (FullAut S) A := by
  rintro x ⟨a,ha,hax⟩
  apply (packet_class_finite S H a).subset
  rintro y ⟨g,hg,rfl⟩
  have he := (fullAut_equivalence S (packet S H) g a x).mpr hax
  change packet S H a (g.val x)
  simpa only [show g.val a = a from hg a ha] using he

include H in
/-- C02 uses actual infinitude and transitivity, including the empty base. -/
theorem real_acl_empty [Infinite M] :
    algebraicClosure (FullAut S) (∅ : Finset M) = ∅ := by
  ext x
  change (orbitOver (FullAut S) ∅ x).Finite ↔ False
  have he : orbitOver (FullAut S) ∅ x = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () x y
      exact ⟨motionAut S H g,fun a ha => False.elim (Finset.notMem_empty a ha),hg⟩
  rw [he]
  exact ⟨fun hf => Set.infinite_univ hf,False.elim⟩

def connectivity (p : Atom S) : ColourEq S () := supportEquiv S (gamma S p)

theorem atom_mem_connectivity (p : Atom S) {x y : M} (h : col S x y = some p) :
    connectivity S p x y := by
  change col S x y ∈ plus S (gamma S p).val
  rw [h,some_mem_plus]
  exact subset_generated S {p} (Set.mem_singleton _)

/-- C05 is finite FULL-lattice minimality, not exact-lattice atomicity. -/
theorem UniqueDirection.le_of_infinite {E J : ColourEq S ()}
    (hE : UniqueDirection S E) (hJ : ¬ FiniteIndex S ⊥ J) : E ≤ J := by
  obtain ⟨D,hD,hmin⟩ := wellFounded_lt.has_min
    {D : ColourEq S () | D ≤ J ∧ ¬ FiniteIndex S ⊥ D} ⟨J,le_rfl,hJ⟩
  have hcut : MinimalInfiniteCut S D := by
    refine ⟨hD.2,?_⟩
    intro K hKD
    by_contra hK
    exact hmin K ⟨hKD.le.trans hD.1,hK⟩ hKD
  exact hE.2 D hcut ▸ hD.1

theorem outside_packet_not_parameter [DecidableEq M] (A : Finset M) (x : M)
    (hx : x ∉ packetHull S H A) : x ∉ A := by
  intro ha
  exact hx ⟨x,ha,(packet S H).val.refl x⟩

/-- C03--C05: each genuine actual spoke is infinite and contains the SAME E. -/
theorem outside_spoke_contains_direction [DecidableEq M] {E : ColourEq S ()}
    (hE : UniqueDirection S E) (A : Finset M) (x : M)
    (hx : x ∉ packetHull S H A) (a : ↥A) :
    E ≤ connectivity S (actualSpokes S A x (outside_packet_not_parameter S H A x hx) a) := by
  apply UniqueDirection.le_of_infinite S hE
  intro hf
  have hle := sigma_greatest S H bot_le hf
  apply hx
  refine ⟨a.val,a.property,(packet S H).val.symm (hle ?_)⟩
  exact atom_mem_connectivity S _ (actualSpokes_colour S A x _ a)

include H in
/-- An infinite actual E-class inside the canonical hull contradicts ONLY
the forward canonical algebraic-hull theorem. This also allows empty A. -/
theorem outside_acl_of_direction_spokes [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()}
    (hE : MinimalInfiniteCut S E) (A : Finset M) (x : M) (hxA : x ∉ A)
    (hspoke : ∀ a : ↥A, E ≤ connectivity S (actualSpokes S A x hxA a)) :
    x ∉ algebraicClosure (FullAut S) A := by
  intro halg
  have hf := (actual_algebraic_hull S (full_homogeneous S H) cco A x hxA halg).1
  have hclass : {y : M | E x y}.Infinite := by
    have hi := cut_actual_classes_infinite S H hE x
    exact Set.infinite_coe_iff.mp hi
  apply hclass
  apply (Set.finite_coe_iff.mp hf).subset
  intro y hxy
  rw [actualHull,dite_eq_right hxA]
  intro a
  exact (connectivity S _).val.trans
    ((connectivity S _).val.symm (atom_mem_connectivity S _ (actualSpokes_colour S A x hxA a)))
    (hspoke a hxy)

/-- C07: EVERY finite real base, using the direct hull route. -/
theorem direct_real_acl [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()}
    (hE : UniqueDirection S E) (A : Finset M) :
    algebraicClosure (FullAut S) A = packetHull S H A := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra houtside
    exact outside_acl_of_direction_spokes S H cco hE.1 A x
      (outside_packet_not_parameter S H A x houtside)
      (outside_spoke_contains_direction S H hE A x houtside) hx
  · exact packetHull_subset_real_acl S H A

end CCO.DirectOwnerClosure
