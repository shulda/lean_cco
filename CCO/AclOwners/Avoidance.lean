import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.Preorder.Finite

/-! Generic finite-action avoidance, including its finite-index support.
The coset-cover theorem is the proved theorem of the pinned Mathlib, rather
than an additional mathematical assumption. No topology or faithfulness is used. -/

universe u v
namespace CCO.AclOwners

open scoped Pointwise

variable {G : Type u} [Group G]

/-- Virtual containment is finite index of the intersection in the first group. -/
abbrev VirtualLe (U V : Subgroup G) : Prop := V.IsFiniteRelIndex U

@[instance_reducible]
def virtualPreorder : Preorder (Subgroup G) where
  le := VirtualLe
  lt U V := VirtualLe U V ∧ ¬ VirtualLe V U
  le_refl _ := inferInstance
  le_trans _ _ _ hUV hVW := hVW.trans hUV
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Mutual virtual containment is commensurability, with no antisymmetry claim. -/
def virtualCommensurability : Setoid (Subgroup G) where
  r U V := VirtualLe U V ∧ VirtualLe V U
  iseqv := ⟨fun _ => ⟨inferInstance, inferInstance⟩,
    fun h => ⟨h.2, h.1⟩,
    fun hUV hVW => ⟨hVW.1.trans hUV.1, hUV.2.trans hVW.2⟩⟩

/-- A finite nonempty list has a maximal virtual class; equality of subgroups
is not asserted when the converse virtual containment holds. -/
theorem exists_maximal_virtual_class (s : Finset (Subgroup G)) (hs : s.Nonempty) :
    ∃ U ∈ s, ∀ V ∈ s, VirtualLe U V → VirtualLe V U := by
  letI : Preorder (Subgroup G) := virtualPreorder
  exact s.exists_maximal hs

/-- No finite family of cosets of infinite-index subgroups covers a group. -/
theorem no_finite_infinite_index_coset_cover {I : Type*} (s : Finset I)
    (U : I → Subgroup G) (g : I → G)
    (hU : ∀ i ∈ s, ¬ (U i).FiniteIndex) :
    (⋃ i ∈ s, g i • (U i : Set G)) ≠ Set.univ := by
  intro hcover
  obtain ⟨i, hi, hfinite⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcover
  exact hU i hi hfinite

variable {M : Type v} [MulAction G M]

theorem stabilizer_not_finiteIndex_of_infinite_orbit (a : M)
    (ha : (MulAction.orbit G a).Infinite) : ¬ (MulAction.stabilizer G a).FiniteIndex := by
  intro hfinite
  letI := hfinite
  letI : Finite (MulAction.orbit G a) :=
    Finite.of_equiv (G ⧸ MulAction.stabilizer G a)
      (MulAction.orbitEquivQuotientStabilizer G a).symm
  exact ha (Set.finite_coe_iff.mp inferInstance)

/-- One group element moves every requested point away from every forbidden
point. Empty requests are included, and the action need not be faithful. -/
theorem finite_action_avoidance (A Z : Finset M)
    (hA : ∀ a ∈ A, (MulAction.orbit G a).Infinite) :
    ∃ g : G, ∀ a ∈ A, ∀ z ∈ Z, g • a ≠ z := by
  classical
  by_contra! h
  let I := {p : ↥A × ↥Z // ∃ g : G, g • p.1.val = p.2.val}
  let f : I → G := fun p => p.property.choose
  let U : I → Subgroup G := fun p => MulAction.stabilizer G p.val.1.val
  have hf (p : I) : f p • p.val.1.val = p.val.2.val := p.property.choose_spec
  have hcover : (⋃ p ∈ (Finset.univ : Finset I), f p • (U p : Set G)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨a, ha, z, hz, hgz⟩ := h g
    let p : I := ⟨(⟨a, ha⟩, ⟨z, hz⟩), g, hgz⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    apply (mem_leftCoset_iff (f p)).mpr
    change (f p)⁻¹ * g ∈ MulAction.stabilizer G a
    change ((f p)⁻¹ * g) • a = a
    have hfp : f p • a = z := hf p
    rw [mul_smul, hgz, ← hfp, inv_smul_smul]
  exact no_finite_infinite_index_coset_cover Finset.univ U f
    (fun p _ => stabilizer_not_finiteIndex_of_infinite_orbit _
      (hA _ p.val.1.property)) hcover

/-- Set form of the same simultaneous avoidance request. -/
theorem finite_action_avoidance_disjoint (A Z : Finset M)
    (hA : ∀ a ∈ A, (MulAction.orbit G a).Infinite) :
    ∃ g : G, Disjoint ((fun x => g • x) '' (A : Set M)) (Z : Set M) := by
  obtain ⟨g, hg⟩ := finite_action_avoidance A Z hA
  refine ⟨g, Set.disjoint_left.mpr ?_⟩
  rintro z ⟨a, ha, rfl⟩ hz
  exact hg a ha (g • a) hz rfl

end CCO.AclOwners
