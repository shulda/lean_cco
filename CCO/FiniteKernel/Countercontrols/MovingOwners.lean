import CCO.FiniteKernel.Countercontrols.RightRegular
import CCO.FiniteKernel.ActualMarginals
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.FinCases

/-!
# The homogeneous S₃ moving-owner countercontrol

The original language names every directed right-difference relation. Its
FULL automorphism group is the left regular S₃ group. The three actual
two-point owners are left cosets of the subgroup fixing 2. Their owner kernel
is trivial while each intrinsic fibre group has order two. Owner naming
destroys homogeneity; distinct local pair groups are trivial.
-/

namespace CCO.FiniteKernel.Countercontrols.MovingOwners

abbrev S3 := Equiv.Perm (Fin 3)
abbrev source := RightRegular.source S3

def owner (x : S3) : Fin 3 := x 2
def h : S3 := Equiv.swap 0 1

theorem owner_surjective : Function.Surjective owner := by
  intro i
  exact ⟨Equiv.swap 2 i,Equiv.swap_apply_left 2 i⟩

def partition : FinitePartition source (Fin 3) where
  owner := owner
  surjective := owner_surjective
  finite_fibre _ := inferInstance
  invariant g x y := by
    rw [RightRegular.fullAut_left S3 g x,RightRegular.fullAut_left S3 g y]
    change x 2 = y 2 ↔ (g.val 1) (x 2) = (g.val 1) (y 2)
    exact ⟨congrArg (g.val 1), fun hh => (g.val 1).injective hh⟩

local instance (i : Fin 3) : Fintype (partition.Fibre i) :=
  inferInstanceAs (Fintype {x : S3 // owner x = i})

def H : Subgroup S3 where
  carrier := {g | g 2 = 2}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a (b 2) = 2
    rw [hb,ha]
  inv_mem' := by
    intro a ha
    change a.symm 2 = 2
    apply a.injective
    rw [Equiv.apply_symm_apply,ha]

instance (g : S3) : Decidable (g ∈ H) := inferInstanceAs (Decidable (g 2 = 2))

theorem H_two_elements : ∀ g : S3, g ∈ H ↔ g = 1 ∨ g = h := by decide
theorem h_ne_one : h ≠ 1 := by decide
theorem h_square : h * h = 1 := by decide

/-- F is exactly equality of the three ACTUAL left cosets xH. -/
theorem left_coset_iff (x y : S3) : x⁻¹ * y ∈ H ↔ owner x = owner y := by
  change x.symm (y 2) = 2 ↔ x 2 = y 2
  constructor
  · intro hh
    have h' := congrArg x hh
    simpa only [Equiv.apply_symm_apply] using h'.symm
  · intro hh
    rw [←hh,Equiv.symm_apply_apply]

theorem owner_equivalence_definable : ∀ x y : S3,
    owner x = owner y ↔ x = y ∨ source.binary h x y := by
  change ∀ x y : S3, owner x = owner y ↔ x = y ∨ y = x * h
  decide

theorem owners_really_move : ∃ (g : source.Aut) (x : S3), owner (g.val x) ≠ owner x := by
  refine ⟨RightRegular.leftAut S3 (Equiv.swap 0 2),1,?_⟩
  decide

theorem core_trivial : ∀ t : S3, (∀ x : S3, x⁻¹ * t * x ∈ H) ↔ t = 1 := by decide

/-- The actual owner-action kernel is exactly core(H), not an abstract
unrelated permutation subgroup. -/
theorem kernel_core_iff (g : source.Aut) :
    g ∈ partition.kernel ↔ ∀ x : S3, x⁻¹ * (g.val 1) * x ∈ H := by
  rw [partition.mem_kernel_iff]
  constructor
  · intro hg x
    have hh := hg x
    rw [RightRegular.fullAut_left S3 g x] at hh
    change (g.val 1) (x 2) = x 2 at hh
    change x.symm ((g.val 1) (x 2)) = 2
    rw [hh,Equiv.symm_apply_apply]
  · intro hg x
    have hh := hg x
    change x.symm ((g.val 1) (x 2)) = 2 at hh
    have hh' := congrArg x hh
    rw [RightRegular.fullAut_left S3 g x]
    change (g.val 1) (x 2) = x 2
    simpa only [Equiv.apply_symm_apply] using hh'

theorem owner_kernel_trivial : partition.kernel = ⊥ := by
  apply le_antisymm
  · intro g hg
    have ht : g.val 1 = 1 := (core_trivial (g.val 1)).mp ((kernel_core_iff g).mp hg)
    change g = 1
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [RightRegular.fullAut_left S3 g x,ht,one_mul]
    rfl
  · exact bot_le

theorem source_homogeneous : source.Homogeneous := RightRegular.homogeneous S3

theorem fullAut_card : Nat.card source.Aut = 6 := by
  rw [←Nat.card_congr (RightRegular.fullAutEquiv S3),Nat.card_eq_fintype_card]
  decide

/-- Every internal binary relation on one class is either equality or its
unique off-diagonal colour h. This is an actual six-point finite calculation.
-/
theorem internal_palette : ∀ r x y : S3, owner x = owner y →
    (y = x * r ↔ (r = 1 ∧ x = y) ∨ (r = h ∧ x ≠ y)) := by decide

def every_fibre_perm_aut (i : Fin 3) (g : Equiv.Perm (partition.Fibre i)) :
    g ∈ (partition.fibreStructure i).autGroup := by
  constructor
  · intro r
    exact r.elim
  · intro r x y
    change S3 at r
    change (g y).val = (g x).val * r ↔ y.val = x.val * r
    rw [internal_palette r (g x).val (g y).val ((g x).property.trans (g y).property.symm),
      internal_palette r x.val y.val (x.property.trans y.property.symm)]
    have heq : (g x).val = (g y).val ↔ x.val = y.val := by
      constructor
      · exact fun hh => congrArg Subtype.val (g.injective (Subtype.ext hh))
      · exact fun hh => congrArg (fun x => (g x).val) (Subtype.ext hh)
    simp only [ne_eq,heq]

def intrinsicEquivPerm (i : Fin 3) : partition.Intrinsic i ≃ Equiv.Perm (partition.Fibre i) where
  toFun g := g.val
  invFun g := ⟨g,every_fibre_perm_aut i g⟩
  left_inv g := Subtype.ext rfl
  right_inv _ := rfl

def intrinsicMulEquivPerm (i : Fin 3) :
    partition.Intrinsic i ≃* Equiv.Perm (partition.Fibre i) where
  toEquiv := intrinsicEquivPerm i
  map_mul' _ _ := rfl

theorem fibre_card (i : Fin 3) : Nat.card (partition.Fibre i) = 2 := by
  letI : Fintype (partition.Fibre i) := inferInstanceAs (Fintype {x : S3 // owner x = i})
  rw [Nat.card_eq_fintype_card]
  fin_cases i <;> decide

theorem intrinsic_card (i : Fin 3) : Nat.card (partition.Intrinsic i) = 2 := by
  rw [Nat.card_congr (intrinsicEquivPerm i),Nat.card_perm,fibre_card]
  rfl

theorem all_fibre_permutations_square : ∀ (i : Fin 3)
    (g : Equiv.Perm (partition.Fibre i)), g * g = 1 := by decide

theorem intrinsic_exponent_two (i : Fin 3) (g : partition.Intrinsic i) : g * g = 1 := by
  apply Subtype.ext
  exact all_fibre_permutations_square i g.val

theorem binding_trivial (i : Fin 3) : partition.binding i = ⊥ := by
  apply le_antisymm
  · rintro a ⟨g,hg⟩
    have hg' : g = 1 := by
      apply Subtype.ext
      have hh : g.val ∈ (⊥ : Subgroup source.Aut) :=
        (congrArg (fun K : Subgroup source.Aut => g.val ∈ K) owner_kernel_trivial).mp g.property
      exact hh
    change a = 1
    simpa only [hg',map_one] using hg.symm
  · exact bot_le

theorem intrinsic_nontrivial (i : Fin 3) : ∃ g : partition.Intrinsic i, g ≠ 1 := by
  by_contra hh
  have hall : ∀ g : partition.Intrinsic i, g = 1 := by
    intro g
    by_contra hg
    exact hh ⟨g,hg⟩
  have hs : Subsingleton (partition.Intrinsic i) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have hc : Nat.card (partition.Intrinsic i) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs,inferInstance⟩
  rw [intrinsic_card] at hc
  cases hc

theorem binding_intrinsic_gap (i : Fin 3) : partition.binding i ≠ ⊤ := by
  intro heq
  obtain ⟨g,hg⟩ := intrinsic_nontrivial i
  have hm : g ∈ partition.binding i := heq ▸ (show g ∈ (⊤ : Subgroup _) from trivial)
  rw [binding_trivial] at hm
  exact hg hm

/-- A permutation of three points fixing two distinct points is identity. -/
theorem two_fixed_identity : ∀ (t : S3) (i j : Fin 3),
    i ≠ j → t i = i → t j = j → t = 1 := by decide

theorem pair_trivial {i j : Fin 3} (hij : i ≠ j)
    (g : partition.Intrinsic i) (g' : partition.Intrinsic j)
    (hpair : partition.Compatible g g') : g = 1 ∧ g' = 1 := by
  obtain ⟨x⟩ := partition.fibre_nonempty i
  obtain ⟨y⟩ := partition.fibre_nonempty j
  let t : S3 := (g.val x).val * x.val⁻¹
  have hg (z : partition.Fibre i) : (g.val z).val = t * z.val := by
    have hh := (BinaryStructure.Aut.binary (partition.fibreStructure i) g
      (x.val⁻¹ * z.val) x z).mpr
      (show z.val = x.val * (x.val⁻¹ * z.val) from (mul_inv_cancel_left _ _).symm)
    exact hh.trans (mul_assoc _ _ _).symm
  have hg' (z : partition.Fibre j) : (g'.val z).val = t * z.val := by
    have hh := (hpair.1 (x.val⁻¹ * z.val) x z).mpr
      (show z.val = x.val * (x.val⁻¹ * z.val) from (mul_inv_cancel_left _ _).symm)
    exact hh.trans (mul_assoc _ _ _).symm
  have ti : t i = i := by
    have hh := (g.val x).property
    rw [hg] at hh
    change t (x.val 2) = i at hh
    simpa only [show x.val 2 = i from x.property] using hh
  have tj : t j = j := by
    have hh := (g'.val y).property
    rw [hg'] at hh
    change t (y.val 2) = j at hh
    simpa only [show y.val 2 = j from y.property] using hh
  have ht : t = 1 := two_fixed_identity t i j hij ti tj
  constructor
  · apply Subtype.ext
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change (g.val z).val = z.val
    simpa only [ht,one_mul] using hg z
  · apply Subtype.ext
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change (g'.val z).val = z.val
    simpa only [ht,one_mul] using hg' z

theorem pairGroup_trivial {i j : Fin 3} (hij : i ≠ j) : partition.pairGroup i j = ⊥ := by
  apply le_antisymm
  · rintro ⟨g,g'⟩ hp
    obtain ⟨hg,hg'⟩ := pair_trivial hij g g' hp
    change (g,g') = 1
    exact Prod.ext hg hg'
  · exact bot_le

theorem pair_not_subdirect_left {i j : Fin 3} (hij : i ≠ j) :
    ¬ ∀ g : partition.Intrinsic i, ∃ g' : partition.Intrinsic j, partition.Compatible g g' := by
  intro hh
  obtain ⟨g,hg⟩ := intrinsic_nontrivial i
  obtain ⟨g',hp⟩ := hh g
  exact hg (pair_trivial hij g g' hp).1

def ownerNamed := source.ownerExpansion owner
def base : Finset S3 := {1,h}
def partialFlip (x : ↥base) : S3 := h * x.val

theorem named_aut_trivial (g : ownerNamed.Aut) : g.val = 1 := by
  have hm := (BinaryStructure.ownerExpansion_aut_iff source owner g.val).mp g.property
  let g₀ : source.Aut := ⟨g.val,hm.1⟩
  have hk : g₀ ∈ partition.kernel := (partition.mem_kernel_iff g₀).mpr hm.2
  rw [owner_kernel_trivial] at hk
  exact congrArg Subtype.val hk

theorem named_not_homogeneous : ¬ ownerNamed.Homogeneous := by
  intro hH
  have hinj : Function.Injective partialFlip := by
    intro x y hh
    exact Subtype.ext (mul_left_cancel hh)
  have hu : ∀ r x, ownerNamed.unary r (partialFlip x) ↔ ownerNamed.unary r x.val := by
    intro r x
    cases r with
    | inl r => exact r.elim
    | inr i =>
        have hh : owner (h * x.val) = owner x.val := by
          have hx : x.val = 1 ∨ x.val = h := by simpa only [base,Finset.mem_insert,Finset.mem_singleton] using x.property
          rcases hx with hx | hx <;> rw [hx] <;> decide
        change owner (h * x.val) = i ↔ owner x.val = i
        rw [hh]
  have hb : ∀ r x y, ownerNamed.binary r (partialFlip x) (partialFlip y) ↔ ownerNamed.binary r x.val y.val := by
    intro r x y
    exact BinaryStructure.Aut.binary source (RightRegular.leftAut S3 h) r x.val y.val
  obtain ⟨g,hg⟩ := hH base partialFlip hinj hu hb
  have hh := hg ⟨1,by simp [base]⟩
  rw [named_aut_trivial] at hh
  change (1 : S3) = h * 1 at hh
  rw [mul_one] at hh
  exact h_ne_one hh.symm

end CCO.FiniteKernel.Countercontrols.MovingOwners
