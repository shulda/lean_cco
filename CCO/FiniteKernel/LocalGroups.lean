import CCO.FiniteKernel.Partition
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod

/-! Intrinsic induced fibre groups, all directed cross relations, and genuine
finite local solution groups. No local projection is asserted surjective. -/

universe u v w z
namespace CCO.FiniteKernel.FinitePartition
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

def Compatible {i j : I} (g : P.Intrinsic i) (h : P.Intrinsic j) : Prop :=
  (∀ r (x : P.Fibre i) (y : P.Fibre j),
    S.binary r ((g.val x).val) ((h.val y).val) ↔ S.binary r x.val y.val) ∧
  (∀ r (y : P.Fibre j) (x : P.Fibre i),
    S.binary r ((h.val y).val) ((g.val x).val) ↔ S.binary r y.val x.val)

theorem Compatible.symm {i j : I} {g : P.Intrinsic i} {h : P.Intrinsic j}
    (hp : P.Compatible g h) : P.Compatible h g := ⟨hp.2,hp.1⟩

theorem compatible_one (i j : I) : P.Compatible (1 : P.Intrinsic i) (1 : P.Intrinsic j) :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ _ => Iff.rfl⟩

theorem Compatible.mul {i j : I} {g g' : P.Intrinsic i} {h h' : P.Intrinsic j}
    (h₁ : P.Compatible g h) (h₂ : P.Compatible g' h') :
    P.Compatible (g*g') (h*h') := by
  exact ⟨fun r x y => (h₁.1 r (g'.val x) (h'.val y)).trans (h₂.1 r x y),
    fun r y x => (h₁.2 r (h'.val y) (g'.val x)).trans (h₂.2 r y x)⟩

theorem Compatible.inv {i j : I} {g : P.Intrinsic i} {h : P.Intrinsic j}
    (hh : P.Compatible g h) : P.Compatible g⁻¹ h⁻¹ := by
  constructor
  · intro r x y
    simpa only [Subgroup.coe_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using
      (hh.1 r (g.val⁻¹ x) (h.val⁻¹ y)).symm
  · intro r y x
    simpa only [Subgroup.coe_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using
      (hh.2 r (h.val⁻¹ y) (g.val⁻¹ x)).symm

def pairGroup (i j : I) : Subgroup (P.Intrinsic i × P.Intrinsic j) where
  carrier := {p | P.Compatible p.1 p.2}
  one_mem' := P.compatible_one i j
  mul_mem' h₁ h₂ := Compatible.mul P h₁ h₂
  inv_mem' hh := Compatible.inv P hh

instance pairGroupFinite (i j : I) : Finite (P.pairGroup i j) := by infer_instance

def globalSolutions : Subgroup (∀ i, P.Intrinsic i) where
  carrier := {p | ∀ i j, i ≠ j → P.Compatible (p i) (p j)}
  one_mem' i j _ := P.compatible_one i j
  mul_mem' h₁ h₂ i j hij := Compatible.mul P (h₁ i j hij) (h₂ i j hij)
  inv_mem' hh i j hij := Compatible.inv P (hh i j hij)

def solutions (A : Finset I) : Subgroup (∀ i : ↥A, P.Intrinsic i.val) where
  carrier := {p | ∀ (i j : ↥A), i.val ≠ j.val → P.Compatible (p i) (p j)}
  one_mem' i j _ := P.compatible_one i.val j.val
  mul_mem' h₁ h₂ i j hij := Compatible.mul P (h₁ i j hij) (h₂ i j hij)
  inv_mem' hh i j hij := Compatible.inv P (hh i j hij)

instance solutionsFinite (A : Finset I) : Finite (P.solutions A) := by
  classical
  letI : ∀ i : ↥A, Fintype (P.Intrinsic i.val) := fun _ => Fintype.ofFinite _
  infer_instance

def restrictSolutions {A B : Finset I} (hAB : A ⊆ B) : P.solutions B →* P.solutions A where
  toFun h := ⟨fun i => h.val ⟨i.val,hAB i.property⟩,
    fun i j hij => h.property ⟨i.val,hAB i.property⟩ ⟨j.val,hAB j.property⟩ hij⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def restrictGlobal (A : Finset I) : P.globalSolutions →* P.solutions A where
  toFun h := ⟨fun i => h.val i.val,fun i j hij => h.property i.val j.val hij⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem restrictSolutions_apply {A B : Finset I} (hAB : A ⊆ B)
    (h : P.solutions B) (i : ↥A) :
    (P.restrictSolutions hAB h).val i = h.val ⟨i.val,hAB i.property⟩ := rfl

theorem empty_solution_unique (h h' : P.solutions ∅) : h = h' := by
  apply Subtype.ext
  funext i
  exact False.elim (Finset.notMem_empty i.val i.property)

end CCO.FiniteKernel.FinitePartition
