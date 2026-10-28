import CCO.FiniteKernel.Named.Axes
import CCO.FiniteKernel.Named.Goursat
import CCO.FiniteKernel.F2Subgroup
import Mathlib.Algebra.Field.ZMod

/-! Actual full-group pair images, transported by the supplied elementary
abelian intrinsic group representations, are genuine F2-subspaces. Their
surjective projections follow from original finite-axis homogeneity, not
from an extra subdirectness or linearity premise. -/

universe u v w z a
namespace CCO.FiniteKernel.NamedAxes
noncomputable section

variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : NamedAxes S I)
variable {V : I → Type a} [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

def linearPair (i j : I) : Submodule F2 (V i × V j) :=
  F2Subgroup.linearPreimage (F2Subgroup.pairRepresentation (e i) (e j)).toMonoidHom (P.actualPair i j)

@[simp] theorem mem_linearPair (i j : I) (x : V i) (y : V j) :
    (x,y) ∈ P.linearPair e i j ↔
      (e i (Multiplicative.ofAdd x),e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j := Iff.rfl

theorem linearPair_subdirect_left (H : S.Homogeneous) (i j : I) :
    Function.Surjective (Prod.fst ∘ (P.linearPair e i j).subtype) := by
  intro x
  obtain ⟨b,hb⟩ := P.actual_pair_subdirect_left H i j (e i (Multiplicative.ofAdd x))
  let y := Multiplicative.toAdd ((e j).symm b)
  have hy : e j (Multiplicative.ofAdd y) = b := (e j).apply_symm_apply b
  refine ⟨⟨(x,y),?_⟩,rfl⟩
  change (e i (Multiplicative.ofAdd x),e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j
  rw [hy]
  exact hb

theorem linearPair_subdirect_right (H : S.Homogeneous) (i j : I) :
    Function.Surjective (Prod.snd ∘ (P.linearPair e i j).subtype) := by
  intro y
  obtain ⟨b,hb⟩ := P.actual_pair_subdirect_right H i j (e j (Multiplicative.ofAdd y))
  let x := Multiplicative.toAdd ((e i).symm b)
  have hx : e i (Multiplicative.ofAdd x) = b := (e i).apply_symm_apply b
  refine ⟨⟨(x,y),?_⟩,rfl⟩
  change (e i (Multiplicative.ofAdd x),e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j
  rw [hx]
  exact hb

abbrev PairSpace (i j : I) := Named.CommonSpace (P.linearPair e i j)

def pairLeft (i j : I) : V i →ₗ[F2] P.PairSpace e i j := Named.leftCheck (P.linearPair e i j)

def pairRight (H : S.Homogeneous) (i j : I) : V j →ₗ[F2] P.PairSpace e i j :=
  Named.rightCheck (P.linearPair e i j)
    (P.linearPair_subdirect_left e H i j) (P.linearPair_subdirect_right e H i j)

theorem actual_pair_goursat (H : S.Homogeneous) (i j : I) (x : V i) (y : V j) :
    (e i (Multiplicative.ofAdd x),e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j ↔
      P.pairLeft e i j x = P.pairRight e H i j y :=
  (P.mem_linearPair e i j x y).symm.trans
    (Named.mem_pair_iff_checks _ (P.linearPair_subdirect_left e H i j)
      (P.linearPair_subdirect_right e H i j) x y)

theorem pairLeft_surjective (i j : I) : Function.Surjective (P.pairLeft e i j) :=
  Named.leftCheck_surjective _

theorem pairRight_surjective (H : S.Homogeneous) (i j : I) : Function.Surjective (P.pairRight e H i j) :=
  Named.rightCheck_surjective _ _ _

theorem linearPair_left_kernel (i j : I) (x : V i) :
    x ∈ Named.leftKernel (P.linearPair e i j) ↔
      (e i (Multiplicative.ofAdd x),1) ∈ P.actualPair i j := by
  rw [Named.mem_leftKernel]
  change (e i (Multiplicative.ofAdd x),e j 1) ∈ P.actualPair i j ↔ _
  rw [map_one]

theorem linearPair_right_kernel (i j : I) (y : V j) :
    y ∈ Named.rightKernel (P.linearPair e i j) ↔
      (1,e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j := by
  rw [Named.mem_rightKernel]
  change (e i 1,e j (Multiplicative.ofAdd y)) ∈ P.actualPair i j ↔ _
  rw [map_one]

def linearImage (A : Finset I) : Submodule F2 (∀ i : ↥A,V i.val) :=
  F2Subgroup.linearPreimage (F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)).toMonoidHom
    (P.actualImage A)

@[simp] theorem mem_linearImage (A : Finset I) (x : ∀ i : ↥A,V i.val) :
    x ∈ P.linearImage e A ↔
      (fun i : ↥A => e i.val (Multiplicative.ofAdd (x i))) ∈ P.actualImage A := Iff.rfl

def linearImageEquivActual (A : Finset I) : P.linearImage e A ≃ P.actualImage A where
  toFun x := ⟨F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val) (Multiplicative.ofAdd x.val),x.property⟩
  invFun y := ⟨Multiplicative.toAdd
    ((F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)).symm y.val),by
      change F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)
        ((F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)).symm y.val) ∈ P.actualImage A
      rw [MulEquiv.apply_symm_apply]
      exact y.property⟩
  left_inv x := by apply Subtype.ext; exact
    (F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)).symm_apply_apply (Multiplicative.ofAdd x.val)
  right_inv y := by apply Subtype.ext; exact
    (F2Subgroup.tupleRepresentation (fun i : ↥A => e i.val)).apply_symm_apply y.val

end
end CCO.FiniteKernel.NamedAxes
