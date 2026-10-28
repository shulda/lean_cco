import CCO.RigidGroupoid.Geometry.Bridge
import Mathlib.CategoryTheory.Groupoid

/-! One reached object per original named sort, proved from the SAME-SORT
symmetry of Rᵒ;S. The resulting actual exact-arrow category is a finite
connected groupoid; no parity, Hasse, SAP or distinguished involution enters. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

theorem kernel_ext {i : ι} {A B : Kernel S i} (h : A.setoid = B.setoid) : A = B := by
  cases A
  cases B
  cases h
  rfl

include H
theorem target_kernel_unique {i j : ι} {A : Kernel S i}
    (R T : Bridge S A j) :
    TRel.comp (TRel.converse R.rel) R.rel = TRel.comp (TRel.converse T.rel) T.rel := by
  let U := TRel.comp (TRel.converse R.rel) T.rel
  have hU : TRel.Invariant (G := G) U :=
    TRel.invariant_comp _ _ (TRel.invariant_converse _ (R.exact.invariant S H))
      (T.exact.invariant S H)
  have hs : TRel.converse U = U := invariant_same_sort_converse S H U hU
  calc
    TRel.comp (TRel.converse R.rel) R.rel =
        TRel.comp (TRel.converse R.rel) (TRel.comp A.rel R.rel) := by rw [R.left]
    _ = TRel.comp (TRel.converse R.rel)
        (TRel.comp (TRel.comp T.rel (TRel.converse T.rel)) R.rel) := by rw [T.source]
    _ = TRel.comp U (TRel.converse U) := by
      dsimp only [U]
      simp only [TRel.converse_comp,TRel.converse_converse,TRel.comp_assoc]
    _ = TRel.comp (TRel.converse U) U := by rw [hs]
    _ = TRel.comp (TRel.converse T.rel)
        (TRel.comp (TRel.comp R.rel (TRel.converse R.rel)) T.rel) := by
      dsimp only [U]
      simp only [TRel.converse_comp,TRel.converse_converse,TRel.comp_assoc]
    _ = TRel.comp (TRel.converse T.rel) T.rel := by rw [R.source,T.left]

theorem bridge_targetKernel_unique {i j : ι} {A : Kernel S i}
    (R T : Bridge S A j) : R.targetKernel H C = T.targetKernel H C := by
  have hr := target_kernel_unique S H R T
  have hs : (R.targetKernel H C).setoid = (T.targetKernel H C).setoid := by
    apply Setoid.ext
    intro x y
    exact Iff.of_eq (congrFun (congrFun hr x) y)
  exact kernel_ext S hs

theorem arrowFinite {i j : ι} (A : Kernel S i) (B : Kernel S j) : Finite (Arrow S A B) := by
  letI : Finite {R : TRel X i j // FullExact S R} := finite_fullExact S H i j
  let f : Arrow S A B → {R : TRel X i j // FullExact S R} := fun R => ⟨R.rel,R.exact⟩
  apply Finite.of_injective f
  intro R T h
  exact Arrow.ext (congrArg Subtype.val h)

def Reached {i : ι} (A : Kernel S i) := {j : ι // Nonempty (Bridge S A j)}

namespace Reached
variable {S} {i : ι} {A : Kernel S i}

instance : Finite (Reached S A) := by
  letI : Fintype ι := S.finiteSort
  exact inferInstanceAs (Finite {j : ι // Nonempty (Bridge S A j)})

def root (A : Kernel S i) : Reached S A := ⟨i,⟨(Arrow.id A).toBridge⟩⟩

noncomputable def bridge (b : Reached S A) : Bridge S A b.val := Classical.choice b.property

noncomputable def kernel (b : Reached S A) : Kernel S b.val := (bridge b).targetKernel H C

noncomputable def rootArrow (b : Reached S A) : Arrow S A (kernel H C b) := (bridge b).toArrow H C

theorem root_kernel : kernel H C (root A) = A := by
  have h := bridge_targetKernel_unique S H C (bridge (root A)) (Arrow.id A).toBridge
  apply h.trans
  have hs : ((Arrow.id A).toBridge.targetKernel H C).setoid = A.setoid := by
    apply Setoid.ext
    intro x y
    exact Iff.of_eq (congrFun (congrFun (Arrow.id A).target x) y)
  exact kernel_ext S hs

noncomputable def groupoid : CategoryTheory.Groupoid (Reached S A) where
  Hom b c := Arrow S (kernel H C b) (kernel H C c)
  id b := Arrow.id (kernel H C b)
  comp R T := R.comp C T
  id_comp R := Arrow.id_comp C R
  comp_id R := Arrow.comp_id C R
  assoc R T U := Arrow.comp_assoc C R T U
  inv R := R.inv
  inv_comp R := Arrow.inv_comp C R
  comp_inv R := Arrow.comp_inv C R

/-- Every two reached objects have an ACTUAL exact bridge, via the common
root. This is connectedness, including the root-only/trivial-isotropy case. -/
noncomputable def connectingArrow (b c : Reached S A) :
    Arrow S (kernel H C b) (kernel H C c) :=
  (rootArrow H C b).inv.comp C (rootArrow H C c)

theorem connected (b c : Reached S A) :
    Nonempty (Arrow S (kernel H C b) (kernel H C c)) := ⟨connectingArrow H C b c⟩

end Reached
end CCO.RigidGroupoid.Geometry
