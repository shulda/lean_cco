import CCO.RigidGroupoid.Geometry.RootedGroupoid
import CCO.RigidGroupoid.Geometry.QuotientBijection
import CCO.RigidGroupoid.Geometry.Isotropy
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! The rigid groupoid really acts on its disjoint actual kernel-class sets.
Functoriality is proved from real bridge witnesses; freeness holds on every
point, without faithfulness of the original ambient group action. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

namespace Arrow
variable {S} {i j k : ι} {A : Kernel S i} {B : Kernel S j} {D : Kernel S k}

theorem quotientMap_id (q : A.Class) : (id A).quotientMap H q = q := by
  induction q using Quotient.inductionOn with
  | _ x => exact ((id A).quotientMap_eq_iff H x x).mpr (A.setoid.refl x)

theorem quotientMap_comp (R : Arrow S A B) (T : Arrow S B D) (q : A.Class) :
    (R.comp C T).quotientMap H q = T.quotientMap H (R.quotientMap H q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    apply ((R.comp C T).quotientMap_eq_iff H x _).mpr
    exact ⟨R.pointImage H x,R.pointImage_spec H x,T.pointImage_spec H _⟩

theorem nonidentity_fixed_point_free (R : Arrow S A A) (hne : R ≠ id A) (q : A.Class) :
    R.quotientMap H q ≠ q := by
  intro hfix
  apply hne
  exact R.eq_of_agree_at H (id A) q (hfix.trans (quotientMap_id H q).symm)

end Arrow

namespace Isotropy
variable {S} {i : ι} (A : Kernel S i)

theorem vectorSpace_finite :
    letI := commGroup C A H
    letI := vectorSpace C A H
    Module.Finite (ZMod 2) (Additive (Isotropy S C A)) := by
  letI := commGroup C A H
  letI := vectorSpace C A H
  letI := finiteType C A H
  exact inferInstance
end Isotropy

namespace Reached
variable {S} {i : ι} (A : Kernel S i)

theorem class_nonempty (b : Reached S A) : Nonempty (kernel H C b).Class := by
  obtain ⟨x⟩ := S.nonemptySort b.val
  exact ⟨(kernel H C b).project x⟩

theorem totalArrowFinite :
    Finite (Σ b : Reached S A, Σ c : Reached S A,
      Arrow S (kernel H C b) (kernel H C c)) := by
  letI : ∀ (b c : Reached S A), Finite (Arrow S (kernel H C b) (kernel H C c)) :=
    fun b c => arrowFinite S H _ _
  exact inferInstance

noncomputable def pointFunctor :
    letI := groupoid H C (A := A)
    CategoryTheory.Functor (Reached S A) (Type v) := by
  letI := groupoid H C (A := A)
  exact {
    obj := fun b => (kernel H C b).Class
    map := fun R => TypeCat.ofHom (R.quotientMap H)
    map_id := by
      intro b
      ext q
      exact Arrow.quotientMap_id H q
    map_comp := by
      intro b c d R T
      ext q
      exact Arrow.quotientMap_comp H C R T q
  }

/-- Literal disjoint union of the actual object point sets. -/
def Point := Σ b : Reached S A, (kernel H C b).Class

theorem free {b c : Reached S A}
    (R T : Arrow S (kernel H C b) (kernel H C c)) (q : (kernel H C b).Class)
    (h : R.quotientMap H q = T.quotientMap H q) : R = T :=
  R.eq_of_agree_at H T q h

end Reached
end CCO.RigidGroupoid.Geometry
