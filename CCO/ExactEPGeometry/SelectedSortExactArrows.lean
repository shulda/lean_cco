import CCO.ExactEPGeometry.SelectedSortExactWords
import CCO.RigidGroupoid.Geometry.Bridge

/-!
# B062 C83: full-RAW-exact Arrow transport along coherent selected sorts

The C82 equivariant carrier equivalences transfer EVERY entire RAW
word, including its internal witnesses, to the selected source.
Consequently they transfer the actual gate setoids and complete Arrow
relations, preserving all FOUR exact Arrow laws. Composition uses
surjectivity of the point equivalence at the REAL intermediate sort.

This constructs a faithful, identity/inverse/composition preserving
map on complete homs. It does NOT silently assert essential
surjectivity, merge arbitrary gate OBJECTS, supply a section of a
quotient action, or infer quotient SAP. Those subsequent C83 and
C84 obligations must be proved from the actual occupancy identities.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable [Fintype κ] {σ : κ ↪ ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (D : SelectedRetyping (X := X) σ (G := G))

namespace SelectedRetyping

/-- Move the entire ACTUAL relation to the canonical selected
carriers by the REAL inverse of each endpoint point equivalence. -/
def transportRelation {i j : ι} (R : TRel X i j) :
    TRel (fun k : κ => X (σ k)) (D.target i) (D.target j) :=
  fun x y => R ((D.pointEquiv i).symm x) ((D.pointEquiv j).symm y)

/-- Typed composition commutes with actual bijective retyping,
because EVERY middle-sort witness has precisely one selected
counterpart (not merely some common old E-class). -/
theorem transportRelation_comp {i j k : ι}
    (R : TRel X i j) (T : TRel X j k) :
    D.transportRelation (TRel.comp R T) =
      TRel.comp (D.transportRelation R) (D.transportRelation T) := by
  funext x z
  apply propext
  change (∃ y : X j,
      R ((D.pointEquiv i).symm x) y ∧
      T y ((D.pointEquiv k).symm z)) ↔
    ∃ y : X (σ (D.target j)),
      R ((D.pointEquiv i).symm x) ((D.pointEquiv j).symm y) ∧
      T ((D.pointEquiv j).symm y) ((D.pointEquiv k).symm z)
  constructor
  · rintro ⟨y,hxy,hyz⟩
    refine ⟨D.pointEquiv j y,?_,?_⟩
    · simpa only [Equiv.symm_apply_apply] using hxy
    · simpa only [Equiv.symm_apply_apply] using hyz
  · rintro ⟨y,hxy,hyz⟩
    exact ⟨(D.pointEquiv j).symm y,hxy,hyz⟩

/-- Converse commutes literally with endpoint retyping. -/
theorem transportRelation_converse {i j : ι}
    (R : TRel X i j) :
    D.transportRelation (TRel.converse R) =
      TRel.converse (D.transportRelation R) := rfl

/-- A genuine fully represented exact gate, with the complete
transported setoid on the selected carrier. -/
noncomputable def transportKernel (H : HomogeneousSource S G)
    {i : ι} (K : Kernel S i) :
    Kernel (selectedSortAtomicSource S σ) (D.target i) where
  setoid := {
    r := D.transportRelation K.rel
    iseqv := ⟨
      (by intro x; exact K.setoid.refl _),
      (by intro x y h; exact K.setoid.symm h),
      (by intro x y z hxy hyz; exact K.setoid.trans hxy hyz)⟩
  }
  exact := D.retypeFullExact H K.rel K.exact

/-- Transport one ACTUAL complete full-exact Arrow with all FOUR
groupoid equations, preserving the ENTIRE rectangular relation
rather than a chosen point or single generating orbit. -/
noncomputable def transportArrow (H : HomogeneousSource S G)
    {i j : ι} {Kp : Kernel S i} {Kq : Kernel S j}
    (R : Arrow S Kp Kq) :
    Arrow (selectedSortAtomicSource S σ)
      (D.transportKernel H Kp) (D.transportKernel H Kq) where
  rel := D.transportRelation R.rel
  exact := D.retypeFullExact H R.rel R.exact
  left := by
    change TRel.comp (D.transportRelation Kp.rel)
      (D.transportRelation R.rel) = D.transportRelation R.rel
    rw [← D.transportRelation_comp, R.left]
  right := by
    change TRel.comp (D.transportRelation R.rel)
      (D.transportRelation Kq.rel) = D.transportRelation R.rel
    rw [← D.transportRelation_comp, R.right]
  source := by
    change TRel.comp (D.transportRelation R.rel)
      (TRel.converse (D.transportRelation R.rel)) =
      D.transportRelation Kp.rel
    rw [← D.transportRelation_converse,← D.transportRelation_comp,R.source]
  target := by
    change TRel.comp (TRel.converse (D.transportRelation R.rel))
      (D.transportRelation R.rel) = D.transportRelation Kq.rel
    rw [← D.transportRelation_converse,← D.transportRelation_comp,R.target]

/-- The FULL selected exact Arrow identity is mapped from the
original exact gate identity; it is not logical equality. -/
theorem transportArrow_id (H : HomogeneousSource S G)
    {i : ι} (K : Kernel S i) :
    D.transportArrow H (Arrow.id K) =
      Arrow.id (D.transportKernel H K) :=
  Arrow.ext rfl

/-- Every selected Arrow's genuine complete inverse is retained. -/
theorem transportArrow_inv (H : HomogeneousSource S G)
    {i j : ι} {Kp : Kernel S i} {Kq : Kernel S j}
    (R : Arrow S Kp Kq) :
    D.transportArrow H R.inv = (D.transportArrow H R).inv :=
  Arrow.ext rfl

/-- Actual full Arrow composition respects all middle-sort
witnesses under retyping, for any provided genuine full
exact calculi on the two source structures. -/
theorem transportArrow_comp (H : HomogeneousSource S G)
    (C : ExactCalculus S)
    (CT : ExactCalculus (selectedSortAtomicSource S σ))
    {i j k : ι} {Kp : Kernel S i} {Kq : Kernel S j}
    {Kr : Kernel S k} (R : Arrow S Kp Kq) (T : Arrow S Kq Kr) :
    D.transportArrow H (R.comp C T) =
      (D.transportArrow H R).comp CT (D.transportArrow H T) :=
  Arrow.ext (D.transportRelation_comp R.rel T.rel)

/-- Faithfulness is literal: selected relations determine the
original relation pointwise via each endpoint bijection. -/
theorem transportArrow_injective (H : HomogeneousSource S G)
    {i j : ι} {Kp : Kernel S i} {Kq : Kernel S j} :
    Function.Injective
      (fun R : Arrow S Kp Kq => D.transportArrow H R) := by
  intro R U h
  apply Arrow.ext
  have hrel := congrArg Arrow.rel h
  funext x y
  have hxy := congrFun (congrFun hrel (D.pointEquiv i x))
    (D.pointEquiv j y)
  change D.transportRelation R.rel (D.pointEquiv i x)
      (D.pointEquiv j y) =
    D.transportRelation U.rel (D.pointEquiv i x)
      (D.pointEquiv j y) at hxy
  change R.rel x y = U.rel x y
  simpa only [transportRelation, Equiv.symm_apply_apply] using hxy

end SelectedRetyping
end
end CCO.ExactEPGeometry
