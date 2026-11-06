import CCO.ExactEPGeometry.OriginalRetainedNormalizedArrows

/-!
# B062 C84: full selected Arrow composition from actual E-quotient images

C83 proves a whole Hom equivalence from the actual old Reached groupoid
to the genuine one-per-E-occupancy selected quotient source, but a
hom-set bijection alone does not certify preservation of composition.
This file proves that the TRUE source-to-selected map respects the
composition of EVERY two complete old Arrows, including all original
intermediate current sorts and all projected E-kernel classes.

The source Arrow laws give actual E-bisaturation at each endpoint
because the real E restriction lies below every reached gate.
Quotient.image_comp then transports the FULL old composition across
the actual simultaneous quotient, and the previously proved
SelectedRetyping.transportRelation_comp transports ALL resulting
intermediate quotient classes into the selected occupancy carriers.
No arbitrary reverse descent, quotient SAP, group action section,
or generator-only assumption occurs.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C84 precise functoriality of the COMPLETE selected-quotient
bridge correspondence for ANY triple of true old Reached objects.
The selected Arrow Hom types already have both projected full-exact
gates certified by the source C82/C83 theorems, and the equality
holds on WHOLE real rectangular binary relations. -/
theorem originalRetainedSelectedArrow_comp
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c d : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) c))
    (U : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) c)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) d)) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E
    let CQ := exactCalculus_of_homogeneous_CCO
      Q.source Q.homogeneous Q.cco
    (originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE b d) (R.comp CB U) =
      ((originalRetainedSelectedArrowEquiv A B P transport tp
        hOne Kroot E hE b c) R).comp CQ
        ((originalRetainedSelectedArrowEquiv A B P transport tp
          hOne Kroot E hE c d) U) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  let Qsel : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO
    Qsel.source Qsel.homogeneous Qsel.cco
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let σ : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let π : ∀ p : B.Sorts, B.Point p → Qall.Point p :=
    fun _ x => Quotient.mk'' x
  let Kb := Reached.kernel B.homogeneous CB b
  let Kc := Reached.kernel B.homogeneous CB c
  let Kd := Reached.kernel B.homogeneous CB d
  have hNb : ∀ x y : B.Point b.val,
      π b.val x = π b.val y → Kb.rel x y := by
    intro x y hxy
    exact (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b) (Quotient.exact hxy)
  have hNc : ∀ x y : B.Point c.val,
      π c.val x = π c.val y → Kc.rel x y := by
    intro x y hxy
    exact (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE c) (Quotient.exact hxy)
  have hNd : ∀ x y : B.Point d.val,
      π d.val x = π d.val y → Kd.rel x y := by
    intro x y hxy
    exact (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE d) (Quotient.exact hxy)
  have hR : Quotient.Bisaturated (π b.val) (π c.val) R.rel :=
    R.nested_bisaturated (π b.val) (π c.val) hNb hNc
  have hU : Quotient.Bisaturated (π c.val) (π d.val) U.rel :=
    U.nested_bisaturated (π c.val) (π d.val) hNc hNd
  have hImg :
      Quotient.image (π b.val) (π d.val) (TRel.comp R.rel U.rel) =
        TRel.comp
          (Quotient.image (π b.val) (π c.val) R.rel)
          (Quotient.image (π c.val) (π d.val) U.rel) := by
    exact Quotient.image_comp (π b.val) (π c.val) (π d.val)
      Quotient.mk''_surjective Quotient.mk''_surjective
      Quotient.mk''_surjective R.rel U.rel hR hU
  apply Arrow.ext
  change D.transportRelation
      (Quotient.image (π b.val) (π d.val)
        (TRel.comp R.rel U.rel)) =
    TRel.comp
      (D.transportRelation
        (Quotient.image (π b.val) (π c.val) R.rel))
      (D.transportRelation
        (Quotient.image (π c.val) (π d.val) U.rel))
  calc
    D.transportRelation
        (Quotient.image (π b.val) (π d.val)
          (TRel.comp R.rel U.rel)) =
      D.transportRelation
        (TRel.comp
          (Quotient.image (π b.val) (π c.val) R.rel)
          (Quotient.image (π c.val) (π d.val) U.rel)) :=
      congrArg (D.transportRelation) hImg
    _ = TRel.comp
          (D.transportRelation
            (Quotient.image (π b.val) (π c.val) R.rel))
          (D.transportRelation
            (Quotient.image (π c.val) (π d.val) U.rel)) :=
      D.transportRelation_comp _ _

end
end CCO.ExactEPGeometry
