import CCO.ExactEPGeometry.OriginalRetainedSelectedGroupoid
import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C83/C88: pairwise inverse image of EVERY selected whole exact Arrow

The C83 selected one-parent-per-original-E-occupancy quotient has an
ACTUAL entire-Hom equivalence for the genuinely nested old reached
gate kernels. Its forward map is the complete E-bisaturated quotient
image followed by the proved equivariant selected carrier equivalence.

Here we identify its relation on each pair of selected points obtained
from ACTUAL old current representatives. The selected Arrow holds on
those points exactly when its old full Arrow holds on the old points.
Both directions rely on the true endpoint E<=K hypotheses, hence on
whole Arrow bisaturation; the reverse is not inferred from an
arbitrary, non-saturated quotient relation.

This provides the real pair bridge needed for C88/C96 marked-age
converse, without assuming quotient SAP or equating E equality with
the whole K/E gate identity.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- For any real reached endpoints and any WHOLE original full-exact
Arrow, the actual selected quotient Arrow contains the two projected
old points if and only if the old Arrow contains their actual pair.
This remains true when the endpoints are not the chosen occupancy
representatives. -/
theorem originalRetainedSelectedArrow_real_pair_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c))
    (x : B.Point b.val) (y : B.Point c.val) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Qall := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
    let D := originalSelectedSortRetyping
      A B P transport base hBase E
    ((originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE b c) R).rel
      (D.pointEquiv b.val (Quotient.mk'' x))
      (D.pointEquiv c.val (Quotient.mk'' y)) ↔ R.rel x y := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let sigma : Occ ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let pi : ∀ i : B.Sorts, B.Point i → Qall.Point i :=
    fun _ z => Quotient.mk'' z
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous CB b
  let Kc := Reached.kernel B.homogeneous CB c
  have hNb : ∀ a z : B.Point b.val, pi b.val a = pi b.val z →
      Kb.rel a z := by
    intro a z h
    exact (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b) (Quotient.exact h)
  have hNc : ∀ a z : B.Point c.val, pi c.val a = pi c.val z →
      Kc.rel a z := by
    intro a z h
    exact (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE c) (Quotient.exact h)
  have hPull : GroupActions.pullback (pi b.val) (pi c.val)
      (Quotient.image (pi b.val) (pi c.val) R.rel) = R.rel :=
    R.image_pullback_nested (pi b.val) (pi c.val) hNb hNc
  have hPair : Quotient.image (pi b.val) (pi c.val) R.rel
      (pi b.val x) (pi c.val y) ↔ R.rel x y :=
    Iff.of_eq (congrFun (congrFun hPull x) y)
  change D.transportRelation
      (Quotient.image (pi b.val) (pi c.val) R.rel)
        (D.pointEquiv b.val (pi b.val x))
        (D.pointEquiv c.val (pi c.val y)) ↔ R.rel x y
  simpa only [SelectedRetyping.transportRelation,
    Equiv.symm_apply_apply] using hPair

end
end CCO.ExactEPGeometry
