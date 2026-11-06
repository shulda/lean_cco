import CCO.ExactEPGeometry.OriginalRetainedGateClassPointReadout

/-!
# B062 C90/C94: EXACT original E-point lifts from reached selected quotient sorts

Every actually occurring selected E-quotient point on the true
E-occupancy sort of a reached parent b is an image of an actual
original current point x of THAT reached sort, not merely of some
other E-class in its K_b/E_b gate orbit. C49/C66's bijective,
equivariant selected-sort point transport and the literal
surjectivity of the local E quotient supply x.

The actual projected K/E gate class of this very selected point is
exactly the image of the old K-class of x, by the real C82/C83 gate
class equivalence. These equations let C94 preserve prescriptions
for PRECISE selected E-classes rather than a convenient unrelated
representative within the same projected gate.

No group section, quotient SAP, new exactness provider, arbitrary
unrealized diagram or fake logical identity.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- An ACTUAL point in the genuine selected quotient occupancy sort
of reached b has a genuine old representative of B's ORIGINAL
current sort b, with no choice of a different global E-class. -/
noncomputable def originalSelectedReachedEclassRepresentative
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (b : Reached B.source Kroot)
    (q : (originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E).Point
          (Quotient.mk'' b.val :
            OriginalOccupancy A B P (P.parent r)
              (fun i => hOne (P.parent r) i) E)) :
    B.Point b.val := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let D : SelectedRetyping (X := Qall.Point)
      (originalOccupancyRepresentativeEmbedding A B P base hBase E)
      (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  exact Quotient.out ((D.pointEquiv b.val).symm q)

/-- This is EXACTLY the displayed selected E-class, with the whole
old E relation encoded in Quotient.mk rather than a chosen K-class
representative. -/
theorem originalSelectedReachedEclassRepresentative_spec
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (b : Reached B.source Kroot)
    (q : (originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E).Point
          (Quotient.mk'' b.val :
            OriginalOccupancy A B P (P.parent r)
              (fun i => hOne (P.parent r) i) E)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Qall := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
    let Occ := OriginalOccupancy A B P base hBase E
    letI : Finite Occ := originalOccupancyFinite A B P base hBase E
    letI : Fintype Occ := Fintype.ofFinite Occ
    let D := originalSelectedSortRetyping A B P transport base hBase E
    D.pointEquiv b.val
      (Quotient.mk'' (originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E b q)) = q := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let D : SelectedRetyping (X := Qall.Point)
      (originalOccupancyRepresentativeEmbedding A B P base hBase E)
      (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  change D.pointEquiv b.val
    (Quotient.mk'' (Quotient.out ((D.pointEquiv b.val).symm q))) = q
  have hout :
      (Quotient.mk'' (Quotient.out ((D.pointEquiv b.val).symm q)) :
        Qall.Point b.val) = (D.pointEquiv b.val).symm q :=
    Quotient.out_eq ((D.pointEquiv b.val).symm q)
  rw [hout]
  exact (D.pointEquiv b.val).apply_symm_apply q

/-- The SAME chosen old E-class representative has the required
complete old-K to selected-K/E gate-point image, with NO replacement
of its actual quotient E-class. -/
theorem originalSelectedReachedEclassRepresentative_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot)
    (q : (originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E).Point
          (Quotient.mk'' b.val :
            OriginalOccupancy A B P (P.parent r)
              (fun i => hOne (P.parent r) i) E)) :
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b
    originalRetainedSelectedGateClassEquiv A B P transport tp
      hOne Kroot E hE b
      (K.project (originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E b q)) =
      (originalRetainedSelectedKernel A B P transport tp
        hOne Kroot E hE b).project q := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let D : SelectedRetyping (X := Qall.Point)
      (originalOccupancyRepresentativeEmbedding A B P base hBase E)
      (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b
  let x := originalSelectedReachedEclassRepresentative
    A B P transport hOne Kroot E b q
  have hs : D.pointEquiv b.val (Quotient.mk'' x) = q :=
    originalSelectedReachedEclassRepresentative_spec
      A B P transport hOne Kroot E b q
  have hm := originalRetainedSelectedGateClassEquiv_mk
    A B P transport tp hOne Kroot E hE b x
  change originalRetainedSelectedGateClassEquiv A B P transport tp
      hOne Kroot E hE b (K.project x) =
    (originalRetainedSelectedKernel A B P transport tp
      hOne Kroot E hE b).project q
  calc
    originalRetainedSelectedGateClassEquiv A B P transport tp
        hOne Kroot E hE b (K.project x) =
      (originalRetainedSelectedKernel A B P transport tp
        hOne Kroot E hE b).project
          (D.pointEquiv b.val (Quotient.mk'' x)) := hm
    _ = (originalRetainedSelectedKernel A B P transport tp
          hOne Kroot E hE b).project q :=
      congrArg (fun z => (originalRetainedSelectedKernel
        A B P transport tp hOne Kroot E hE b).project z) hs

end
end CCO.ExactEPGeometry
