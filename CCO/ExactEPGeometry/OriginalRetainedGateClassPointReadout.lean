import CCO.ExactEPGeometry.OriginalRetainedSelectedGateClasses

/-!
# B062 C88/C93: exact selected E-quotient class of a genuine old point

For every actual old reached type b and its real full gate K_b, the
C82/C83 class equivalence K_b ≃ K_b/E_b is evaluated on an ACTUAL old
point x. Its value is exactly the projected-gate class of the
actual canonical selected E-class of x, carried along the genuine
selected-sort E-class bijection. This is the missing pointwise
readout needed to prescribe phase bits for the SAME selected quotient
vertices, not arbitrary replacements in the same gate orbit.

No representative section, fake quotient identity, SAP or fresh
source property is introduced.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

theorem originalRetainedSelectedGateClassEquiv_mk
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) (x : B.Point b.val) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Qall := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    letI : ∀ i : Qall.Sorts, MulAction B.G (Qall.Point i) := Qall.action
    let Occ := OriginalOccupancy A B P base hBase E
    letI : Finite Occ := originalOccupancyFinite A B P base hBase E
    letI : Fintype Occ := Fintype.ofFinite Occ
    let D := originalSelectedSortRetyping A B P transport base hBase E
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b
    originalRetainedSelectedGateClassEquiv
        A B P transport tp hOne Kroot E hE b (K.project x) =
      (originalRetainedSelectedKernel A B P transport tp
        hOne Kroot E hE b).project
          (D.pointEquiv b.val (Quotient.mk'' x)) := by
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
  let hb := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hb
  change (D.gateClassEquiv Qall.homogeneous Kq)
      ((originalAllparentGateClassEquiv
        A B P transport tp base hBase E b.val K hb) (K.project x)) =
      (D.transportKernel Qall.homogeneous Kq).project
        (D.pointEquiv b.val (Quotient.mk'' x))
  rw [originalAllparentGateClassEquiv_mk
    A B P transport tp base hBase E b.val K hb x]
  rfl

end
end CCO.ExactEPGeometry
