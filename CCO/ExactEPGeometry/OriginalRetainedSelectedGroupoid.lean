import CCO.ExactEPGeometry.OriginalSelectedArrowCorrespondence
import CCO.ExactEPGeometry.OriginalRetainedProjectedGateBase

/-!
# B062 C83: ALL actual retained full-Reached projected exact groupoid gates

The original retained-case condition E <= the genuine selected
root largest old gate gives e_b <= K_b for EVERY actual Reached
object b, not merely a selected pair or artificially supplied
nestedness hypotheses. The exact actual all-parent quotient,
one-per-E-occupancy selected source and full exact retyping
then construct the projected K_b/E_b as a genuine selected
full-RAW exact Kernel. The full Arrow equivalence applies to
EVERY pair of real Reached objects, including repeated occupancy
sorts, and to ALL their whole original/selected Hom arrows.

There is no hypothesis of selected projected gate exactness, no
quotient SAP or automorphism section, and no choice of one orbit.
Objectwise identity/phase normalisation upon quotienting the
Reached object set by E-occupancy remains a separate C84 obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual FULL RAW exact selected quotient K_b/E_b for
EVERY reached parent b in the retained case. This is a real
full exact Kernel on the genuine occupancy-selected CurrentSource,
with the actual local e_b <= K_b proved from C56 and E <= G. -/
noncomputable def originalRetainedSelectedKernel
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    Kernel
      (originalExactSelectedQuotientCurrentSource A B P transport
        (P.parent r) (fun i => hOne (P.parent r) i) E).source
      (Quotient.mk'' b.val :
        OriginalOccupancy A B P (P.parent r)
          (fun i => hOne (P.parent r) i) E) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Kb := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hb := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
  let C := OriginalOccupancy A B P base hBase E
  letI : Finite C := originalOccupancyFinite A B P base hBase E
  letI : Fintype C := Fintype.ofFinite C
  let σ : C ↪ B.Sorts :=
    originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Q.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  change Kernel (selectedSortAtomicSource Q.source σ) (D.target b.val)
  exact D.transportKernel Q.homogeneous
    (originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val Kb hb)

/-- Full C83 for the GENUINE connected rigid-groupoid source:
EVERY original full Arrow b -> c corresponds BIJECTIVELY to
EVERY whole selected quotient Arrow between the actual
projected full exact gates constructed above. Each source object
comes from the actual Reached, and ALL E-nesting providers have
already been discharged. No future quotient step supplies an
assumption needed for this statement. -/
noncomputable def originalRetainedSelectedArrowEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot) :
    Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c) ≃
    Arrow
      (originalExactSelectedQuotientCurrentSource A B P transport
        (P.parent r) (fun i => hOne (P.parent r) i) E).source
      (originalRetainedSelectedKernel
        A B P transport tp hOne Kroot E hE b)
      (originalRetainedSelectedKernel
        A B P transport tp hOne Kroot E hE c) := by
  exact originalCoherentSelectedArrowEquiv A B P transport tp
    (P.parent r) (fun i => hOne (P.parent r) i) E
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b)
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) c)
    (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b)
    (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE c)

end
end CCO.ExactEPGeometry
