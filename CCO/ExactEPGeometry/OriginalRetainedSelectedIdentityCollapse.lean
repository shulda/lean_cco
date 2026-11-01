import CCO.ExactEPGeometry.OriginalRetainedBridgeNormalization
import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowUnits
import CCO.ExactEPGeometry.OriginalReachedOccupancyAnchors

/-!
# B062 C84: real old G-identity bridges become selected gate identities

The old canonical original G traces I_bc connect EVERY two actual
reached types in one E-occupancy component. Their normalization
through that component's ACTUAL selected reached anchor is the
complete old full-exact gate identity, by the proved C79 composition
equations, not merely a selected graph edge or an equality relation.

The complete C83 source-to-selected quotient Hom equivalence maps
that old gate identity to the whole projected selected K/E gate
identity. This is the precise object-merging equation needed by
the source C84 character correction: old duplicate identities
collapse to new GROUPoid identities, not to logical diagonal.
No quotient SAP, invented quotient action section or unproved
reverse RAW descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The FULL real I_bc of ANY two E-occupancy supported reached
objects becomes the WHOLE gate identity of the ACTUAL selected
quotient groupoid after normalizing through their common reached
anchor a. All old intermediate witnesses remain in b and c. -/
theorem originalRetainedSelectedIdentityBridge_collapse
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
    (hbc : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val c.val) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let J := originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E
    let a := originalReachedOccupancyAnchorOf A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
    let hba := originalReachedOccupancyAnchorOf_supported A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
    let hca := J.trans (J.symm hbc) hba
    let Iab := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE a b (J.symm hba)
    let Ibc := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE b c hbc
    let Ica := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE c a hca
    (originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE a a)
      ((Iab.comp CB Ibc).comp CB Ica) =
    Arrow.id (originalRetainedSelectedKernel A B P transport tp
      hOne Kroot E hE a) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let a := originalReachedOccupancyAnchorOf A B P
    (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
  let hba : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
  let hca : J.r c.val a.val := J.trans (J.symm hbc) hba
  let Iab := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE a b (J.symm hba)
  let Ibc := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE b c hbc
  let Ica := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE c a hca
  let e := originalRetainedSelectedArrowEquiv A B P transport tp
    hOne Kroot E hE a a
  have hNormalize : (Iab.comp CB Ibc).comp CB Ica =
      Arrow.id (Reached.kernel B.homogeneous CB a) :=
    originalRetainedIdentity_normalized_at_anchor A B P transport tp
      hOne Kroot E hE a b c hba hca
  calc
    e ((Iab.comp CB Ibc).comp CB Ica) =
        e (Arrow.id (Reached.kernel B.homogeneous CB a)) :=
      congrArg e hNormalize
    _ = Arrow.id (originalRetainedSelectedKernel A B P transport tp
          hOne Kroot E hE a) :=
      originalRetainedSelectedArrow_id A B P transport tp
        hOne Kroot E hE a

end
end CCO.ExactEPGeometry
