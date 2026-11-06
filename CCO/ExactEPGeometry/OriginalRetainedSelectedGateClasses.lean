import CCO.ExactEPGeometry.OriginalAllparentGateClasses
import CCO.ExactEPGeometry.SelectedGateClassTransport
import CCO.ExactEPGeometry.OriginalRetainedSelectedGroupoid

/-!
# B062 C83/C86/C93: REAL selected K/E classes equal original K classes

The C67/C82 simultaneous typed quotient and the proven
one-per-E-occupancy class transports form an actual chain:

  (old current K_b classes)
    ≃ (all-parent K_b/E_b classes)
    ≃ (selected occupancy K_b/E_b classes).

Both equivalences are induced by genuine underlying point maps and
their WHOLE full-exact gate kernels. No new group action, quotient
SAP, group section, or arbitrary reverse RAW descent is assumed.

The composition remains objectwise at each genuine Reached old
parent; identifying E-occupancy duplicate groupoid objects and
transporting entire source Arrows is the following C84/C93 step.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Real, bijective old-to-selected full gate-class map for EVERY
reached source parent b. The genuine C82 projected kernel
exactness and C66 selected occupancy equivalence are consumed
on this same original E and source. -/
noncomputable def originalRetainedSelectedGateClassEquiv
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
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    (Reached.kernel B.homogeneous CB b).Class ≃
      (originalRetainedSelectedKernel
        A B P transport tp hOne Kroot E hE b).Class := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
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
  let Kb := Reached.kernel B.homogeneous CB b
  let hb := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let KbQ := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val Kb hb
  change Kb.Class ≃ (D.transportKernel Qall.homogeneous KbQ).Class
  exact (originalAllparentGateClassEquiv
    A B P transport tp base hBase E b.val Kb hb).trans
      (D.gateClassEquiv Qall.homogeneous KbQ)

end
end CCO.ExactEPGeometry
