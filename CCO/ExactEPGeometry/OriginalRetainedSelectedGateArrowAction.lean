import CCO.ExactEPGeometry.OriginalRetainedSelectedGateClasses
import CCO.ExactEPGeometry.OriginalAllparentGateArrowAction

/-!
# B062 C83/C93: REAL selected K/E gate-class action is the old K action

C83 gave the exact Hom-equivalence of all original reached arrows and
their fully projected and selected E-quotient arrows. The point-class
equivalences from the actual C82 full gate and C66 genuine one-parent
E-occupancy carrier bijections are NOW SHOWN equivariant for ALL
these whole arrows, not a generating collection.

Proof composition uses the accepted all-parent endpoint image map
and the source-verified selected-sort retyping, with actual full
Arrow relations and source homogeneity at each stage. This is the
point-action compatibility required for C93/C94 selected-to-original
marking pullback. Normalizing duplicated old Reached objects to their
ONE E-occupancy anchor remains separately necessary. No quotient SAP,
group section or arbitrary reverse mixed RAW exact descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every ACTUAL original reached full Arrow R:b->c is natural on
the genuine equivalences of its old K-class carriers with the
selected occupancy quotient K/E-class carriers. -/
theorem originalRetainedSelectedGateClass_arrow_natural
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
          B.source B.homogeneous B.cco) c)) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E
    ∀ x : (Reached.kernel B.homogeneous CB b).Class,
      originalRetainedSelectedGateClassEquiv
          A B P transport tp hOne Kroot E hE c
          (R.quotientMap B.homogeneous x) =
        ((originalRetainedSelectedArrowEquiv
          A B P transport tp hOne Kroot E hE b c) R).quotientMap
          Q.homogeneous
          (originalRetainedSelectedGateClassEquiv
            A B P transport tp hOne Kroot E hE b x) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Qall : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource
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
  let Kc := Reached.kernel B.homogeneous CB c
  let hb := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let hc := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE c
  let KbQ := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val Kb hb
  let KcQ := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E c.val Kc hc
  let Uall : Arrow Qall.source KbQ KcQ :=
    (originalCoherentAllparentArrowEquiv
      A B P transport tp base hBase E Kb Kc hb hc) R
  change ∀ x : Kb.Class,
    D.gateClassMap Qall.homogeneous KcQ
        ((originalAllparentGateClassEquiv
          A B P transport tp base hBase E c.val Kc hc)
          (R.quotientMap B.homogeneous x)) =
      (D.transportArrow Qall.homogeneous Uall).quotientMap
        (selectedSortHomogeneous Qall.source sigma Qall.homogeneous)
        (D.gateClassMap Qall.homogeneous KbQ
          ((originalAllparentGateClassEquiv
            A B P transport tp base hBase E b.val Kb hb) x))
  intro x
  have hAll := originalAllparentGateClass_arrow_natural
    A B P transport tp base hBase E Kb Kc hb hc R x
  have hRetag := D.gateClassMap_arrow_natural Qall.homogeneous
    Uall ((originalAllparentGateClassEquiv
      A B P transport tp base hBase E b.val Kb hb) x)
  change D.gateClassMap Qall.homogeneous KcQ
      ((originalAllparentGateClassEquiv
        A B P transport tp base hBase E c.val Kc hc)
        (R.quotientMap B.homogeneous x)) =
    (D.transportArrow Qall.homogeneous Uall).quotientMap
      (selectedSortHomogeneous Qall.source sigma Qall.homogeneous)
      (D.gateClassMap Qall.homogeneous KbQ
        ((originalAllparentGateClassEquiv
          A B P transport tp base hBase E b.val Kb hb) x))
  rw [hAll]
  exact hRetag

end
end CCO.ExactEPGeometry
