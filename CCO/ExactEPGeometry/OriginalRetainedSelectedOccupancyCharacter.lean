import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowUnits

/-!
# B062 C84: FULL character on the ACTUAL occupancy-selected quotient groupoid

The earlier C84 step constructed the genuine connected groupoid with
one actual E-occupancy class of Reached objects per object, with ALL
selected-quotient full RAW-exact Arrow Hom sets between its canonical
Reached anchors. C83 supplies a BIJECTION on each entire source /
selected Hom set, not just a generating set.

The precise source-to-selected map preserves ALL compositions and
full gate identities, as separately proved from actual bisaturated
quotient images. Pulling the old FULL SourcePhase character back
through these complete Hom equivalences gives a GENUINE character
on the selected occupancy groupoid. No arbitrary quotient SAP,
automorphism group section, external character or unverified
normalization premise is supplied. The next consumer will identify
this character on normalized old full Arrows with the actual
object-corrected C79/C84 source phase.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- The ACTUAL selected occupancy quotient source's full
rigid-groupoid character. Every Hom is a whole source-constructed
projected exact Arrow between true selected kernels. The source
old character is transported by actual bijective C83 Hom maps
whose identity and composition laws have already been PROVED.
In particular it is not a character defined on selected generators. -/
noncomputable def originalRetainedSelectedOccupancyCharacter
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    Abstract.Character
      (OriginalReachedOccupancy A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E Kroot) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO
    Q.source Q.homogeneous Q.cco
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let anchor : Occ → Reached B.source Kroot :=
    originalReachedOccupancyAnchor A B P base hBase E Kroot
  let e := fun a b : Occ =>
    originalRetainedSelectedArrowEquiv A B P transport tp
      hOne Kroot E hE (anchor a) (anchor b)
  refine {
    value := fun {a b} R => phase.character.value ((e a b).symm R)
    map_id := ?_
    map_comp := ?_
  }
  · intro a
    let x := anchor a
    let ea := e a a
    let OldK := Reached.kernel B.homogeneous CB x
    let NewK := originalRetainedSelectedKernel A B P transport tp
      hOne Kroot E hE x
    have hid : ea (Arrow.id OldK) = Arrow.id NewK :=
      originalRetainedSelectedArrow_id A B P transport tp
        hOne Kroot E hE x
    have hinv : ea.symm (Arrow.id NewK) = Arrow.id OldK := by
      calc
        ea.symm (Arrow.id NewK) =
            ea.symm (ea (Arrow.id OldK)) :=
          congrArg ea.symm hid.symm
        _ = Arrow.id OldK := ea.symm_apply_apply _
    change phase.character.value (ea.symm (Arrow.id NewK)) = 0
    rw [hinv]
    exact phase.character.map_id x
  · intro a b c R U
    let x := anchor a
    let y := anchor b
    let z := anchor c
    let eab := e a b
    let ebc := e b c
    let eac := e a c
    let V := eab.symm R
    let W := ebc.symm U
    have hForward : eac (V.comp CB W) = R.comp CQ U := by
      calc
        eac (V.comp CB W) =
            (eab V).comp CQ (ebc W) :=
          originalRetainedSelectedArrow_comp A B P transport tp
            hOne Kroot E hE x y z V W
        _ = R.comp CQ U :=
          congrArg₂ (fun M N => M.comp CQ N)
            (eab.apply_symm_apply R) (ebc.apply_symm_apply U)
    have hBackward : eac.symm (R.comp CQ U) = V.comp CB W := by
      calc
        eac.symm (R.comp CQ U) =
            eac.symm (eac (V.comp CB W)) :=
          congrArg eac.symm hForward.symm
        _ = V.comp CB W := eac.symm_apply_apply _
    change phase.character.value (eac.symm (R.comp CQ U)) =
      phase.character.value V + phase.character.value W
    rw [hBackward]
    exact phase.character.map_comp V W

end
end CCO.ExactEPGeometry
