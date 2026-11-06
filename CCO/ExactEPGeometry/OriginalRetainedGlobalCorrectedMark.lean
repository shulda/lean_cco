import CCO.ExactEPGeometry.OriginalRetainedOccupancyChildEquiv
import CCO.ExactEPGeometry.OriginalRetainedAnyMarkCorrection
import CCO.ExactEPGeometry.OriginalSelectedGlobalEClassEquiv
import CCO.ExactEPGeometry.OriginalSelectedGlobalClassReadout
import CCO.ExactEPGeometry.OriginalPhaseSelectedPointEquiv

/-!
# B062 C96/C103: the real corrected old marking descends globally

The canonical original character marking is corrected on every actual
reached parent by its whole identity-arrow offset, and is zero on inactive
parents. Its value is constant on the ENTIRE global original E-class.
Literal quotient descent therefore gives a genuine selected point marking;
there is no chosen quotient action section or extra marking provider.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- The actual canonical old mark with its true original full-arrow
correction on every old named parent. -/
def originalRetainedCorrectedMark (p : Sigma B.Point) : Bit :=
  UnarySource.mark (SingleStep.identification B phase) p +
    originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE p.1

/-- Chosen reached anchors have precisely zero normalization offset. -/
theorem originalRetainedNamedOffset_anchor_zero
    (c : OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot) :
    originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE
      (originalReachedOccupancyAnchor A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E Kroot c).val = 0 := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  rw [originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE (anchor c)]
  change originalRetainedAnchorOffset A B P transport tp hOne Kroot phase E hE
    (anchor (Quotient.mk'' (anchor c))) (anchor c) = 0
  rw [originalReachedOccupancyAnchor_class A B P base hBase E Kroot c]
  exact originalRetainedAnchorOffset_anchor_zero A B P transport tp hOne Kroot phase E hE (anchor c)

/-- Any two points of one actual global original E-class have equal
corrected marks, including points in different old parents. -/
theorem originalRetainedCorrectedMark_globalE
    (p q : Sigma B.Point)
    (hpq : (currentOriginalExactSetoid A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E).r p q) :
    originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE p =
      originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE q := by
  classical
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let J := originalExactOccupancySetoid A B P base hBase E
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let mark := UnarySource.mark (SingleStep.identification B phase)
  have hMark : phase.masks.GlobalMarking mark := UnarySource.global_marking _
  have hSupp : J.r p.1 q.1 := ⟨p.2,q.2,hpq⟩
  by_cases hp : Nonempty (Bridge B.source Kroot p.1)
  · have hq := (original_retained_occupancy_active_iff A B P transport tp hOne
      Kroot E hE p.1 q.1 hSupp).mp hp
    let b : Reached B.source Kroot := ⟨p.1,hp⟩
    let d : Reached B.source Kroot := ⟨q.1,hq⟩
    let anchor := originalReachedOccupancyAnchorOf A B P base hBase E Kroot
    let a := anchor b
    have hba : J.r b.val a.val :=
      originalReachedOccupancyAnchorOf_supported A B P base hBase E Kroot b
    have hda : J.r d.val a.val := J.trans (J.symm hSupp) hba
    have hAnchor : anchor b = anchor d :=
      originalReachedOccupancyAnchorOf_eq A B P base hBase E Kroot b d hSupp
    have gb : originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE b.val =
        phase.character.value (original_retained_identity_arrow A B P transport tp hOne
          Kroot E hE b a hba) := by
      rw [originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE b]
      exact originalRetainedAnchorOffset_supported A B P transport tp hOne Kroot phase E hE a b hba
    have gd : originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE d.val =
        phase.character.value (original_retained_identity_arrow A B P transport tp hOne
          Kroot E hE d a hda) := by
      rw [originalRetainedNamedOffset_active A B P transport tp hOne Kroot phase E hE d]
      change originalRetainedAnchorOffset A B P transport tp hOne Kroot phase E hE
        (anchor d) d = _
      rw [← hAnchor]
      exact originalRetainedAnchorOffset_supported A B P transport tp hOne Kroot phase E hE a d hda
    change mark p + _ = mark q + _
    rw [gb,gd]
    exact originalRetainedAnyMarkCorrectedInvariant A B P transport tp hOne Kroot phase E hE
      mark hMark a b d hba hda p.2 q.2 hpq
  · have hq : ¬Nonempty (Bridge B.source Kroot q.1) := by
      intro h
      exact hp ((original_retained_occupancy_active_iff A B P transport tp hOne
        Kroot E hE p.1 q.1 hSupp).mpr h)
    change mark p + _ = mark q + _
    rw [hMark.1 p hp,hMark.1 q hq,
      originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE p.1 hp,
      originalRetainedNamedOffset_inactive A B P transport tp hOne Kroot phase E hE q.1 hq]

/-- Literal descent through the entire actual original E-class quotient,
then the proved equivalence with the actual selected quotient source. -/
def originalRetainedSelectedCorrectedMark :
    Sigma (originalExactSelectedQuotientCurrentSource A B P transport
      (P.parent r) (fun i => hOne (P.parent r) i) E).Point → Bit :=
  fun q => Quotient.lift
    (originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE)
    (originalRetainedCorrectedMark_globalE A B P transport tp hOne Kroot phase E hE)
    (originalSelectedGlobalEClassEquiv A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E q)

/-- Every old point reads back its exact corrected bit after true
selected original-E projection, with no representative choice. -/
theorem originalRetainedSelectedCorrectedMark_project (p : Sigma B.Point) :
    originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE
      (originalCurrentToSelectedPoint A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E p) =
    originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE p := by
  unfold originalRetainedSelectedCorrectedMark
  change Quotient.lift _ _
    (Quotient.mk'' (originalSelectedTaggedRepresentative A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E (originalCurrentToSelectedPoint A B P transport
        (P.parent r) (fun i => hOne (P.parent r) i) E p))) = _
  rw [originalCurrentToSelectedPoint_globalE A B P transport (P.parent r)
    (fun i => hOne (P.parent r) i) E p]
  rfl

/-- The actual point bijection through original E-classes reproduces the
precise corrected actual child-name bit on EVERY successor quotient point. -/
theorem originalRetainedSelectedCorrectedMark_child :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
    ∀ q : Sigma QN.Point,
      originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE (f q) =
        (e q.1).2.val := by
  dsimp only
  intro q
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  have hEpair := originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hBase E q
  have hc := originalRetainedCorrectedMark_globalE A B P transport tp hOne Kroot phase E hE
    (repB (f q)) (R.project (repN q)) hEpair
  change originalRetainedCorrectedMark A B P transport tp hOne Kroot phase E hE (repB (f q)) = _
  rw [hc]
  have hName : e q.1 = originalRetainedChildToSelectedChild A B P transport tp hOne Kroot phase E hE (repN q).1 := by
    have h := originalOccupancyRepresentative_class A N (P.compose R) base hBase E q.1
    exact (congrArg e h).symm
  rw [hName]
  change UnarySource.mark (SingleStep.identification B phase) (R.project (repN q)) + _ =
    (repN q).1.2.val + _
  have ht := congrArg Subtype.val (repN q).2.property
  change UnarySource.mark (SingleStep.identification B phase) (R.project (repN q)) = (repN q).1.2.val at ht
  exact congrArg (fun z => z + originalRetainedNamedOffset A B P transport tp hOne Kroot phase E hE (repN q).1.1) ht

end
end CCO.ExactEPGeometry
