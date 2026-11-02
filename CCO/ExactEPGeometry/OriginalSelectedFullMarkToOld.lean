import CCO.ExactEPGeometry.OriginalReachedSelectedActionNaturality
import CCO.ExactEPGeometry.SelectedMarkingPullback
import CCO.APCharacter.ActualMasks

/-!
# B062 C93: every FULL selected E-quotient marking lifts to a legal original mark

For one genuine AP-only maximal-character source step, original full
exact E≤G and the already proved actual C82/C83 full selected
E-occupancy quotient groupoid, the C84 selected corrected character
has an actual point-action representation on true K/E classes.

The source-verified normalization via original whole G-identity
bridges and actual full Hom correspondence yields an arrow-natural
bijection from every old reached K-class to its canonical selected
E-occupancy K/E-class. The C84 corrected character equation then
allows a full selected-groupoid marking to pull back to an old
Reached-groupoid marking with original phase. The existing AP-only
SourcePhase provider gives a globally legal marking on the ENTIRE
genuine old source. On reached old points its bits are precisely
selected marked K/E-class bit plus the actual original object
correction gamma_b; all inactive original sorts get their forced bit.

No hypothetical source marking, quotient SAP, extra group-section,
mixed reverse RAW exactness or selected generating family occurs.

This is global-mark transfer on existing actual prefix points.
C89's realization of EVERY allowed unmarked quotient prefix and
C94–C96's complete finite-age transfer/recovery remain separate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- Every globally compatible FULL selected quotient character marking
produces an ACTUAL old global SourcePhase mask, with exact C79/C84
offset readout on EVERY original reached old point. The selected
marking is not assumed to be an original source marking. -/
theorem originalSelectedFullMarkToOldSource
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
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    letI := Reached.groupoid B.homogeneous CB (A := Kroot)
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let FS := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chiS := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    let gamma := originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
    ∀ (selectedMark : Abstract.Point FS → ZMod 2),
      Abstract.IsMarking FS chiS selectedMark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (b : Reached B.source Kroot) (x : B.Point b.val),
            oldMark ⟨b.val,x⟩ =
              selectedMark ⟨
                (Quotient.mk'' b : OriginalReachedOccupancy
                  A B P (P.parent r)
                    (fun k => hOne (P.parent r) k) E Kroot),
                originalReachedSelectedActionPoint
                  A B P transport tp hOne Kroot E hE b
                    ((Reached.kernel B.homogeneous CB b).project x)⟩ +
              gamma b := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let FO := Reached.pointFunctor B.homogeneous CB Kroot
  let FS := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chiS := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  let gamma := originalReachedGlobalOffset
    A B P transport tp hOne Kroot phase E hE
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot
  let owner : Reached B.source Kroot → Occ := fun b => Quotient.mk'' b
  let mapArrow : ∀ {a b : Reached B.source Kroot},
      (a ⟶ b) → (owner a ⟶ owner b) :=
    fun {a b} R => originalReachedSelectedActionArrow
      A B P transport tp hOne Kroot E hE a b R
  let mapPoint : ∀ b : Reached B.source Kroot, FO.obj b → FS.obj (owner b) :=
    fun b => originalReachedSelectedActionPoint
      A B P transport tp hOne Kroot E hE b
  have hNatural : ∀ {a b : Reached B.source Kroot}
      (R : a ⟶ b) (q : FO.obj a),
      mapPoint b (FO.map R q) = FS.map (mapArrow R) (mapPoint a q) := by
    intro a b R q
    exact originalReachedSelectedAction_natural
      A B P transport tp hOne Kroot E hE a b R q
  have hCharacter : ∀ {a b : Reached B.source Kroot} (R : a ⟶ b),
      chiS.value (mapArrow R) =
        gamma a + phase.character.value R + gamma b := by
    intro a b R
    exact originalReachedSelectedActionArrow_character
      A B P transport tp hOne Kroot phase E hE a b R
  change ∀ (selectedMark : Abstract.Point FS → ZMod 2),
      Abstract.IsMarking FS chiS selectedMark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (b : Reached B.source Kroot) (x : B.Point b.val),
            oldMark ⟨b.val,x⟩ =
              selectedMark ⟨owner b,mapPoint b
                ((Reached.kernel B.homogeneous CB b).project x)⟩ + gamma b
  intro selectedMark hSelected
  let groupMark : Abstract.Point FO → ZMod 2 :=
    fun p => selectedMark ⟨owner p.1,mapPoint p.1 p.2⟩ + gamma p.1
  have hGroup : Abstract.IsMarking FO phase.character groupMark :=
    selectedMarkingPullback FO FS phase.character chiS
      owner mapArrow mapPoint gamma hNatural hCharacter
      selectedMark hSelected
  let oldMark := originalMarking B.source B.homogeneous CB Kroot groupMark
  refine ⟨oldMark,phase.original_global_marking groupMark hGroup,?_⟩
  intro b x
  rw [originalMarking_reached B.source B.homogeneous CB Kroot
    groupMark b x]
  rfl

end
end CCO.ExactEPGeometry
