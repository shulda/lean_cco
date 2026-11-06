import CCO.ExactEPGeometry.OriginalCurrentExactColourInvariance
import CCO.APCharacter.SourceAge.SingleStep

/-! B062 C96: the genuine marked limit identifies with the ACTUAL
SingleStep successor. This is the constructed back-and-forth
identification, not an assumed quotient action or section. -/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- Literal actual successor encoding of the already constructed
marked homogeneous limit, with all real successor child types. -/
noncomputable def originalPhaseMarkedToActual
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot) :
    phase.MarkedLimit B.cco ≃
      Sigma (SingleStep.successor B phase).Point :=
  (UnarySource.newEquiv (SingleStep.identification B phase)).symm

/-- The genuine next-source reduct of a marked-limit point is its
TRUE old-reduct preimage. No independently chosen old witness. -/
theorem originalPhaseMarkedToActual_projection
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (p : phase.MarkedLimit B.cco) :
    (SingleStep.projection B phase).project
      (originalPhaseMarkedToActual B Kroot phase p) =
      (SingleStep.identification B phase).equiv.symm p := by
  let I := SingleStep.identification B phase
  change (UnarySource.oldEquiv I)
    ((UnarySource.oldEquiv I).symm (I.equiv.symm p)) =
      I.equiv.symm p
  exact (UnarySource.oldEquiv I).apply_symm_apply _


/-- Every actual successor point pair has the SAME complete fine
old-current orbital code as its marked-limit counterpart. This
includes the genuine old diagonal and all mixed named sorts.
The comparison uses the actual back-and-forth identification. -/
theorem originalPhaseMarkedToActual_colours
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (p q : phase.MarkedLimit B.cco) :
    (phase.markedCoding B.cco).table.colour p q =
      Age.colourEquiv B.source
        (taggedColour B.source
          ((SingleStep.projection B phase).project
            (originalPhaseMarkedToActual B Kroot phase p))
          ((SingleStep.projection B phase).project
            (originalPhaseMarkedToActual B Kroot phase q))) := by
  let I := SingleStep.identification B phase
  rw [originalPhaseMarkedToActual_projection B Kroot phase p,
      originalPhaseMarkedToActual_projection B Kroot phase q]
  have h := UnarySource.colour_eq I (I.equiv.symm p) (I.equiv.symm q)
  change (phase.markedCoding B.cco).table.colour
      (I.equiv (I.equiv.symm p)) (I.equiv (I.equiv.symm q)) =
    Age.colourEquiv B.source
      (taggedColour B.source (I.equiv.symm p) (I.equiv.symm q))
    at h
  rw [I.equiv.apply_symm_apply,I.equiv.apply_symm_apply] at h
  exact h

end
end CCO.ExactEPGeometry
