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

end
end CCO.ExactEPGeometry
