import CCO.UnfilteredEP.OwnerHistoryCanonicalIso
import CCO.AutomaticEPCore.CodedTowerReceiving

/-! ANY supplied genuine clone-stable owner history receives into the
accepted B063 certified maximal-character history with explicit source
isomorphisms and the SAME fixed original code. Endpoint equivalence alone
is not used as a substitute for stepwise provenance. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z
namespace CCO.UnfilteredEP
open CloneTupleGeometry APCharacter APCharacter.Towers
open APCharacter.SourceAge RigidGroupoid.Geometry ExactEPGeometry AutomaticEPCore
noncomputable section

variable {A B D : OwnerStage.{u,v,w}} {Code : Type z}
variable (rootCode : Sigma (CloneSAP.Carrier A.Point) → Sigma (CloneSAP.Carrier A.Point) → Code)

/-- A genuine owner phase, followed by its actual canonicalizing
isomorphism, is exactly an accepted fixed-code maximal-character step. -/
theorem ownerCodedStep {B D : OwnerStage.{u,v,w}}
    (P : UnaryReduct A.source B.source) (step : OwnerStage.SafeStep B D) :
    CodedSafeSourceStep
      (codedSourceClass (ownerCodedCurrent B rootCode P))
      (codedSourceClass (ownerCodedCurrent D rootCode (P.compose step.reduct))) := by
  cases step with
  | @phase i K phase =>
    refine ⟨ownerCodedCurrent B rootCode P,i,K,phase,rfl,?_,?_⟩
    · exact (codedSourceClass_eq (ownerPhaseCanonicalCodedIso B phase rootCode P)).symm
    · exact actualPhaseRoot_maximalGate B.cloneCurrent K phase

/-- Receive every owner-phase edge, with arbitrary original reduct P,
not only an existentially chosen terminal tower. -/
theorem ownerCodedHistory (history : History OwnerStage.Next B D)
    (P : UnaryReduct A.source B.source) :
    Nonempty (History CodedSafeSourceStep
      (codedSourceClass (ownerCodedCurrent B rootCode P))
      (codedSourceClass
        (ownerCodedCurrent D rootCode (P.compose (OwnerStage.historyReduct history))))) := by
  induction history generalizing A with
  | nil B => exact ⟨.nil _⟩
  | @cons B C D step tail ih =>
    let actual := Classical.choice step
    obtain ⟨rest⟩ := ih rootCode (P.compose actual.reduct)
    have same :
        ownerCodedCurrent D rootCode
          ((P.compose actual.reduct).compose (OwnerStage.historyReduct tail)) =
        ownerCodedCurrent D rootCode
          (P.compose (OwnerStage.historyReduct (.cons step tail))) := rfl
    rw [same] at rest
    exact ⟨.cons (ownerCodedStep rootCode P actual) rest⟩

/-- The exact-prefix history is received from the SAME supplied owner
tower; its endpoint has a full source iso preserving all fixed old code. -/
theorem ownerHistoryExactPrefix (history : History OwnerStage.Next A D) :
    ∃ next : CertifiedGateTower.ExactPrefix A.cloneCurrent,
      Nonempty (History IsoGateTower.Step (CertifiedGateTower.initial A.cloneCurrent) next) ∧
      Nonempty (CodedCurrentSourceIso (codedExactPrefix rootCode next)
        (ownerCodedCurrent D rootCode (OwnerStage.historyReduct history))) := by
  obtain ⟨codeHistory⟩ := ownerCodedHistory rootCode history (UnaryReduct.identity A.source)
  have start : codedSourceClass
      (codedExactPrefix rootCode (CertifiedGateTower.initial A.cloneCurrent)) =
      codedSourceClass (ownerCodedCurrent A rootCode (UnaryReduct.identity A.source)) := rfl
  obtain ⟨next,received,same⟩ := coded_safe_history_exact_prefix_receiving
    A.cloneCurrent rootCode codeHistory (CertifiedGateTower.initial A.cloneCurrent) start
  refine ⟨next,received,?_⟩
  have last : ownerCodedCurrent D rootCode
      ((UnaryReduct.identity A.source).compose (OwnerStage.historyReduct history)) =
      ownerCodedCurrent D rootCode (OwnerStage.historyReduct history) := rfl
  rw [last] at same
  exact Quotient.exact same

end
end CCO.UnfilteredEP
