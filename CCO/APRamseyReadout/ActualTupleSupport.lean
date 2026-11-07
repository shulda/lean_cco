import CCO.APRamseyReadout.TupleSupport
import CCO.APRamseyReadout.OwnerCodeAction
import CCO.TerminalHiddenHN.NormalForms

/-! Every structural field of the multi-coordinate support interpretation
is discharged on the SAME actual terminal clone source and fixed chart.
In particular no map-extension, finite-closure or Ramsey callback remains. -/

universe u v w p
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.TerminalPowers
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- The actual marked tuple interpretation, uniform in the arbitrary
fixed distinct meet-K chart. No original-F-MI specialization is used. -/
def actualTupleInterpretation :
    TupleInterpretation (G := FullAut B.source) B.source
      (CoordinateTarget B ht) (tupleScheme B ht F) where
  normal := TerminalHiddenHN.binaryNormalForms (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht)
  valid := TerminalHiddenHN.binaryNormalForms_valid (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht)
  eta := ownerRoot B ht F
  eta_injective := ownerRoot_injective B ht F
  motion := ownerCoordinateMotion B ht
  eta_equivariant := ownerRoot_equivariant B ht F

/-- Actual finite support, retaining every marked coordinate and every
normal term value rather than only a displayed list of original roots. -/
abbrev actualTupleSupport (A : CCO.FiniteInduced (X := B.Point)) :=
  (actualTupleInterpretation B ht F).support A

theorem actualTupleSupport_finite (A : CCO.FiniteInduced (X := B.Point)) :
    (actualTupleSupport B ht F A).Finite :=
  (actualTupleInterpretation B ht F).support_finite A

end
end CCO.APRamseyReadout
