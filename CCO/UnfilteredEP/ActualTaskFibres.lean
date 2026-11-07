import CCO.UnfilteredEP.TaskFormula
import CCO.UnfilteredEP.TaskPrefixLanguage
import CCO.UnfilteredEP.RootCoverage
import CCO.ResetOrder.ResetSetting

/-! The actual old-language fibres for one representative task. The
allowed old class retains every proper hidden vertex and every existing
partial unary function. All-map naturality is literal formula naturality. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)

abbrev TaskOldSignature := resetUnarySignature (PrefixFullCodeLanguage B ht n)

abbrev taskOldBase (A : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)) :=
  prefixBase B ht (resetUnaryDecode (PrefixFullCodeLanguage B ht n) A.data)

abbrev taskOldRaw (A : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)) :=
  TerminalHiddenHN.binaryDecode (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) (taskOldBase B ht n A)

theorem taskOldBase_eq (A : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)) :
    CoordinateModel B ht (taskOldRaw B ht n A) = taskOldBase B ht n A :=
  TerminalHiddenHN.binaryStructure_binaryDecode _ _ _

def taskOldBaseEmbedding
    {A D : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)}
    (e : A.Emb D) : Structure.Embedding (taskOldBase B ht n A) (taskOldBase B ht n D) :=
  (resetUnaryDecodeEmbedding (PrefixFullCodeLanguage B ht n) e).reduct
    (prefixBaseReduct B ht n)

def taskOldRawEmbedding
    {A D : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)}
    (e : A.Emb D) : (taskOldRaw B ht n A).Embedding (taskOldRaw B ht n D) :=
  TerminalHiddenHN.binaryDecodeEmbedding _ _ (taskOldBaseEmbedding B ht n e)

def actualTaskAllowed (A : ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n)) : Prop :=
  ProperFiniteCodeAge B ht ⟨A.Carrier,taskOldBase B ht n A,A.finite⟩

theorem actualTaskAllowed_hereditary : ResetOrder.Unary.Hereditary (actualTaskAllowed B ht n) := by
  intro A D hD he
  obtain ⟨e⟩ := he
  refine ⟨TerminalHiddenHN.actualAge_hereditary_mixed _ _ _ _ hD.1
    (taskOldRawEmbedding B ht n e),?_⟩
  intro x
  rw [← (taskOldBaseEmbedding B ht n e).sort_eq x]
  exact hD.2 (e.point x)

/-- The complete parent keys and the existing complete reset cylinder
are both read in the retained old-language reduct. -/
def actualTaskFibres (D : HiddenCut B)
    (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2)) :
    ResetOrder.Unary.Fibres.{max u v w,max u v} (TaskOldSignature B ht n) where
  Allowed := actualTaskAllowed B ht n
  hereditary := actualTaskAllowed_hereditary B ht n
  same A := (actualParentFormula B ht D).same (taskOldBase B ht n A)
  reset A := (actualCutFormula B ht D m).reset (taskOldBase B ht n A)
  same_symm A _ _ _ h := (actualParentFormula B ht D).same_symm _ h
  same_trans A _ _ _ _ h h' := (actualParentFormula B ht D).same_trans _ h h'
  same_natural e x y := (actualParentFormula B ht D).same_natural
    (taskOldBaseEmbedding B ht n e) x y
  reset_natural e x y := (actualCutFormula B ht D m).reset_natural
    (taskOldBaseEmbedding B ht n e) x y
  reset_symm A hA x y h := by
    obtain ⟨e⟩ := hA.1.2
    have h' : (actualCutFormula B ht D m).reset
        (CoordinateModel B ht (taskOldRaw B ht n A)) x y :=
      (taskOldBase_eq B ht n A).symm ▸ h
    have hr := actualCutFormula_reset_symmetric B ht (taskOldRaw B ht n A) e D m x y h'
    exact (taskOldBase_eq B ht n A) ▸ hr
  reset_ne A hA x y h := by
    obtain ⟨e⟩ := hA.1.2
    exact actualCutFormula_reset_ne B ht (taskOldRaw B ht n A) e D m x y
      ((taskOldBase_eq B ht n A).symm ▸ h)
  reset_same A hA x y h := by
    obtain ⟨e⟩ := hA.1.2
    have hr := actualCutFormula_reset_same B ht (taskOldRaw B ht n A) hA.1 e D m x y
      ((taskOldBase_eq B ht n A).symm ▸ h)
    exact (taskOldBase_eq B ht n A) ▸ hr

end
end CCO.UnfilteredEP
