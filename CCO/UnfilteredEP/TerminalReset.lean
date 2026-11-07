import CCO.UnfilteredEP.FullLatticeKeys
import CCO.TerminalLattice.OriginalTerminalReset

/-! The actual terminal source supplies ONE COMPLETE reset menu and its
two different squares. No hidden SAP, normalized order, Ramsey arrow or
expansion property is a premise of this source calculation. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

include ht in
/-- C50-C51: instantiate the genuine FULL terminal relative-reset proof.
The menu is a complete quotient orbital and may contain many fine atoms.
The first square is diversity STRONG; the second includes real equality. -/
theorem actual_terminal_reset {i : B.Sorts} (J : FullCloneProperMI B.source i) :
    ∃ p z : CloneSAP.Carrier B.Point i,
      fullMIParent B J p z ∧ ¬ J.val p z ∧
      ((cloneSource B).product
        (originalQuotientOrbitalPalette (cloneSource B) (G := CCO.TerminalPowers.FullAut (cloneSource B)) J.val p z)
        (originalQuotientOrbitalPalette (cloneSource B) (G := CCO.TerminalPowers.FullAut (cloneSource B)) J.val p z) =
          originalEquivDiversityPalette (cloneSource B) (fullMIParent B J)) ∧
      (RawSymmetric.compose
        ((cloneSource B).menuRel
          (originalQuotientOrbitalPalette (cloneSource B) (G := CCO.TerminalPowers.FullAut (cloneSource B)) J.val p z))
        ((cloneSource B).menuRel
          (originalQuotientOrbitalPalette (cloneSource B) (G := CCO.TerminalPowers.FullAut (cloneSource B)) J.val p z)) =
          (fullMIParent B J).val.r) := by
  let S := cloneSource B
  let H := cloneHomogeneous B
  let K := fullMIParent B J
  have hJK : J.val ⋖ K := fullMIParent_cover B J
  have hJ : (⊥ : ColourEq S i) < J.val := bot_lt_iff_ne_bot.mpr J.property.1
  obtain ⟨wJ,hwJ⟩ := original_terminal_nonzero_positive_word
    S H (cloneSAP B) (B.terminal_sortNR2 ht i) J.val hJ
  obtain ⟨wK,hwK⟩ := original_terminal_nonzero_positive_word
    S H (cloneSAP B) (B.terminal_sortNR2 ht i) K (hJ.trans hJK.lt)
  obtain ⟨anchor⟩ := S.nonemptySort i
  exact original_full_cover_reset_single_path S H (cloneSAP B) (cloneCCO B)
    J.val K hJK hJ anchor
    (B.terminal_sortNR2 ht i J.val K hJK.le anchor) wJ hwJ wK hwK

end
end CCO.UnfilteredEP
