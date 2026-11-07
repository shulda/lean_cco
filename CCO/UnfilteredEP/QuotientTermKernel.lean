import CCO.UnfilteredEP.QuotientReturnTerms
import CCO.UnfilteredEP.FullLatticeKeys
import CCO.APRamseyReadout.CoordinateBridge
import CCO.HiddenSAPReadings.OrbitalNamedTerms

/-! C34-C35: compose a quotient-start term with its actual real
projection. Its kernel is a represented proper MI containing the input
kernel; the equality-kernel branch is excluded by genuine nonzeroness. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w r
namespace CCO.UnfilteredEP
open CCO.UnaryTermsReturn CCO.UnaryFreshFrames CCO.TypedOrbitFrames
open CCO.ParityHasse.Original CCO.HiddenSAPReadings CCO.TransitionClosure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "M" => originalCompletedStructure S H sap nr2
local notation "L" => originalCompletedLanguage S H sap nr2

theorem actual_projection_eq_iff {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) (x y : X i) :
    actualRealTerm S H sap nr2 (originalProjectionAsTerm S H sap nr2 D) x =
      actualRealTerm S H sap nr2 (originalProjectionAsTerm S H sap nr2 D) y ↔ D.val x y := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change (M).eval (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,x⟩) =
      (M).eval (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,y⟩) at hv
    rw [original_projection_as_term_eval,original_projection_as_term_eval] at hv
    exact Quotient.exact (original_completed_hidden_node_injective S H D hv)
  · intro h
    apply Subtype.ext
    change (M).eval (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,x⟩) =
      (M).eval (originalProjectionAsTerm S H sap nr2 D) (.inl ⟨i,y⟩)
    rw [original_projection_as_term_eval,original_projection_as_term_eval]
    exact congrArg (originalCompletedNamedHiddenNode S H D) (Quotient.sound h)

theorem actual_quotient_term_surjective {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inr D⟩⟩ s) : Function.Surjective ((M).typedEval term) := by
  intro y
  let projection := originalProjectionAsTerm S H sap nr2 D
  obtain ⟨x,hx⟩ := actualRealTerm_surjective S H sap nr2 (term.comp projection) y
  refine ⟨actualRealTerm S H sap nr2 projection x,?_⟩
  apply Subtype.ext
  simpa only [actualRealTerm,Structure.typedEval,Structure.eval_comp] using congrArg Subtype.val hx

theorem actual_quotient_term_injective_of_kernel {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inr D⟩⟩ s)
    (kernel : ∀ x y : X i,
      actualRealTerm S H sap nr2 (term.comp (originalProjectionAsTerm S H sap nr2 D)) x =
        actualRealTerm S H sap nr2 (term.comp (originalProjectionAsTerm S H sap nr2 D)) y ↔
          D.val x y) : Function.Injective ((M).typedEval term) := by
  intro q t hqt
  let projection := originalProjectionAsTerm S H sap nr2 D
  obtain ⟨x,hx⟩ := actualRealTerm_surjective S H sap nr2 projection q
  obtain ⟨y,hy⟩ := actualRealTerm_surjective S H sap nr2 projection t
  rw [← hx,← hy] at hqt
  have hcomp : actualRealTerm S H sap nr2 (term.comp projection) x =
      actualRealTerm S H sap nr2 (term.comp projection) y := by
    apply Subtype.ext
    simpa only [actualRealTerm,Structure.typedEval,Structure.eval_comp] using congrArg Subtype.val hqt
  have hD : D.val x y := (kernel x y).mp hcomp
  exact hx.symm.trans (((actual_projection_eq_iff S H sap nr2 D x y).mpr hD).trans hy)

theorem actual_quotient_term_named_kernel {i : ι}
    (D : OriginalNamedHiddenCoordinate S H i) {s : (L).Sorts}
    (term : Term L ⟨⟨i,.inr D⟩⟩ s) :
    ∃ E : OriginalNamedHiddenCoordinate S H i, D.val ≤ E.val ∧
      ∀ x y : X i,
        actualRealTerm S H sap nr2 (term.comp (originalProjectionAsTerm S H sap nr2 D)) x =
          actualRealTerm S H sap nr2 (term.comp (originalProjectionAsTerm S H sap nr2 D)) y ↔
            E.val x y := by
  letI : MulAction G ((M).Carrier s) := completedSortAction S H sap nr2 s
  let projection := originalProjectionAsTerm S H sap nr2 D
  let composite := term.comp projection
  let f := namedRealTermMap S H sap nr2 composite
  let equiv := namedRealTermMap_equivariant S H sap nr2 composite
  have hfactor : ∀ x y : X i, D.val x y → f x = f y := by
    intro x y hxy
    apply Subtype.ext
    change (M).eval composite (.inl ⟨i,x⟩) = (M).eval composite (.inl ⟨i,y⟩)
    dsimp only [composite,projection]
    rw [Structure.eval_comp,Structure.eval_comp,original_projection_as_term_eval,
      original_projection_as_term_eval]
    exact congrArg ((M).eval term)
      (congrArg (originalCompletedNamedHiddenNode S H D) (Quotient.sound hxy))
  rcases named_real_term_kernel_id_or_MI S H sap nr2 composite with hbot | ⟨E,hE⟩
  · have hle : D.val ≤ (⊥ : ColourEq S i) := by
      intro x y hxy
      have hk : equivariantKernel S H f equiv x y := hfactor x y hxy
      rw [hbot] at hk
      exact hk
    exact False.elim ((not_le_of_gt D.property.1) hle)
  · refine ⟨E,?_,?_⟩
    · intro x y hxy
      have hk : equivariantKernel S H f equiv x y := hfactor x y hxy
      rw [hE] at hk
      exact hk
    · intro x y
      change equivariantKernel S H f equiv x y ↔ E.val x y
      rw [hE]

section Clone
open CCO.APRamseyReadout CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- C34-C35/C57: a proper quotient term either transports the entire
J coordinate bijectively or factors through the unique FULL parent.
The latter equality holds on every parent pair in the actual source. -/
theorem actual_terminal_term_kernel_split {i : B.Sorts}
    (J : FullCloneProperMI B.source i) {s : (Lang B ht).Sorts}
    (term : Term (Lang B ht) (coordinateSort B ht (namedCoordinateHF B ht i J)) s) :
    (Function.Bijective ((Hidden B ht).typedEval term)) ∨
      (∀ x y : CloneSAP.Carrier B.Point i, fullMIParent B J x y →
        (Hidden B ht).eval term (coordinateNode B ht J (Quotient.mk J.val.val x)) =
          (Hidden B ht).eval term (coordinateNode B ht J (Quotient.mk J.val.val y))) := by
  let D := namedCoordinateHF B ht i J
  let nr := CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)
  obtain ⟨E,hJE,hkernel⟩ := actual_quotient_term_named_kernel
    (cloneSource B) (HF B) (cloneSAP B) nr D term
  by_cases he : E.val = J.val
  · left
    refine ⟨actual_quotient_term_injective_of_kernel
      (cloneSource B) (HF B) (cloneSAP B) nr D term ?_,
      actual_quotient_term_surjective (cloneSource B) (HF B) (cloneSAP B) nr D term⟩
    intro x y
    exact (hkernel x y).trans (by rw [he]; rfl)
  · right
    have hParent : fullMIParent B J ≤ E.val :=
      fullMIParent_le B J E.val (lt_of_le_of_ne hJE (Ne.symm he))
    intro x y hxy
    have heq := congrArg Subtype.val ((hkernel x y).mpr (hParent hxy))
    change (Hidden B ht).eval
        (term.comp (originalProjectionAsTerm (cloneSource B) (HF B) (cloneSAP B) nr D))
        (.inl ⟨i,x⟩) =
      (Hidden B ht).eval
        (term.comp (originalProjectionAsTerm (cloneSource B) (HF B) (cloneSAP B) nr D))
        (.inl ⟨i,y⟩) at heq
    rw [Structure.eval_comp,Structure.eval_comp] at heq
    have hx := original_projection_as_term_eval (cloneSource B) (HF B) (cloneSAP B) nr D x
    have hy := original_projection_as_term_eval (cloneSource B) (HF B) (cloneSAP B) nr D y
    change (Hidden B ht).eval (originalProjectionAsTerm (cloneSource B) (HF B)
      (cloneSAP B) nr D) (.inl ⟨i,x⟩) = coordinateNode B ht J (Quotient.mk J.val.val x) at hx
    change (Hidden B ht).eval (originalProjectionAsTerm (cloneSource B) (HF B)
      (cloneSAP B) nr D) (.inl ⟨i,y⟩) = coordinateNode B ht J (Quotient.mk J.val.val y) at hy
    exact (congrArg ((Hidden B ht).eval term) hx).symm.trans
      (heq.trans (congrArg ((Hidden B ht).eval term) hy))

theorem actual_terminal_quotient_term_split {i : B.Sorts}
    (J : FullCloneProperMI B.source i) {s : (Lang B ht).Sorts}
    (term : Term (Lang B ht) (coordinateSort B ht (namedCoordinateHF B ht i J)) s) :
    (Function.Bijective ((Hidden B ht).typedEval term)) ∨
      (∀ q t : Quotient J.val.val,
        CCO.TerminalLattice.originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
          (fullMIParent_cover B J).le q t →
        (Hidden B ht).eval term (coordinateNode B ht J q) =
          (Hidden B ht).eval term (coordinateNode B ht J t)) := by
  rcases actual_terminal_term_kernel_split B ht J term with hb | hc
  · exact Or.inl hb
  · right
    intro q t
    induction q using Quotient.inductionOn with | _ x =>
      induction t using Quotient.inductionOn with | _ y =>
        intro hp
        exact hc x y ((CCO.TerminalLattice.originalUpperSetoid_mk
          (cloneSource B) J.val (fullMIParent B J) (fullMIParent_cover B J).le x y).mp hp)

end Clone

end
end CCO.UnfilteredEP
