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

end
end CCO.UnfilteredEP
