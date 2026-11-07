import CCO.AutomaticEPCore.OriginalTypes
import CCO.AutomaticEPCore.QuotientRank
import CCO.ExactEPGeometry.CertifiedFinalKernelSupport
import CCO.ExactEPGeometry.CertifiedMeetTower
import CCO.ExactEPGeometry.FullExactSupport
import CCO.ExactEPGeometry.OriginalQuotientTower

/-! The nonidentity-gate branch starts with an ACTUAL selected original
gate separating the prescribed final names. Its quotient has the proved
strict ORIGINAL rank drop and the SAME aligned full-age safe tower.
This does not assume that this quotient already has a separator. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.RigidGroupoid.Geometry
open Classical
noncomputable section

/-- Original uniqueness transports genuine full-exact words across the
two original sort tags. Current sort names are never identified. -/
theorem original_global_exact_full
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (i j : A.Sorts) :
    FullExact A.source (fun (x : A.Point i) (y : A.Point j) =>
      originalExactGlobalRelation A base hOne E ⟨i,x⟩ ⟨j,y⟩) := by
  cases hOne i
  cases hOne j
  exact E.property

/-- C29: finite meet support applies because all true equivalences
share the old diagonal, including the empty-history case. The chosen
gate comes from the SAME actual history, not an assumed separator. -/
theorem distinct_final_types_have_separating_gate
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal)
    (s t : terminal.current.Sorts) (hne : s ≠ t) :
    ∃ E ∈ certifiedHistoryOriginalGates A base hOne history,
      ¬prefixSupport terminal.reduct
        (originalExactGlobalRelation A base hOne E) s t := by
  classical
  let L := certifiedHistoryOriginalGates A base hOne history
  let P := terminal.reduct
  let R (f : Fin L.length) :
      TRel A.Point (P.parent s) (P.parent t) :=
    fun x y => originalExactGlobalRelation A base hOne (L.get f)
      ⟨P.parent s,x⟩ ⟨P.parent t,y⟩
  have exacts (f : Fin L.length) : FullExact A.source (R f) :=
    original_global_exact_full A base hOne (L.get f) (P.parent s) (P.parent t)
  have oldNonempty : ∃ x : A.Point (P.parent s),
      ∃ y : A.Point (P.parent t), ∀ f, R f x y := by
    obtain ⟨x⟩ := A.source.nonemptySort base
    refine ⟨hOne (P.parent s) ▸ x,hOne (P.parent t) ▸ x,?_⟩
    intro f
    change (L.get f)
      ((hOne (P.parent s)).symm ▸ (hOne (P.parent s) ▸ x))
      ((hOne (P.parent t)).symm ▸ (hOne (P.parent t) ▸ x))
    have hs : (hOne (P.parent s)).symm ▸ (hOne (P.parent s) ▸ x) = x := by
      cases hOne (P.parent s)
      rfl
    have ht : (hOne (P.parent t)).symm ▸ (hOne (P.parent t) ▸ x) = x := by
      cases hOne (P.parent t)
      rfl
    rw [hs,ht]
  by_contra notExists
  have each : ∀ E ∈ L,
      prefixSupport P (originalExactGlobalRelation A base hOne E) s t := by
    intro E hE
    by_contra hNo
    exact notExists ⟨E,hE,hNo⟩
  have hMeet := CertifiedGateTower.history_meet_support history
    (ExactMeetSupport.identity A.source)
  obtain ⟨x,y,all⟩ := (fullExact_family_support_iff P hMeet R exacts oldNonempty).mpr
    (fun f => each (L.get f) (List.get_mem L f))
  apply hne
  apply (certifiedHistoryCommonOriginalKernel_support_identity
    A base hOne history s t).mp
  refine ⟨x,y,?_⟩
  apply (certifiedHistoryCommonOriginalKernel_iff A base hOne history _ _).mpr
  intro E hE
  obtain ⟨f,hf⟩ := List.mem_iff_get.mp hE
  rw [← hf]
  exact all f

/-- C29–C31 receiving data. If every selected original gate is positive,
distinct final types give a positive separating E with the actual smaller
original quotient rank and its fully constructed, phase-aligned safe tower.
No induction conclusion or quotient source provider is an input. -/
theorem positive_separating_gate_with_aligned_quotient
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal)
    (positive : ∀ E ∈ certifiedHistoryOriginalGates A base hOne history,
      E ≠ (⊥ : ExactEq A.source base))
    (s t : terminal.current.Sorts) (hne : s ≠ t) :
    ∃ E ∈ certifiedHistoryOriginalGates A base hOne history,
      (⊥ : ExactEq A.source base) < E ∧
      ¬prefixSupport terminal.reduct
        (originalExactGlobalRelation A base hOne E) s t ∧
      Nat.card ((CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
        (originalExactSourceKernelFamily A base hOne E)
        (originalExactSourceKernelWords A base hOne E)
        (originalExactSourceKernelWords_relation A base hOne E)).Atom base base) <
          originalDiversityRank A base ∧
      ∃ trace : QuotientHistoryProvenance.Alignment A base hOne E history,
        trace.indices = QuotientHistoryProvenance.retainedIndices A base hOne E history ∧
        trace.gates = (certifiedHistoryOriginalGates A base hOne history).filter
          (fun G => decide (E ≤ G)) ∧
        (FullInvariantCoverInfinite terminal.current →
          (quotient A base hOne E terminal).Terminal) := by
  classical
  obtain ⟨E,hE,separates⟩ :=
    distinct_final_types_have_separating_gate A base hOne history s t hne
  have hPositive : (⊥ : ExactEq A.source base) < E :=
    bot_lt_iff_ne_bot.mpr (positive E hE)
  obtain ⟨trace,hIndices,hGates,_,_,hTerminal⟩ :=
    originalExactQuotientSafeTower_aligned A base hOne E history
  exact ⟨E,hE,hPositive,separates,
    original_exact_quotient_rank_lt A base hOne E hPositive,
    trace,hIndices,hGates,hTerminal⟩

end
end CCO.AutomaticEPCore
