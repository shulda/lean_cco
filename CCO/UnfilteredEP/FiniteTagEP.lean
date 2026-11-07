import CCO.UnfilteredEP.FiniteTagExpansion

/-! B064 C101--C104: universal expansion property on ONE full finite
original host, with every genuine-tag competitor quantified afterwards.
The inverse of its actual finite self-embedding matches the target tags.
No preferred expansion is substituted for that universal quantifier. -/

universe u v w
namespace CCO.UnfilteredEP
open TerminalHiddenHN APRamseyReadout APCharacter.Towers
noncomputable section
variable {B D : FiniteOwnerStage.{u,v,w}}
variable (h : History FiniteOwnerStage.Next B D) (terminal : D.Terminal)

/-- Every legal expansion of the full finite original source uses each
actual terminal tag exactly once. -/
theorem finite_full_competitor_tags_bijective
    (b : (finiteZeroChartData h terminal).Expansion (finiteWhole B.Point)) :
    Function.Bijective (finiteActualTag h terminal b) := by
  have hs : Function.Surjective b.toEmbedding :=
    Finite.surjective_of_injective b.toEmbedding.injective
  have hv : Function.Bijective
      (fun x : (finiteWhole B.Point).vertices => x.val) :=
    ⟨Subtype.val_injective,fun x => ⟨⟨x,Set.mem_univ _⟩,rfl⟩⟩
  exact (FiniteOwnerStage.terminalTagsEquiv h terminal).symm.bijective.comp
    (hv.comp ⟨b.toEmbedding.injective,hs⟩)

/-- C101: matching the actual tags embeds ANY target into EVERY legal
competitor on the previously fixed full old Q. -/
def finiteTagEveryCompetitor {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A)
    (b : (finiteZeroChartData h terminal).Expansion (finiteWhole B.Point)) :
    (finiteZeroChartData h terminal).Embedding a b := by
  let e : (finiteWhole B.Point).vertices ≃ (finiteWhole B.Point).vertices :=
    Equiv.ofBijective b.toEmbedding
      ⟨b.toEmbedding.injective,Finite.surjective_of_injective b.toEmbedding.injective⟩
  let f : A.vertices ↪ (finiteWhole B.Point).vertices :=
    a.toEmbedding.trans e.symm.toEmbedding
  have hf (x : A.vertices) : b.toEmbedding (f x) = a.toEmbedding x :=
    e.apply_symm_apply _
  let old : InducedEmbedding B.source A (finiteWhole B.Point) := {
    toEmbedding := f
    preserves_sort x := by
      have hb := b.preserves_sort (f x)
      rw [hf x] at hb
      exact hb.symm.trans (a.preserves_sort x)
    preserves_colours x y := by
      have hb := b.preserves_colours (f x) (f y)
      rw [hf x,hf y] at hb
      exact (a.preserves_colours x y).trans hb.symm }
  refine ⟨old,?_,?_⟩
  · intro tag x
    change (b.toEmbedding (f x)).val = _ ↔ (a.toEmbedding x).val = _
    rw [hf x]
  · intro R
    exact PEmpty.elim R

/-- EP retains the exact required order of the host and competitor. -/
theorem finite_zero_chart_EP : (finiteZeroChartData h terminal).EP := by
  intro A a
  refine ⟨finiteWhole B.Point,?_⟩
  intro b
  exact ⟨finiteTagEveryCompetitor h terminal a b⟩

/-- A single canonical labelled full Q is a joint host of any two
objects in this SAME actual genuine-tag expansion. -/
theorem finite_zero_chart_JEP
    (A C : FiniteInduced (X := B.Point))
    (a : (finiteZeroChartData h terminal).Expansion A)
    (c : (finiteZeroChartData h terminal).Expansion C) :
    ∃ (J : FiniteInduced (X := B.Point)) (j : (finiteZeroChartData h terminal).Expansion J),
      Nonempty ((finiteZeroChartData h terminal).Embedding a j) ∧
      Nonempty ((finiteZeroChartData h terminal).Embedding c j) := by
  let j := finitePointInclusion B.source (finiteWhole B.Point)
  exact ⟨finiteWhole B.Point,j,⟨finiteTagEveryCompetitor h terminal a j⟩,
    ⟨finiteTagEveryCompetitor h terminal c j⟩⟩

/-- The separate finite branch uses the SAME specified genuine history,
its actual zero chart and every terminal tag, with all output properties. -/
theorem genuine_finite_unfiltered_expansion :
    (finiteZeroChartData h terminal).Reasonable ∧
      (finiteZeroChartData h terminal).Ramsey ∧
      (finiteZeroChartData h terminal).EP ∧
      (∀ A, Finite ((finiteZeroChartData h terminal).Expansion A)) ∧
      (∀ i, IsEmpty (CloneTupleGeometry.FullCloneProperMI D.source i)) :=
  ⟨finite_zero_chart_reasonable h terminal,finite_zero_chart_ramsey h terminal,
    finite_zero_chart_EP h terminal,
    (finiteZeroChartData h terminal).finite_expansions,
    D.terminalProperMI_isEmpty terminal⟩

/-- Original finite AP+HOM CCO hypotheses internally construct a genuine
maximal-character tower and the unfiltered reasonable Ramsey EP readout.
No infinite-owner, positive-coordinate or hidden Ramsey premise is used. -/
theorem finite_unfiltered_source (B : FiniteOwnerStage.{u,v,w}) :
    ∃ D : FiniteOwnerStage.{u,v,w},
      ∃ h : History FiniteOwnerStage.Next B D, ∃ terminal : D.Terminal,
        (finiteZeroChartData h terminal).Reasonable ∧
          (finiteZeroChartData h terminal).Ramsey ∧
          (finiteZeroChartData h terminal).EP := by
  obtain ⟨D,h,terminal,_⟩ := B.finite_safe_terminalisation
  exact ⟨D,h,terminal,finite_zero_chart_reasonable h terminal,
    finite_zero_chart_ramsey h terminal,finite_zero_chart_EP h terminal⟩

end
end CCO.UnfilteredEP
