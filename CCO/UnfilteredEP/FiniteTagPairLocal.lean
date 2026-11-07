import CCO.UnfilteredEP.FiniteTagEP

/-! The zero-chart objects are EXACTLY the pair-local legal markings
by the same actual terminal tags. Repeated labels on distinct original
vertices are excluded by the original real diagonal, rather than by an
extra injectivity premise. The source realization is recovered through
the literal composite genuine-history reduct. -/

universe u v w
namespace CCO.UnfilteredEP
open TerminalHiddenHN APRamseyReadout APCharacter.Towers
noncomputable section
variable {B D : FiniteOwnerStage.{u,v,w}}
variable (h : History FiniteOwnerStage.Next B D) (terminal : D.Terminal)

/-- Original named sorts and all original diversity-pair atoms are
retained by the exact fixed table of actual terminal tags. -/
def FinitePairLocal {A : FiniteInduced (X := B.Point)} (label : A.vertices → D.Sorts) : Prop :=
  (∀ x, (FiniteOwnerStage.terminalTagsEquiv h terminal (label x)).1 = x.val.1) ∧
    ∀ x y, x ≠ y → taggedColour B.source x.val y.val =
      finiteTagColour h terminal (label x) (label y)

/-- A pair-local legal marking determines one actual finite old
realization; no distinctness assumption is added for equal labels. -/
def finiteMarkingRealization {A : FiniteInduced (X := B.Point)}
    (label : A.vertices → D.Sorts) (legal : FinitePairLocal h terminal label) :
    (finiteZeroChartData h terminal).Expansion A where
  toEmbedding := {
    toFun x := ⟨FiniteOwnerStage.terminalTagsEquiv h terminal (label x),Set.mem_univ _⟩
    inj' := by
      intro x y hxy
      by_contra hne
      have hc := legal.2 x y hne
      have he : FiniteOwnerStage.terminalTagsEquiv h terminal (label x) =
          FiniteOwnerStage.terminalTagsEquiv h terminal (label y) :=
        congrArg Subtype.val hxy
      have hp : x.val = y.val :=
        (APCharacter.SourceAge.UnarySource.equality_iff B.source _ _ _ _ hc).mpr he
      exact hne (Subtype.ext hp) }
  preserves_sort := legal.1
  preserves_colours x y := by
    by_cases he : x = y
    · subst y
      let q := FiniteOwnerStage.terminalTagsEquiv h terminal (label x)
      change taggedColour B.source x.val x.val = taggedColour B.source q q
      have hu := (B.source.colour_none_iff x.val.2 x.val.2).mpr rfl
      have hv := (B.source.colour_none_iff q.2 q.2).mpr rfl
      unfold taggedColour
      rw [hu,hv]
      exact congrArg (fun i =>
        (⟨i,i,none⟩ : Σ i : B.Sorts, Σ j : B.Sorts, Option (B.source.Atom i j)))
        (legal.1 x).symm
    · exact legal.2 x y he

/-- Every allowed zero-chart object has precisely its actual terminal
labels, with the original pair-local rule and no additional restriction. -/
theorem finiteActualTag_pairLocal {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) :
    FinitePairLocal h terminal (finiteActualTag h terminal a) := by
  constructor
  · intro x
    rw [finiteActualTag_realizes]
    exact a.preserves_sort x
  · intro x y _
    exact finite_fine_colour_from_tags h terminal a x y

@[simp] theorem finiteMarkingRealization_tag {A : FiniteInduced (X := B.Point)}
    (label : A.vertices → D.Sorts) (legal : FinitePairLocal h terminal label)
    (x : A.vertices) :
    finiteActualTag h terminal (finiteMarkingRealization h terminal label legal) x = label x :=
  (FiniteOwnerStage.terminalTagsEquiv h terminal).symm_apply_apply _

/-- Exact pair-locality of the actual finite genuine terminal recipe. -/
theorem finite_pair_local_iff {A : FiniteInduced (X := B.Point)}
    (label : A.vertices → D.Sorts) :
    FinitePairLocal h terminal label ↔
      ∃ a : (finiteZeroChartData h terminal).Expansion A,
        finiteActualTag h terminal a = label := by
  constructor
  · intro legal
    exact ⟨finiteMarkingRealization h terminal label legal,
      funext (finiteMarkingRealization_tag h terminal label legal)⟩
  · rintro ⟨a,rfl⟩
    exact finiteActualTag_pairLocal h terminal a

/-- The actual terminal point realizing a zero-chart label in the
supplied genuine endpoint, before its composite reduct is applied. -/
def finiteRecipePoint {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x : A.vertices) : Sigma D.Point :=
  ⟨finiteActualTag h terminal a x,
    D.terminalPoint (finiteActualTag h terminal a x)⟩

/-- Every allowed marking is realized in the SAME actual endpoint:
its literal genuine-history projection is exactly its old realization. -/
theorem finiteRecipePoint_projects {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x : A.vertices) :
    (FiniteOwnerStage.historyReduct h).project (finiteRecipePoint h terminal a x) =
      (a.toEmbedding x).val :=
  finiteActualTag_realizes h terminal a x

theorem finiteRecipePoint_injective {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) :
    Function.Injective (finiteRecipePoint h terminal a) := by
  intro x y he
  apply a.toEmbedding.injective
  apply Subtype.ext
  have hp := congrArg (FiniteOwnerStage.historyReduct h).project he
  rw [finiteRecipePoint_projects,finiteRecipePoint_projects] at hp
  exact hp

end
end CCO.UnfilteredEP
