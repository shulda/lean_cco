import CCO.UnfilteredEP.FiniteZeroChart
import CCO.UnfilteredEP.RealExpansionEP
import CCO.APRamseyReadout.FiniteSourceExpansion

/-! B064 C99--C104: zero-chart expansion with the SAME actual genuine
tower tags. The underlying point realizations are finite, but the unary
symbols are the actual terminal sort names, reindexed by the proved
terminalTagsEquiv of the supplied history. All old fine colours are fixed
by that tag table and no independent binary symbol is added. -/

universe u v w
namespace CCO.UnfilteredEP
open TerminalHiddenHN APRamseyReadout APCharacter.Towers
noncomputable section

namespace FiniteOwnerStage
instance finite_sigma (B : FiniteOwnerStage.{u,v,w}) : Finite (Sigma B.Point) := by
  letI := B.source.finiteSort
  letI := B.finite
  infer_instance
end FiniteOwnerStage

variable {B D : FiniteOwnerStage.{u,v,w}}
variable (h : History FiniteOwnerStage.Next B D) (terminal : D.Terminal)

/-- This is the actual zero-coordinate readout: unary names are the
supplied genuine endpoint's tags, and no free binary code remains. -/
def finiteZeroChartData : RealExpansionData.{u,v,w,u,max u v} B.source where
  Unary := D.Sorts
  Binary := PEmpty.{u+1}
  finiteUnary := by letI := D.source.finiteSort; infer_instance
  finiteBinary := inferInstance
  unarySort tag := (FiniteOwnerStage.terminalTagsEquiv h terminal tag).1
  leftSort := PEmpty.elim
  rightSort := PEmpty.elim
  Expansion A := InducedEmbedding B.source A (finiteWhole B.Point)
  nonempty A := ⟨finitePointInclusion B.source A⟩
  unary a tag x := (a.toEmbedding x).val = FiniteOwnerStage.terminalTagsEquiv h terminal tag
  binary a R := PEmpty.elim R
  unary_sorted a tag x hx :=
    (a.preserves_sort x).symm.trans (congrArg Sigma.fst hx)
  binary_sorted a R := PEmpty.elim R
  faithful a b hu hb := by
    have hp : a.toEmbedding = b.toEmbedding := by
      apply Function.Embedding.ext
      intro x
      apply Subtype.ext
      let e := FiniteOwnerStage.terminalTagsEquiv h terminal
      have ha : (a.toEmbedding x).val = e (e.symm (a.toEmbedding x).val) :=
        (e.apply_symm_apply _).symm
      exact ha.trans ((hu (e.symm (a.toEmbedding x).val) x).mp ha).symm
    cases a
    cases b
    cases hp
    rfl
  restrict f b := finiteLabelRestriction B.source f b
  restrict_unary f b tag x := Iff.rfl
  restrict_binary f b R := PEmpty.elim R

/-- A zero-chart object records its genuine terminal tag at each vertex. -/
def finiteActualTag {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x : A.vertices) : D.Sorts :=
  (FiniteOwnerStage.terminalTagsEquiv h terminal).symm (a.toEmbedding x).val

@[simp] theorem finiteActualTag_realizes {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x : A.vertices) :
    FiniteOwnerStage.terminalTagsEquiv h terminal (finiteActualTag h terminal a x) =
      (a.toEmbedding x).val :=
  (FiniteOwnerStage.terminalTagsEquiv h terminal).apply_symm_apply _

/-- Actual root labels use precisely the proved arity-zero chart. -/
def finiteActualRoot {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x : A.vertices) :
    FullCode.Root finiteEmptyHiddenStructure (finiteZeroRootScheme D) :=
  finiteZeroRoot D (finiteActualTag h terminal a x)

/-- Every actual finite tag marking gives a genuine zero-root object. -/
def finiteActualObject {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) :
    FullCode.Object finiteEmptyHiddenStructure (finiteZeroRootScheme D) A.vertices where
  root := finiteActualRoot h terminal a
  injective := by
    intro x y he
    have ht := congrArg FullCode.Root.tag he
    have hp := congrArg (FiniteOwnerStage.terminalTagsEquiv h terminal) ht
    change FiniteOwnerStage.terminalTagsEquiv h terminal (finiteActualTag h terminal a x) =
      FiniteOwnerStage.terminalTagsEquiv h terminal (finiteActualTag h terminal a y) at hp
    rw [finiteActualTag_realizes,finiteActualTag_realizes] at hp
    exact a.toEmbedding.injective (Subtype.ext hp)

theorem finiteActualObject_support_empty {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) :
    (finiteActualObject h terminal a).support = ∅ :=
  finiteZeroSupport_empty D _

/-- The original complete fine table is a fixed formula of the two tags. -/
def finiteTagColour (s t : D.Sorts) :=
  taggedColour B.source
    (FiniteOwnerStage.terminalTagsEquiv h terminal s)
    (FiniteOwnerStage.terminalTagsEquiv h terminal t)

theorem finite_fine_colour_from_tags {A : FiniteInduced (X := B.Point)}
    (a : (finiteZeroChartData h terminal).Expansion A) (x y : A.vertices) :
    taggedColour B.source x.val y.val =
      finiteTagColour h terminal (finiteActualTag h terminal a x)
        (finiteActualTag h terminal a y) := by
  unfold finiteTagColour
  rw [finiteActualTag_realizes,finiteActualTag_realizes]
  exact a.preserves_colours x y

/-- Every terminal-tag preserving map is a point-label preserving map;
this equivalence retains the literal original underlying embedding. -/
def finitePointEmbedding {A C : FiniteInduced (X := B.Point)}
    {a : (finiteZeroChartData h terminal).Expansion A}
    {c : (finiteZeroChartData h terminal).Expansion C}
    (f : (finiteZeroChartData h terminal).Embedding a c) :
    (finiteLabelExpansion B.source).Embedding a c where
  old := f.old
  unary_iff R x := by
    have hh := f.unary_iff ((FiniteOwnerStage.terminalTagsEquiv h terminal).symm R) x
    change (c.toEmbedding (f.old.toEmbedding x)).val =
      FiniteOwnerStage.terminalTagsEquiv h terminal
        ((FiniteOwnerStage.terminalTagsEquiv h terminal).symm R) ↔
      (a.toEmbedding x).val = FiniteOwnerStage.terminalTagsEquiv h terminal
        ((FiniteOwnerStage.terminalTagsEquiv h terminal).symm R) at hh
    rw [(FiniteOwnerStage.terminalTagsEquiv h terminal).apply_symm_apply R] at hh
    exact hh
  binary_iff R := PEmpty.elim R

def finiteTagEmbedding {A C : FiniteInduced (X := B.Point)}
    {a : (finiteZeroChartData h terminal).Expansion A}
    {c : (finiteZeroChartData h terminal).Expansion C}
    (f : (finiteLabelExpansion B.source).Embedding a c) :
    (finiteZeroChartData h terminal).Embedding a c where
  old := f.old
  unary_iff tag x := f.unary_iff (FiniteOwnerStage.terminalTagsEquiv h terminal tag) x
  binary_iff R := PEmpty.elim R

/-- C102: every embedding set between two labelled finite objects is thin. -/
theorem finiteTagEmbedding_unique {A C : FiniteInduced (X := B.Point)}
    {a : (finiteZeroChartData h terminal).Expansion A}
    {c : (finiteZeroChartData h terminal).Expansion C}
    (f g : (finiteZeroChartData h terminal).Embedding a c) : f = g := by
  have he := finiteLabelEmbedding_unique B.source
    (finitePointEmbedding h terminal f) (finitePointEmbedding h terminal g)
  apply RealExpansionData.Embedding.ext
  intro x
  exact congrArg (fun f => f.old.toEmbedding x) he

/-- C103: original finite homogeneity extends the prescribed genuine tags
along the SAME original induced embedding. -/
theorem finite_zero_chart_reasonable : (finiteZeroChartData h terminal).Reasonable := by
  intro A C f a
  obtain ⟨c,hc⟩ := finiteLabelExpansion_reasonable B.source B.homogeneous A C f a
  exact ⟨c,hc⟩

/-- C102: the labelled full original source is a common Ramsey host. -/
theorem finite_zero_chart_ramsey : (finiteZeroChartData h terminal).Ramsey := by
  intro A C a c n hn
  refine ⟨finiteWhole B.Point,finitePointInclusion B.source (finiteWhole B.Point),?_⟩
  intro colour
  let g := finiteTagEmbedding h terminal (finiteLabelToWhole B.source c)
  refine ⟨g,?_⟩
  intro f₁ f₂
  rw [finiteTagEmbedding_unique h terminal f₁ f₂]

end
end CCO.UnfilteredEP
