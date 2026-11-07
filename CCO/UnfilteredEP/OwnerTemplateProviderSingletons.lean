import CCO.UnfilteredEP.OwnerTemplateProviderArrows

/-! Each full terminal label has one ACTUAL expanded singleton. Every
vertex in an arbitrary full block-code provider object induces that same
singleton, using proved actual singleton faithfulness on its whole support. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.APRamseyReadout CCO.TerminalHiddenHN
noncomputable section

variable {B D : OwnerStage.{u,v,w}} (history : History OwnerStage.Next B D)
variable (terminal : D.Terminal) (F : Charts.{u,v,w,p} D)
variable (priority : LinearOrder (CoordinateLanguage D terminal).Sorts)
local notation "P" => OwnerStage.historyReduct history
local notation "E" => actualFullBlockReadoutData D terminal F priority
local notation "R" => ownerTemplateProvider history terminal F priority

abbrev ownerSingletonPoint (s : D.Sorts) : Sigma D.Point :=
  ⟨s,Classical.choice (D.source.nonemptySort s)⟩

def ownerSingletonOld (s : D.Sorts) : FiniteInduced (X := B.Point) :=
  ⟨{(P).project (ownerSingletonPoint (D := D) s)},Set.finite_singleton _⟩

def ownerSingletonLift (s : D.Sorts) : UnaryLift.Lift P (ownerSingletonOld history s) where
  point _ := ownerSingletonPoint (D := D) s
  injective x y _ := Subtype.ext
    ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)
  sort_eq x := congrArg Sigma.fst (Set.mem_singleton_iff.mp x.property).symm
  colour_eq x y := congrArg₂ (taggedColour B.source)
    (Set.mem_singleton_iff.mp x.property).symm (Set.mem_singleton_iff.mp y.property).symm

theorem ownerSingletonLift_point (s : D.Sorts)
    (x : (ownerSingletonLift history s).object.vertices) :
    x.val = ownerSingletonPoint (D := D) s := by
  obtain ⟨y,hy⟩ := x.property
  exact hy.symm

abbrev ownerSingletonObject (s : D.Sorts) : OwnerProviderObject history terminal F priority :=
  ⟨ownerSingletonOld history s,ownerSingletonLift history s,
    Classical.choice ((E).nonempty (ownerSingletonLift history s).object)⟩

abbrev ownerSingletonRoot (s : D.Sorts) : (ownerSingletonOld history s).vertices :=
  ⟨(P).project (ownerSingletonPoint (D := D) s),Set.mem_singleton _⟩

/-- Every vertex of an arbitrary provider object gives an actual
induced map from the selected terminal singleton on the whole support. -/
def ownerSingletonTerminalEmbedding (A : OwnerProviderObject history terminal F priority)
    (x : A.1.vertices) :
    InducedEmbedding D.source
      (ownerSingletonLift history (((R).marking A).label x)).object A.2.1.object where
  toEmbedding := {
    toFun _ := A.2.1.toObject x
    inj' := by
      intro y z _
      exact Subtype.ext ((ownerSingletonLift_point history _ y).trans
        (ownerSingletonLift_point history _ z).symm) }
  preserves_sort y := by
    change (A.2.1.point x).1 = y.val.1
    rw [ownerSingletonLift_point]
    rfl
  preserves_colours y z := by
    rw [ownerSingletonLift_point history _ y,ownerSingletonLift_point history _ z]
    change taggedColour D.source (ownerSingletonPoint (D := D) (((R).marking A).label x))
      (ownerSingletonPoint (D := D) (((R).marking A).label x)) =
      taggedColour D.source (A.2.1.point x) (A.2.1.point x)
    change (⟨_,_,D.source.colour _ _⟩ : Age.Colour D.source) = ⟨_,_,D.source.colour _ _⟩
    rw [(D.source.colour_none_iff _ _).mpr rfl,(D.source.colour_none_iff _ _).mpr rfl]
    rfl

/-- Actual singleton faithfulness fills the generic singleton-provider
contract; no EP or template-core result is used. -/
def owner_template_provider_singletons : (R).Singletons where
  object := ownerSingletonObject history terminal F priority
  point := ownerSingletonRoot history
  only_point t x := Subtype.ext (Set.mem_singleton_iff.mp x.property)
  labelled _ := rfl
  at_vertex A x := by
    let s := ((R).marking A).label x
    let old := ownerSingletonTerminalEmbedding history terminal F priority A x
    let single := ownerSingletonObject history terminal F priority s
    let readout := actual_singleton_block_embedding D terminal F priority
      (ownerSingletonPoint (D := D) s) (ownerSingletonLift_point history s)
      single.2.2 A.2.2 old
    let full := readoutToFullBlock (actualTupleInterpretation D terminal F)
      D.homogeneous priority readout
    let final := ownerProviderEmbeddingOfReal history terminal F priority
      (UnaryLift.toOldEmbedding P E single.2.1 A.2.1 full)
    refine ⟨final,?_⟩
    change A.2.1.toObject.symm (A.2.1.toObject x) = x
    exact A.2.1.toObject.symm_apply_apply x

end
end CCO.UnfilteredEP
