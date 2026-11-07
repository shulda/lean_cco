import CCO.UnfilteredEP.OwnerPairLocalHistory

/-! Exact pair-local markings are precisely the finite labelled diagrams
of the SAME given genuine owner history. Whole lifts may move old points
while retaining ALL old fine colours, as required by the actual age. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.TerminalHiddenHN
noncomputable section

private def diversityCode (B : OwnerStage.{u,v,w}) (c : Age.Colour B.source) :
    Option (OwnerOriginalAtom B) := c.2.2.map (fun a => ⟨c.1,c.2.1,a⟩)

private theorem diversityCode_some {B : OwnerStage.{u,v,w}}
    (c : Age.Colour B.source) (a : OwnerOriginalAtom B) :
    diversityCode B c = some a ↔ c = ⟨a.1,a.2.1,some a.2.2⟩ := by
  constructor
  · intro h
    rcases c with ⟨i,j,c⟩
    cases c with
    | none =>
      change (none : Option (OwnerOriginalAtom B)) = some a at h
      cases h
    | some b =>
      have he : (⟨i,j,b⟩ : OwnerOriginalAtom B) = a := Option.some.inj h
      rw [← he]
  · rintro rfl
    rfl

/-- A whole actual endpoint lift yields a legal pair-local marking.
This is the converse inclusion in the exact finite age characterization. -/
def reductMarkingOfLift {B D : OwnerStage.{u,v,w}}
    (P : UnaryReduct B.source D.source) {A : FiniteInduced (X := B.Point)}
    (L : UnaryLift.Lift P A) : (ownerFiniteAge B).Marking (reductTemplate P) A where
  label x := (L.point x).1
  sorted x := L.sort_eq x
  pairs x y a hc := by
    refine ⟨L.point x,L.point y,rfl,rfl,?_⟩
    exact (L.colour_eq x y).trans ((diversityCode_some _ a).mp hc)

/-- ANY pair-legal full marking is realized by one endpoint diagram of
this SAME supplied history. All labels and old fine colours are retained
simultaneously; there is no finite-age/provider realization premise. -/
theorem owner_marking_lift {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) (A : FiniteInduced (X := B.Point))
    (a : (ownerFiniteAge B).Marking (ownerTemplate history) A) :
    ∃ L : UnaryLift.Lift (OwnerStage.historyReduct history) A,
      ∀ x, (L.point x).1 = a.label x := by
  classical
  let _ : Finite A.vertices := A.finite_vertices.to_subtype
  let _ : Fintype A.vertices := Fintype.ofFinite _
  let index := Fintype.equivFin A.vertices
  let old : Fin (Fintype.card A.vertices) → Sigma B.Point := fun x => (index.symm x).val
  let labels : Fin (Fintype.card A.vertices) → D.Sorts := a.label ∘ index.symm
  have compatible : PairCompatible (OwnerStage.historyReduct history) old labels :=
    fun x y => marking_pairCompatible (OwnerStage.historyReduct history) A a
      (index.symm x) (index.symm y)
  obtain ⟨f,hf,hc⟩ := owner_history_pairLocal history old
    (Subtype.val_injective.comp index.symm.injective) labels compatible
  let point : A.vertices → Sigma D.Point := fun x => f (index x)
  have hcol (x y : A.vertices) :
      taggedColour B.source ((OwnerStage.historyReduct history).project (point x))
        ((OwnerStage.historyReduct history).project (point y)) =
        taggedColour B.source x.val y.val := by
    simpa only [old,Equiv.symm_apply_apply] using hc (index x) (index y)
  refine ⟨{
    point := point
    injective := f.injective.comp index.injective
    sort_eq x := congrArg (fun c : Age.Colour B.source => c.1) (hcol x x)
    colour_eq := hcol },?_⟩
  intro x
  simpa only [labels,Function.comp_apply,Equiv.symm_apply_apply] using hf (index x)

/-- The endpoint age consists EXACTLY of the pair-local legal markings,
not merely of a subclass satisfying necessary allowed pair conditions. -/
theorem owner_pairLocal_age_iff {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) (A : FiniteInduced (X := B.Point))
    (labels : A.vertices → D.Sorts) :
    (∃ a : (ownerFiniteAge B).Marking (ownerTemplate history) A, a.label = labels) ↔
      ∃ L : UnaryLift.Lift (OwnerStage.historyReduct history) A,
        ∀ x, (L.point x).1 = labels x := by
  constructor
  · rintro ⟨a,rfl⟩
    exact owner_marking_lift history A a
  · rintro ⟨L,hL⟩
    exact ⟨reductMarkingOfLift (OwnerStage.historyReduct history) L,funext hL⟩

end
end CCO.UnfilteredEP
