import CCO.UnfilteredEP.OwnerPairLocalStep

/-! B064 C85–C86: exact joint pair-locality for EVERY given genuine
finite safe history, by prefix induction through its actual unary reducts.
Intermediate fine atom names are recovered by injectivity of the actual
reduct atom maps; necessary pair masks alone are not called realization. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
noncomputable section

/-- The whole-diagram conclusion, distinct from mere allowed pair tables. -/
def PairLocal {B D : OwnerStage.{u,v,w}} (P : UnaryReduct B.source D.source) : Prop :=
  ∀ {n : Nat} (old : Fin n → Sigma B.Point), Function.Injective old →
    ∀ labels : Fin n → D.Sorts, PairCompatible P old labels →
    ∃ f : Fin n ↪ Sigma D.Point,
      (∀ x, (f x).1 = labels x) ∧
      ∀ x y, taggedColour B.source (P.project (f x)) (P.project (f y)) =
        taggedColour B.source (old x) (old y)

private def projectedColour {B D : OwnerStage.{u,v,w}}
    (P : UnaryReduct B.source D.source) (c : Age.Colour D.source) : Age.Colour B.source :=
  ⟨P.parent c.1,P.parent c.2.1,c.2.2.map (P.atom _ _)⟩

private theorem projectedColour_pair {B D : OwnerStage.{u,v,w}}
    (P : UnaryReduct B.source D.source) (p q : Sigma D.Point) :
    projectedColour P (taggedColour D.source p q) =
      taggedColour B.source (P.project p) (P.project q) := by
  change (⟨P.parent p.1,P.parent q.1,(D.source.colour p.2 q.2).map (P.atom _ _)⟩ :
    Age.Colour B.source) = _
  rw [← P.colour]
  rfl

/-- Zero steps realize the same old diagram; label agreement follows
from the diagonal part of the complete pointwise compatibility test. -/
theorem pairLocal_identity (B : OwnerStage.{u,v,w}) : PairLocal (UnaryReduct.identity B.source) := by
  intro n old hinj labels compatible
  refine ⟨⟨old,hinj⟩,?_,fun _ _ => rfl⟩
  intro x
  obtain ⟨p,q,hp,_,hc⟩ := compatible x x
  exact (congrArg (fun c : Age.Colour B.source => c.1) hc).symm.trans hp

/-- Prefix labels are first realized in the actual middle source. Their
entire middle fine matrix is then forced by original colours and middle
sort names, allowing the remainder of the history to be realized. -/
theorem pairLocal_comp {B D E : OwnerStage.{u,v,w}}
    (P : UnaryReduct B.source D.source) (Q : UnaryReduct D.source E.source)
    (hP : PairLocal P) (hQ : PairLocal Q) : PairLocal (P.compose Q) := by
  intro n old hinj labels compatible
  let middleLabels : Fin n → D.Sorts := Q.parent ∘ labels
  have hmiddle : PairCompatible P old middleLabels := by
    intro x y
    obtain ⟨p,q,hp,hq,hc⟩ := compatible x y
    exact ⟨Q.project p,Q.project q,congrArg Q.parent hp,congrArg Q.parent hq,hc⟩
  obtain ⟨middle,hsort,hcolour⟩ := hP old hinj middleLabels hmiddle
  have htail : PairCompatible Q middle labels := by
    intro x y
    obtain ⟨p,q,hp,hq,hc⟩ := compatible x y
    refine ⟨p,q,hp,hq,?_⟩
    apply TerminalHiddenHN.UnaryLift.tagged_of_projected_and_sorts P
    · exact (congrArg Q.parent hp).trans (hsort x).symm
    · exact (congrArg Q.parent hq).trans (hsort y).symm
    · exact hc.trans (hcolour x y).symm
  obtain ⟨f,hf,hfC⟩ := hQ middle middle.injective labels htail
  refine ⟨f,hf,?_⟩
  intro x y
  have hc := congrArg (projectedColour P) (hfC x y)
  rw [projectedColour_pair,projectedColour_pair] at hc
  exact hc.trans (hcolour x y)

/-- One actual SafeStep satisfies the whole finite pair-local theorem,
using its genuine B044 marked-age realization rather than a new premise. -/
theorem safeStep_pairLocal {B D : OwnerStage.{u,v,w}} (s : OwnerStage.SafeStep B D) :
    PairLocal s.reduct := by
  cases s with
  | phase P => exact owner_successor_pairLocal _ P

/-- Exact pair-locality for ANY supplied genuine owner history. No
preferred terminalization algorithm or mere existential tower is substituted. -/
theorem owner_history_pairLocal {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) : PairLocal (OwnerStage.historyReduct history) := by
  induction history with
  | nil B => exact pairLocal_identity B
  | cons step tail ih =>
    exact pairLocal_comp (Classical.choice step).reduct (OwnerStage.historyReduct tail)
      (safeStep_pairLocal (Classical.choice step)) ih

end
end CCO.UnfilteredEP
