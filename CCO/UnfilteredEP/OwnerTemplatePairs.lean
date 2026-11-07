import CCO.UnfilteredEP.OwnerMarkingLift

/-! Every original-atom/label table entry of a genuine owner history is
realized by two DISTINCT old vertices carrying a legal whole marking.
This includes repeated labels and supplies the exact A01 witness clause. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.TerminalHiddenHN
noncomputable section

private def pairColourCode (B : OwnerStage.{u,v,w}) (c : Age.Colour B.source) :
    Option (OwnerOriginalAtom B) := c.2.2.map (fun a => ⟨c.1,c.2.1,a⟩)

/-- Actual diversity pairs remain distinct after the literal unary
reduct, even when both proposed terminal labels are the same. -/
theorem owner_template_pairs_realized {B D : OwnerStage.{u,v,w}}
    (history : History OwnerStage.Next B D) :
    (ownerFiniteAge B).AllPairsRealized (ownerTemplate history) := by
  intro atom s t pair
  obtain ⟨p,q,hp,hq,hpair⟩ := pair
  let P := OwnerStage.historyReduct history
  let A : FiniteInduced (X := B.Point) :=
    ⟨{P.project p,P.project q},(Set.finite_singleton _).insert _⟩
  let x : A.vertices := ⟨P.project p,by simp [A]⟩
  let y : A.vertices := ⟨P.project q,by simp [A]⟩
  let L := UnaryLift.canonicalLift P A
  let m := reductMarkingOfLift P L
  have hpx : L.point x = p :=
    (Equiv.ofBijective P.project P.bijective).symm_apply_apply p
  have hqy : L.point y = q :=
    (Equiv.ofBijective P.project P.bijective).symm_apply_apply q
  have hcol : (ownerFiniteAge B).colour A x y = some atom :=
    congrArg (pairColourCode B) hpair
  refine ⟨A,m,x,y,?_,hcol,?_,?_⟩
  · intro hxy
    have hnone := ((ownerFiniteAge B).diagonal A x y).mpr hxy
    rw [hcol] at hnone
    cases hnone
  · change (L.point x).1 = s
    rw [hpx]
    exact hp
  · change (L.point y).1 = t
    rw [hqy]
    exact hq

end
end CCO.UnfilteredEP
