import CCO.UnfilteredEP.OwnerTemplate
import CCO.UnfilteredEP.OwnerHistoryCore

/-! The literal finite original-sort/atom template used by the independent
singleton criterion is a core for the SAME supplied genuine owner history.
The source B063 original-atom theorem is transported to these actual typed
pair witnesses; no terminal label is individually named in the template. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter.Towers
noncomputable section
variable {B D : OwnerStage.{u,v,w}}
variable (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
variable (history : History OwnerStage.Next B D)

/-- Reading the one original sort uses only actual dependent casts.
Logical equality is still the none sector of the original palette. -/
theorem one_sort_old_atom_iff (a : B.source.Atom base base) (p q : Sigma B.Point) :
    taggedColour B.source p q = ⟨base,base,some a⟩ ↔
      B.source.atomRel a (ownerOriginalPoint base one p) (ownerOriginalPoint base one q) := by
  rcases p with ⟨i,p⟩
  rcases q with ⟨j,q⟩
  cases one i
  cases one j
  change (⟨base,base,B.source.colour p q⟩ :
    Σ i, Σ j, Option (B.source.Atom i j)) = ⟨base,base,some a⟩ ↔ _
  simp only [Sigma.mk.injEq,heq_eq_eq,true_and]
  rfl

/-- The old base-atom sector is exactly the original-atom support used
by the genuine-history automatic-core theorem, on the same endpoint tags. -/
theorem owner_template_base_atom_iff (a : B.source.Atom base base) (s t : D.Sorts) :
    (ownerTemplate history).rel ⟨base,base,a⟩ s t ↔
      ownerOriginalAtomTable base one history a s t := by
  constructor
  · rintro ⟨⟨i,x⟩,⟨j,y⟩,hs,ht,hpair⟩
    dsimp only at hs ht
    subst i
    subst j
    exact ⟨x,y,(one_sort_old_atom_iff base one a _ _).mp hpair⟩
  · rintro ⟨x,y,hpair⟩
    exact ⟨⟨s,x⟩,⟨t,y⟩,rfl,rfl,(one_sort_old_atom_iff base one a _ _).mpr hpair⟩

include base one in
/-- C87 in the precise source-independent finite template language.
Only actual original sorts and diversity atom names are preserved. -/
theorem actual_owner_template_core (terminal : D.Terminal) :
    (ownerTemplate history).Core := by
  intro f preserve
  have oldEnd : CCO.AutomaticEPCore.TableEndomorphism
      (ownerOriginalAtomTable base one history) f := by
    intro a s t pair
    exact (owner_template_base_atom_iff base one history a (f s) (f t)).mp
      (preserve.2 ⟨base,base,a⟩ s t
        ((owner_template_base_atom_iff base one history a s t).mpr pair))
  have oldAuto := owner_terminal_old_atom_core base one history terminal f oldEnd
  let := D.source.finiteSort
  exact (ownerTemplate history).automorphism_of_injective f preserve oldAuto.1.1

end
end CCO.UnfilteredEP
