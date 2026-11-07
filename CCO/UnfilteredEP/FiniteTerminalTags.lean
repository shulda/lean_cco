import CCO.UnfilteredEP.FiniteOwnerTower
import CCO.CloneTupleGeometry.FullKernelMI
import CCO.CloneSAP.Quotient

/-! B064 C97--C100. Actual terminal tags of ANY genuine finite-owner
history name the original owners bijectively. Terminality is used in
the FULL current equivalence lattice. No positive-coordinate chart,
infinite-owner theorem or hidden Ramsey provider enters the proof. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP.FiniteOwnerStage
open CloneTupleGeometry APCharacter.Towers ParityHasse.Original
noncomputable section

variable (D : FiniteOwnerStage.{u,v,w})

/-- A finite owner source has finitely many genuine clone-kernel classes. -/
def cloneKernelQuotientEquiv (i : D.Sorts) :
    Quotient (fullCloneKernel D.source i).val ≃ D.Point i :=
  CloneSAP.quotientOwnerEquiv i

/-- C97: a proper K<Top interval would have finite relative index,
contradicting terminality. Thus the genuine clone kernel is Top. -/
theorem terminalKernel_eq_top (terminal : D.Terminal) (i : D.Sorts) :
    fullCloneKernel D.source i = ⊤ := by
  letI := D.finite i
  letI : Finite (Quotient (fullCloneKernel D.source i).val) :=
    Finite.of_equiv (D.Point i) (D.cloneKernelQuotientEquiv i).symm
  by_contra h
  obtain ⟨q⟩ := D.source.nonemptySort i
  have hfinite : Finite (RelativeClass (fullCloneKernel D.source i).val
      (⊤ : ColourEq (CloneSAP.source D.source) i).val (q,0)) :=
    Finite.of_injective _ (relativeClassToQuotient_injective
      (fullCloneKernel D.source i).val
      (⊤ : ColourEq (CloneSAP.source D.source) i).val (q,0))
  exact terminal ⟨i,fullCloneKernel D.source i,⊤,(q,0),
    lt_top_iff_ne_top.mpr h,hfinite⟩

/-- Each realized terminal tag has exactly one actual finite owner. -/
theorem terminalOwner_subsingleton (terminal : D.Terminal) (i : D.Sorts) :
    Subsingleton (D.Point i) := by
  refine ⟨fun x y => ?_⟩
  have hk : fullCloneKernel D.source i (x,0) (y,0) := by
    rw [D.terminalKernel_eq_top terminal i]
    trivial
  exact hk

/-- All FULL equivalences of a one-owner clone sort are Id or Top. -/
theorem terminal_equivalence_bot_or_top (terminal : D.Terminal) (i : D.Sorts)
    (J : ColourEq (CloneSAP.source D.source) i) : J = ⊥ ∨ J = ⊤ := by
  by_cases h : J = ⊥
  · exact Or.inl h
  · right
    apply top_le_iff.mp
    rw [← D.terminalKernel_eq_top terminal i]
    exact fullCloneKernel_le_nonidentity D.source i J h

/-- C98: there are no proper nonidentity FULL MI coordinates at all. -/
theorem terminalProperMI_isEmpty (terminal : D.Terminal) (i : D.Sorts) :
    IsEmpty (FullCloneProperMI D.source i) := by
  refine ⟨fun J => ?_⟩
  rcases D.terminal_equivalence_bot_or_top terminal i J.val with hbot | htop
  · exact J.property.1 hbot
  · exact J.property.2.ne_top htop

/-- The unique actual point carrying the supplied genuine terminal tag. -/
def terminalPoint (i : D.Sorts) : D.Point i :=
  Classical.choice (D.source.nonemptySort i)

/-- Forgetting a terminal point to its tag is a literal bijection,
using actual nonempty sorts and terminal owner uniqueness. -/
def terminalPointEquiv (terminal : D.Terminal) : D.Sorts ≃ Sigma D.Point where
  toFun i := ⟨i,D.terminalPoint i⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨i,x⟩
    haveI := D.terminalOwner_subsingleton terminal i
    exact congrArg (Sigma.mk i) (Subsingleton.elim _ _)

variable {B D}

/-- C97: actual terminal labels of this SAME supplied genuine history
are in bijection with the original finite owner points. -/
def terminalTagsEquiv (h : History Next B D) (terminal : D.Terminal) :
    D.Sorts ≃ Sigma B.Point :=
  (D.terminalPointEquiv terminal).trans
    (Equiv.ofBijective (historyReduct h).project (historyReduct h).bijective)

@[simp] theorem terminalTagsEquiv_apply (h : History Next B D)
    (terminal : D.Terminal) (i : D.Sorts) :
    terminalTagsEquiv h terminal i =
      (historyReduct h).project ⟨i,D.terminalPoint i⟩ := rfl

/-- Actual old sort of a terminal tag is its composite genuine parent. -/
theorem terminalTagsEquiv_sort (h : History Next B D)
    (terminal : D.Terminal) (i : D.Sorts) :
    (terminalTagsEquiv h terminal i).1 = (historyReduct h).parent i := rfl

/-- The terminal-tag palette has exactly the number of original owners. -/
theorem terminalTags_card (h : History Next B D) (terminal : D.Terminal) :
    Nat.card D.Sorts = Nat.card (Sigma B.Point) :=
  Nat.card_congr (terminalTagsEquiv h terminal)

end
end CCO.UnfilteredEP.FiniteOwnerStage
