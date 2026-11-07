import CCO.UnfilteredEP.OwnerHistoryReceiving
import CCO.AutomaticEPCore.SourceExports
import CCO.AutomaticEPCore.NamedIsoEndTransfer

/-! The SAME arbitrary genuine clone-stable owner history has a core
unfiltered ORIGINAL-owner-atom table. Its actual history is received in
B063 with all old predicate values fixed. The additional clone atom has
exactly diagonal type support, so forgetting it changes no endomorphism.
No automatic-core premise or preferred safe tower is supplied. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w
namespace CCO.UnfilteredEP
open CloneTupleGeometry APCharacter APCharacter.Towers
open APCharacter.SourceAge RigidGroupoid.Geometry ExactEPGeometry AutomaticEPCore ParityHasse.Original
noncomputable section
variable {B D : OwnerStage.{u,v,w}}
variable (base : B.Sorts) (hOne : ∀ i : B.Sorts, base = i)
variable (history : History OwnerStage.Next B D)

/-- Original clone-atom predicates, with every atom's literal name fixed. -/
def ownerCloneRootCode (p q : Sigma (CloneSAP.Carrier B.Point)) :
    B.cloneCurrent.source.Atom base base → Prop :=
  fun a => originalRelation B.cloneCurrent base hOne
    (B.cloneCurrent.source.atomRel a) p q

def ownerCloneAtomTable (a : B.cloneCurrent.source.Atom base base)
    (s t : D.Sorts) : Prop :=
  codedPredicateSupport
    (ownerCodedCurrent D (ownerCloneRootCode base hOne) (OwnerStage.historyReduct history))
    (fun code => code a) s t

/-- B063's actual bipartite original-atom separation/core is transported
to the prescribed actual endpoint names using fixed-code witnesses. -/
theorem owner_terminal_clone_atom_core (terminal : D.Terminal)
    (f : D.Sorts → D.Sorts)
    (hf : TableEndomorphism (ownerCloneAtomTable base hOne history) f) :
    TableAutomorphism (ownerCloneAtomTable base hOne history) f := by
  let rootCode := ownerCloneRootCode base hOne
  obtain ⟨next,⟨received⟩,⟨I⟩⟩ := ownerHistoryExactPrefix rootCode history
  have nextTerminal : next.current.Terminal :=
    (namedIso_terminal_iff I.toNamedCurrentSourceIso).mpr terminal
  have full := actual_terminal_full_cover next.current nextTerminal
  let BP : Set (B.cloneCurrent.source.Atom base base) :=
    {a | (atomGraph B.cloneCurrent.source a).IsBipartite}
  have support (a : B.cloneCurrent.source.Atom base base) (s t : D.Sorts) :
      ownerCloneAtomTable base hOne history a s t ↔
      originalAtomTable B.cloneCurrent next.current next.reduct base hOne a
        (I.sorts.symm s) (I.sorts.symm t) :=
    codedPredicateSupport_target_iff I (fun code => code a) s t
  have loopless : ∀ a ∈ BP, ∀ t, ¬ownerCloneAtomTable base hOne history a t t := by
    intro a ha t hLoop
    exact original_bipartite_table_loopless B.cloneCurrent next.current next.reduct
      base hOne full a ha (I.sorts.symm t) ((support a t t).mp hLoop)
  have separates : ∀ s t : D.Sorts, s ≠ t →
      ∃ a ∈ BP, ownerCloneAtomTable base hOne history a s t := by
    intro s t different
    have diff : I.sorts.symm s ≠ I.sorts.symm t :=
      fun he => different (I.sorts.symm.injective he)
    obtain ⟨a,bipartite,pair⟩ :=
      (actual_tower_separation B.cloneCurrent base hOne) next received nextTerminal
        (I.sorts.symm s) (I.sorts.symm t) diff
    exact ⟨a,bipartite,(support a s t).mpr pair⟩
  letI := D.source.finiteSort
  exact finite_table_core_of_separation (ownerCloneAtomTable base hOne history)
    BP loopless separates f hf

/-- The same literal unique-original-sort identification for real owners. -/
def ownerOriginalPoint : Sigma B.Point ≃ B.Point base where
  toFun p := (hOne p.1).symm ▸ p.2
  invFun x := ⟨base,x⟩
  left_inv p := by
    rcases p with ⟨i,x⟩
    cases hOne i
    rfl
  right_inv _ := rfl

def ownerOriginalAtomTable (a : B.source.Atom base base) (s t : D.Sorts) : Prop :=
  prefixSupport (OwnerStage.historyReduct history)
    (fun p q => B.source.atomRel a
      (ownerOriginalPoint base hOne p) (ownerOriginalPoint base hOne q)) s t

/-- One-sort identification commutes with actual clone-owner erasure. -/
theorem originalClonePoint_owner (p : Sigma (CloneSAP.Carrier B.Point)) :
    (originalPointEquiv B.cloneCurrent base hOne p).1 =
      ownerOriginalPoint base hOne (CloneSAP.owner p) := by
  rcases p with ⟨i,x,n⟩
  cases hOne i
  rfl

theorem originalClonePoint_index (p : Sigma (CloneSAP.Carrier B.Point)) :
    (originalPointEquiv B.cloneCurrent base hOne p).2 = p.2.2 := by
  rcases p with ⟨i,x,n⟩
  cases hOne i
  rfl

/-- The original-owner relation is exactly the old-atom sector of the
full clone table. Both directions construct actual source-point witnesses. -/
theorem ownerClone_old_atom_iff (a : B.source.Atom base base) (s t : D.Sorts) :
    ownerCloneAtomTable base hOne history (.inl a) s t ↔
      ownerOriginalAtomTable base hOne history a s t := by
  have pair (p : Sigma (CloneSAP.Carrier D.Point)) (q : Sigma (CloneSAP.Carrier D.Point)) :
      ownerCloneRootCode base hOne
        (ownerCloneProject (OwnerStage.historyReduct history) p)
        (ownerCloneProject (OwnerStage.historyReduct history) q) (.inl a) ↔
      B.source.atomRel a
        (ownerOriginalPoint base hOne ((OwnerStage.historyReduct history).project (CloneSAP.owner p)))
        (ownerOriginalPoint base hOne ((OwnerStage.historyReduct history).project (CloneSAP.owner q))) := by
    change CloneSAP.colour B.source _ _ = some (.inl a) ↔ _
    rw [CloneSAP.colour_old_iff,originalClonePoint_owner,originalClonePoint_owner]
    rfl
  constructor
  · rintro ⟨x,y,hxy⟩
    exact ⟨x.1,y.1,(pair ⟨s,x⟩ ⟨t,y⟩).mp hxy⟩
  · rintro ⟨x,y,hxy⟩
    exact ⟨(x,0),(y,0),(pair ⟨s,(x,0)⟩ ⟨t,(y,0)⟩).mpr hxy⟩

/-- The new clone diversity name has EXACTLY diagonal type support. -/
theorem ownerClone_marker_iff (s t : D.Sorts) :
    ownerCloneAtomTable base hOne history (.inr ⟨rfl⟩) s t ↔ s = t := by
  constructor
  · rintro ⟨x,y,hxy⟩
    change CloneSAP.colour B.source _ _ = some (.inr ⟨rfl⟩) at hxy
    have owners := (CloneSAP.colour_clone_iff B.source _ _ ⟨rfl⟩).mp hxy
    have hp : (OwnerStage.historyReduct history).project ⟨s,x.1⟩ =
        (OwnerStage.historyReduct history).project ⟨t,y.1⟩ := by
      apply (ownerOriginalPoint base hOne).injective
      have same : (originalPointEquiv B.cloneCurrent base hOne
          (ownerCloneProject (OwnerStage.historyReduct history) ⟨s,x⟩)).1 =
          (originalPointEquiv B.cloneCurrent base hOne
            (ownerCloneProject (OwnerStage.historyReduct history) ⟨t,y⟩)).1 := by
        exact eq_of_heq (Sigma.mk.inj owners.1).2
      simpa only [originalClonePoint_owner,CloneSAP.owner,ownerCloneProject,UnaryReduct.project] using same
    exact congrArg Sigma.fst ((OwnerStage.historyReduct history).bijective.1 hp)
  · intro same
    subst t
    obtain ⟨x⟩ := D.source.nonemptySort s
    refine ⟨(x,0),(x,1),?_⟩
    change CloneSAP.colour B.source _ _ = some (.inr ⟨rfl⟩)
    apply (CloneSAP.colour_clone_iff B.source _ _ ⟨rfl⟩).mpr
    constructor
    · have same : (originalPointEquiv B.cloneCurrent base hOne
          (ownerCloneProject (OwnerStage.historyReduct history) ⟨s,(x,0)⟩)).1 =
          (originalPointEquiv B.cloneCurrent base hOne
            (ownerCloneProject (OwnerStage.historyReduct history) ⟨s,(x,1)⟩)).1 := by
        rw [originalClonePoint_owner,originalClonePoint_owner]
        rfl
      exact congrArg (fun q => (⟨base,q⟩ : Sigma B.Point)) same
    · rw [originalClonePoint_index,originalClonePoint_index]
      exact Nat.zero_ne_one

/-- Forgetting the diagonal clone name changes NO endomorphism. -/
theorem owner_clone_table_end_iff (f : D.Sorts → D.Sorts) :
    TableEndomorphism (ownerCloneAtomTable base hOne history) f ↔
      TableEndomorphism (ownerOriginalAtomTable base hOne history) f := by
  constructor
  · intro preserve a s t pair
    exact (ownerClone_old_atom_iff base hOne history a (f s) (f t)).mp
      (preserve (.inl a) ((ownerClone_old_atom_iff base hOne history a s t).mpr pair))
  · intro preserve a s t pair
    cases a with
    | inl a =>
      exact (ownerClone_old_atom_iff base hOne history a (f s) (f t)).mpr
        (preserve a ((ownerClone_old_atom_iff base hOne history a s t).mp pair))
    | inr marker =>
      exact (ownerClone_marker_iff base hOne history (f s) (f t)).mpr
        (congrArg f ((ownerClone_marker_iff base hOne history s t).mp pair))

/-- C87: actual unfiltered original-owner atom table is core after ANY
specified genuine maximal-character owner history to terminal D. -/
theorem owner_terminal_old_atom_core (terminal : D.Terminal) (f : D.Sorts → D.Sorts)
    (hf : TableEndomorphism (ownerOriginalAtomTable base hOne history) f) :
    TableAutomorphism (ownerOriginalAtomTable base hOne history) f := by
  have cloneEnd := (owner_clone_table_end_iff base hOne history f).mpr hf
  have cloneAuto := owner_terminal_clone_atom_core base hOne history terminal f cloneEnd
  letI := D.source.finiteSort
  exact finite_table_endomorphism_automorphism (ownerOriginalAtomTable base hOne history)
    f hf cloneAuto.1.1

end
end CCO.UnfilteredEP
