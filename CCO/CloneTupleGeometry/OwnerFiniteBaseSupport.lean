import CCO.CloneTupleGeometry.OwnerReasonableness
import CCO.CloneTupleGeometry.OwnerSourceHomogeneity
import CCO.CloneTupleGeometry.ActualOldMonoClique
import CCO.RawExact.TaggedColourConverse

/-! Finite-base support for the genuine owner character expansion.
Actual finite old owner diagrams carrying compatible character bits embed
in the actual marked owner source, with their full old names and child
labels together. No arbitrary unary expansion or owner SAP is used. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : CloneMarkedIdentification S H C P cco)

/-- Complete child labels are actual parent-sort/phase-bit pairs. -/
abbrev ownerFiniteBaseLabel
    (q : Sigma (OwnerChild S H C P cco I)) : ι × Bit :=
  (q.1.1,q.1.2.val)

/-- Erasing the new child labels retains every FULL original name. -/
theorem owner_project_tagged
    {p q x y : Sigma (OwnerChild S H C P cco I)}
    (h : taggedColour (owner_child_source S H ap C P cco I) p q =
      taggedColour (owner_child_source S H ap C P cco I) x y) :
    taggedColour S ((ownerProjection S H ap C P cco I).project p)
      ((ownerProjection S H ap C P cco I).project q) =
    taggedColour S ((ownerProjection S H ap C P cco I).project x)
      ((ownerProjection S H ap C P cco I).project y) := by
  let erase : (Σ c, Σ d, Option ((owner_child_source S H ap C P cco I).Atom c d)) →
      Age.Colour S := fun a => ⟨a.1.1,a.2.1.1,a.2.2.map Subtype.val⟩
  have he := congrArg erase h
  have et (p q : Sigma (OwnerChild S H C P cco I)) :
      erase (taggedColour (owner_child_source S H ap C P cco I) p q) =
        taggedColour S ((ownerProjection S H ap C P cco I).project p)
          ((ownerProjection S H ap C P cco I).project q) := by
    rcases p with ⟨c,p⟩
    rcases q with ⟨d,q⟩
    change (⟨c.1,d.1,(Rank.colour S _ _ p q).map Subtype.val⟩ : Age.Colour S) =
      ⟨c.1,d.1,S.colour p.val q.val⟩
    rw [Rank.colour_map]
  exact (et p q).symm.trans (he.trans (et x y))

/-- Child names and complete old pair names determine the full new
pair name; this uses the actual occurring-colour subtype. -/
theorem owner_tagged_of_old_and_labels
    {p q x y : Sigma (OwnerChild S H C P cco I)}
    (hp : ownerFiniteBaseLabel S H C P cco I p = ownerFiniteBaseLabel S H C P cco I x)
    (hq : ownerFiniteBaseLabel S H C P cco I q = ownerFiniteBaseLabel S H C P cco I y)
    (hc : taggedColour S ((ownerProjection S H ap C P cco I).project p)
      ((ownerProjection S H ap C P cco I).project q) =
      taggedColour S ((ownerProjection S H ap C P cco I).project x)
        ((ownerProjection S H ap C P cco I).project y)) :
    taggedColour (owner_child_source S H ap C P cco I) p q =
      taggedColour (owner_child_source S H ap C P cco I) x y := by
  have hp' : p.1 = x.1 := UnarySource.childLabel_injective I hp
  have hq' : q.1 = y.1 := UnarySource.childLabel_injective I hq
  rcases p with ⟨c,p⟩
  rcases q with ⟨d,q⟩
  rcases x with ⟨e,x⟩
  rcases y with ⟨f,y⟩
  dsimp only at hp' hq'
  subst e
  subst f
  apply congrArg (fun z => (⟨c,d,z⟩ : Σ c, Σ d,
    Option ((owner_child_source S H ap C P cco I).Atom c d)))
  apply (Option.map_injective Subtype.val_injective)
  have hc' : S.colour p.val q.val = S.colour x.val y.val := by
    change (⟨c.1,d.1,S.colour p.val q.val⟩ : Age.Colour S) =
      ⟨c.1,d.1,S.colour x.val y.val⟩ at hc
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hc
  change (Rank.colour S _ _ p q).map Subtype.val = (Rank.colour S _ _ x y).map Subtype.val
  rw [Rank.colour_map,Rank.colour_map]
  exact hc'

/-- Every actual finite old owner diagram with legal clone-zero bits is
realized in the SAME B047 owner expansion. All bits and all old fine
colours belong to one whole marked-age embedding. -/
theorem owner_marked_age_embeds {V : Type} [Finite V]
    (point : V → Sigma X) (bits : V → Bit)
    (hinj : Function.Injective point)
    (hlegal : Age.Legal (CloneSAP.source S) P.masks
      (zeroClonePoint ∘ point) bits) :
    ∃ f : V ↪ Sigma (OwnerChild S H C P cco I),
      (∀ x, ownerFiniteBaseLabel S H C P cco I (f x) = ((point x).1,bits x)) ∧
      ∀ x y, taggedColour S ((ownerProjection S H ap C P cco I).project (f x))
        ((ownerProjection S H ap C P cco I).project (f y)) =
          taggedColour S (point x) (point y) := by
  obtain ⟨e,heO,heC⟩ := Age.embed_realized (CloneSAP.source S)
    (CloneSAP.homogeneous S H) (P.completion_property (CloneSAP.CCO.cco_forward S cco))
    (zeroClonePoint ∘ point) bits (zeroClonePoint_injective.comp hinj) hlegal
  let rr (x : V) := (UnarySource.newEquiv I).symm (e x)
  let out (x : V) := markedOwnerDrop S H ap C P cco I (rr x)
  have hr (x : V) : I.equiv (UnarySource.oldEquiv I (rr x)) = e x :=
    (UnarySource.newEquiv I).apply_symm_apply _
  have hproj (x : UnarySource.NewPoint
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) :
      (actualProjection
        (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).project x =
      UnarySource.oldEquiv
        (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I x := rfl
  have hn (x y : V) :
      taggedColour (CloneSAP.source S)
        (UnarySource.oldEquiv I (rr x)) (UnarySource.oldEquiv I (rr y)) =
        taggedColour (CloneSAP.source S) (zeroClonePoint (point x)) (zeroClonePoint (point y)) := by
    apply (Age.colourEquiv (CloneSAP.source S)).injective
    calc
      _ = (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour (e x) (e y) := by
        have hh := (UnarySource.colour_eq
          (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco))
          I (UnarySource.oldEquiv I (rr x))
          (UnarySource.oldEquiv I (rr y))).symm
        rw [hr x,hr y] at hh
        exact hh
      _ = _ := heC x y
  have hOld (x y : V) :
      taggedColour S ((ownerProjection S H ap C P cco I).project (out x))
        ((ownerProjection S H ap C P cco I).project (out y)) =
          taggedColour S (point x) (point y) := by
    simpa only [out,markedOwnerDrop_project,hproj,owner_zeroClonePoint] using
      CloneSAP.tagged_owner_eq S (hn x y)
  have hout : Function.Injective out := by
    intro x y he
    apply hinj
    apply (CloneSAP.tagged_diagonal S (hOld x y)).mp
    exact congrArg (ownerProjection S H ap C P cco I).project he
  refine ⟨⟨out,hout⟩,?_,hOld⟩
  intro x
  apply (Age.ownerEquiv (CloneSAP.source S)).injective
  have hnew := UnarySource.new_owner I (rr x)
  have hEO := heO x
  change (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
      (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.owner (e x) =
      Age.ownerEquiv (CloneSAP.source S) ((point x).1,bits x) at hEO
  exact hnew.symm.trans (by
    simpa only [rr,Equiv.apply_symm_apply] using hEO)

end
end CCO.CloneTupleGeometry
