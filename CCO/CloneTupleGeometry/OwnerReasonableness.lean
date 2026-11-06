import CCO.CloneTupleGeometry.OwnerHomogeneity
import CCO.CloneTupleGeometry.MarkedChildProduct
import CCO.APCharacter.SourceAge.UnaryTransition

/-! The genuine marked-age extension lifts a prescribed owner embedding
on one clone per owner. Descending the resulting fibre-constant child
labels retains that same embedding. The resulting finite-age functor is
reasonable, reduct-surjective and precompact; no owner SAP is asserted. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
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

/-- The actual owner child forgets only its new unary tag. -/
def ownerProjection : Towers.UnaryReduct S (owner_child_source S H ap C P cco I) where
  parent c := c.1
  point _ x := x.val
  atom _ _ a := a.val
  atom_injective _ _ := Subtype.coe_injective
  colour _ _ x y := (Rank.colour_map S _ _ x y).symm
  bijective := by
    refine ⟨Rank.forget_injective _ _,?_⟩
    rintro ⟨i,x⟩
    exact ⟨⟨⟨i,ownerChildTag S H C P cco I i x⟩,⟨x,rfl⟩⟩,rfl⟩

/-- Choose one actual clone of each prescribed owner child. -/
def markedOwnerLift (q : Sigma (OwnerChild S H C P cco I)) :
    Sigma (Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)) :=
  ⟨q.1,⟨(q.2.val,0),
    (marked_child_tag_fibre S H ap C P cco I q.1.1 q.2.val 0).trans q.2.property⟩⟩

/-- The marked source's literal clone product descends back to an owner. -/
def markedOwnerDrop (q : Sigma (Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I))) :
    Sigma (OwnerChild S H C P cco I) :=
  ⟨q.1,(marked_child_equiv S H ap C P cco I q.1 q.2).1⟩

@[simp] theorem markedOwnerDrop_lift (q : Sigma (OwnerChild S H C P cco I)) :
    markedOwnerDrop S H ap C P cco I (markedOwnerLift S H ap C P cco I q) = q := by
  rcases q with ⟨c,q⟩
  rfl

theorem markedOwnerLift_injective : Function.Injective (markedOwnerLift S H ap C P cco I) := by
  intro x y h
  simpa only [markedOwnerDrop_lift] using congrArg (markedOwnerDrop S H ap C P cco I) h

@[simp] theorem markedOwnerLift_project (q : Sigma (OwnerChild S H C P cco I)) :
    (actualProjection (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).project (markedOwnerLift S H ap C P cco I q) =
      zeroClonePoint ((ownerProjection S H ap C P cco I).project q) := rfl

@[simp] theorem markedOwnerDrop_project
    (q : Sigma (Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I))) :
    (ownerProjection S H ap C P cco I).project (markedOwnerDrop S H ap C P cco I q) =
      CloneSAP.owner ((actualProjection (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).project q) := rfl

/-- Extend the SAME finite old owner diagram and its prescribed child
embedding, using the actual global-character marked-age extension. -/
theorem owner_actual_extension :
    FiniteExtension (Towers.UnaryReduct.originalTable (S := S))
      (ownerProjection S H ap C P cco I).projectedTable := by
  intro n m j p q h
  let pC : Fin m ↪ Sigma (CloneSAP.Carrier X) :=
    p.trans ⟨zeroClonePoint,zeroClonePoint_injective⟩
  let qM := q.trans ⟨markedOwnerLift S H ap C P cco I,
    markedOwnerLift_injective S H ap C P cco I⟩
  have ho : ∀ x, (actualProjection (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).projectedTable.owner (qM x) =
      (Towers.UnaryReduct.originalTable (S := CloneSAP.source S)).owner (pC (j x)) :=
    h.1
  have hc : ∀ x y, (actualProjection (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).projectedTable.colour (qM x) (qM y) =
      (Towers.UnaryReduct.originalTable (S := CloneSAP.source S)).colour
        (pC (j x)) (pC (j y)) := by
    intro x y
    change taggedColour (CloneSAP.source S)
      (zeroClonePoint ((ownerProjection S H ap C P cco I).project (q x)))
      (zeroClonePoint ((ownerProjection S H ap C P cco I).project (q y))) =
      taggedColour (CloneSAP.source S) (zeroClonePoint (p (j x))) (zeroClonePoint (p (j y)))
    exact zeroClonePoint_tagged S (h.2 x y)
  obtain ⟨rr,hrO,hrC,hr⟩ := actual_extension (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I P.finite_seed_extension n m j pC qM ⟨ho,hc⟩
  let out : Fin m → Sigma (OwnerChild S H C P cco I) :=
    fun x => markedOwnerDrop S H ap C P cco I (rr x)
  have hnames (x y : Fin m) :
      taggedColour S ((ownerProjection S H ap C P cco I).project (out x))
        ((ownerProjection S H ap C P cco I).project (out y)) =
      taggedColour S (p x) (p y) := by
    exact CloneSAP.tagged_owner_eq S (hrC x y)
  have hout : Function.Injective out := by
    intro x y he
    apply p.injective
    apply (CloneSAP.tagged_diagonal S (hnames x y)).mp
    exact congrArg (ownerProjection S H ap C P cco I).project he
  refine ⟨⟨out,hout⟩,hrO,hnames,?_⟩
  intro x
  change markedOwnerDrop S H ap C P cco I (rr (j x)) = q x
  rw [hr]
  exact markedOwnerDrop_lift S H ap C P cco I (q x)

/-- C11: all three finite unary expansion properties for the literal
owner forgetful functor, including the same-map reasonableness law. -/
def owner_unary_transition : Towers.UnaryTransition
    ⟨Age.Chart S (Age.zeroMask S),Age.chartCategory S (Age.zeroMask S)⟩
    ⟨Age.Chart (owner_child_source S H ap C P cco I)
        (Age.zeroMask (owner_child_source S H ap C P cco I)),
      Age.chartCategory (owner_child_source S H ap C P cco I)
        (Age.zeroMask (owner_child_source S H ap C P cco I))⟩ :=
  (ownerProjection S H ap C P cco I).transition_of_extension
    (owner_actual_extension S H ap C P cco I)

end
end CCO.CloneTupleGeometry
