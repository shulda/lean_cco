import CCO.CloneTupleGeometry.MarkedChildAtomEquiv

/-!
# B060 N02: pointwise old and clone colour readout in the genuine child

The actual B047 marked successor's complete old fine-atom predicates,
on any two named child sorts, agree with the pure clone of the actual
owner child source under the genuine owner-by-clone carrier bijections.
On same-child pairs, the true clone atom also agrees exactly.

These two literal pointwise iff statements contain no quotient
sections, presumed source isomorphisms, hidden SAP or arbitrary unary
label hypotheses. Full option-valued colour equality using the
already proved atom equivalences remains the next step.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter
open APCharacter.SourceAge
open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include ap in
/-- On ANY pair of real B047 child sorts, occurrence of one
particular original owner fine atom on two points agrees exactly
with that atom between the corresponding pure-clone owner points.
This includes mixed old named sorts and actual diagonal equality. -/
theorem marked_child_old_pair_colour_iff
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : APCharacter.Rank.Point (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)
      (UnarySource.tag
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I) c)
    (y : APCharacter.Rank.Point (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)
      (UnarySource.tag
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I) d)
    (a : (owner_child_source S H ap C P cco I).Atom c d) :
    (∃ e : MarkedChildAtom S H C P cco I c d,
      e.val = Sum.inl a.val ∧
        (UnarySource.source
          (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I).colour x y = some e) ↔
      (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
        (marked_child_equiv S H ap C P cco I c x)
        (marked_child_equiv S H ap C P cco I d y) =
          some (Sum.inl a) := by
  have hOld :
      (∃ e : MarkedChildAtom S H C P cco I c d,
        e.val = Sum.inl a.val ∧
          (UnarySource.source
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I).colour x y = some e) ↔
        S.colour x.val.1 y.val.1 = some a.val :=
    marked_child_old_colour_iff S H C P cco I x y a.val
  have hOwner :
      (owner_child_source S H ap C P cco I).colour
        (marked_child_equiv S H ap C P cco I c x).1
        (marked_child_equiv S H ap C P cco I d y).1 = some a ↔
      S.colour x.val.1 y.val.1 = some a.val := by
    exact APCharacter.Rank.colour_some_iff
      S (UnarySource.β (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)
      (ownerChildTag S H C P cco I)
      (marked_child_equiv S H ap C P cco I c x).1
      (marked_child_equiv S H ap C P cco I d y).1 a
  have hClone :
      (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
        (marked_child_equiv S H ap C P cco I c x)
        (marked_child_equiv S H ap C P cco I d y) =
          some (Sum.inl a) ↔
      (owner_child_source S H ap C P cco I).colour
        (marked_child_equiv S H ap C P cco I c x).1
        (marked_child_equiv S H ap C P cco I d y).1 = some a :=
    CloneSAP.colour_old_iff
      (owner_child_source S H ap C P cco I)
      (marked_child_equiv S H ap C P cco I c x)
      (marked_child_equiv S H ap C P cco I d y) a
  exact hOld.trans (hOwner.symm.trans hClone.symm)

include ap in
/-- On a genuine SAME full child sort, the clone marker connects
exactly two distinct clone indices of one old owner, both in the
actual B047 marked successor and in the pure clone of its owner
child. The comparison does not identify different child labels. -/
theorem marked_child_clone_pair_colour_iff
    (I : CloneMarkedIdentification S H C P cco)
    {c : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (x y : APCharacter.Rank.Point (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)
      (UnarySource.tag
        (completion := P.completion_property
          (CloneSAP.CCO.cco_forward S cco)) I) c) :
    (∃ e : MarkedChildAtom S H C P cco I c c,
      e.val = Sum.inr ⟨rfl⟩ ∧
        (UnarySource.source
          (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I).colour x y = some e) ↔
      (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
        (marked_child_equiv S H ap C P cco I c x)
        (marked_child_equiv S H ap C P cco I c y) =
          some (Sum.inr ⟨rfl⟩) := by
  have hOld :
      (∃ e : MarkedChildAtom S H C P cco I c c,
        e.val = Sum.inr ⟨rfl⟩ ∧
          (UnarySource.source
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I).colour x y = some e) ↔
        x.val.1 = y.val.1 ∧ x.val.2 ≠ y.val.2 :=
    marked_child_clone_colour_iff S H C P cco I x y
  have hClone :
      (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
        (marked_child_equiv S H ap C P cco I c x)
        (marked_child_equiv S H ap C P cco I c y) =
          some (Sum.inr ⟨rfl⟩) ↔
        (marked_child_equiv S H ap C P cco I c x).1 =
          (marked_child_equiv S H ap C P cco I c y).1 ∧
        (marked_child_equiv S H ap C P cco I c x).2 ≠
          (marked_child_equiv S H ap C P cco I c y).2 :=
    CloneSAP.source_clone_iff
      (owner_child_source S H ap C P cco I)
      (marked_child_equiv S H ap C P cco I c x)
      (marked_child_equiv S H ap C P cco I c y)
  have hBridge :
      (x.val.1 = y.val.1 ∧ x.val.2 ≠ y.val.2) ↔
        ((marked_child_equiv S H ap C P cco I c x).1 =
           (marked_child_equiv S H ap C P cco I c y).1 ∧
         (marked_child_equiv S H ap C P cco I c x).2 ≠
           (marked_child_equiv S H ap C P cco I c y).2) := by
    constructor
    · rintro ⟨howner,hidx⟩
      exact ⟨Subtype.ext howner,hidx⟩
    · rintro ⟨howner,hidx⟩
      exact ⟨congrArg Subtype.val howner,hidx⟩
  exact hOld.trans (hBridge.trans hClone.symm)

end
end CCO.CloneTupleGeometry
