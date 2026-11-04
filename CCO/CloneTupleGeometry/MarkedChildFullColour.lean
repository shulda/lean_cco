import CCO.CloneTupleGeometry.MarkedChildColourReadout

/-!
# B060 N02: exact full optional pair-colour transport

The genuine B047 marked successor's complete binary pair colour is
exactly the image, under the ACTUAL occurring-atom equivalence,
of the pure clone of the actual owner child source's complete colour.
This includes old fine atoms on mixed child sorts, the unique clone
marker on one complete child sort, and the logical diagonal `none`.

This is pointwise colour equality, not merely equal realized atom
palettes or a colour-preserving assumption about some abstract split.
It uses the source's actual identification, marked child carrier
bijections and literal atom maps. Whole source isomorphism and finite
terminal iteration are subsequent obligations.
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
/-- Exact atomic witness transport for any two ACTUAL child sorts,
including different parent sorts and different valid phase bits.
The conclusion uses real occurrences of the marked successor atom. -/
theorem marked_full_colour_some_iff
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
    (a : OwnerCloneChildAtom S H ap C P cco I c d) :
    (UnarySource.source
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I).colour x y =
      some (ownerCloneAtomToMarked S H ap C P cco I a) ↔
    (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
      (marked_child_equiv S H ap C P cco I c x)
      (marked_child_equiv S H ap C P cco I d y) = some a := by
  classical
  cases a with
  | inl u =>
      have hcode :=
        ownerCloneAtomToMarked_code S H ap C P cco I (Sum.inl u)
      have hrel :=
        marked_child_old_pair_colour_iff S H ap C P cco I x y u
      constructor
      · intro h
        exact hrel.mp ⟨_, hcode, h⟩
      · intro h
        obtain ⟨e,he,hcol⟩ := hrel.mpr h
        have heq : e = ownerCloneAtomToMarked S H ap C P cco I (Sum.inl u) :=
          Subtype.ext (he.trans hcode.symm)
        exact heq ▸ hcol
  | inr h =>
      cases h.down
      have hcode :=
        ownerCloneAtomToMarked_code S H ap C P cco I (Sum.inr ⟨rfl⟩)
      have hrel :=
        marked_child_clone_pair_colour_iff S H ap C P cco I x y
      constructor
      · intro h
        exact hrel.mp ⟨_, hcode, h⟩
      · intro h
        obtain ⟨e,he,hcol⟩ := hrel.mpr h
        have heq : e = ownerCloneAtomToMarked S H ap C P cco I (Sum.inr ⟨rfl⟩) :=
          Subtype.ext (he.trans hcode.symm)
        exact heq ▸ hcol

include ap in
/-- Full optional atomic colour transport at the TRUE B047 current
marked successor. This includes logical equality as `none`, and
all mixed child sorts and all old/clone diversity colours. -/
theorem marked_full_colour_transport
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
          (CloneSAP.CCO.cco_forward S cco)) I) d) :
    (UnarySource.source
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I).colour x y =
    ((CloneSAP.source (owner_child_source S H ap C P cco I)).colour
      (marked_child_equiv S H ap C P cco I c x)
      (marked_child_equiv S H ap C P cco I d y)).map
      (ownerCloneAtomToMarked S H ap C P cco I) := by
  classical
  cases hR :
      (CloneSAP.source (owner_child_source S H ap C P cco I)).colour
        (marked_child_equiv S H ap C P cco I c x)
        (marked_child_equiv S H ap C P cco I d y) with
  | none =>
      cases hL :
          (UnarySource.source
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I).colour x y with
      | none =>
          simp only [hL,hR,Option.map_none]
      | some e =>
          obtain ⟨a,ha⟩ :=
            ownerCloneAtomToMarked_surjective S H ap C P cco I e
          have hsome :
              (UnarySource.source
                (completion := P.completion_property
                  (CloneSAP.CCO.cco_forward S cco)) I).colour x y =
                some (ownerCloneAtomToMarked S H ap C P cco I a) := by
            simpa only [ha] using hL
          have hr :=
            (marked_full_colour_some_iff S H ap C P cco I x y a).mp hsome
          rw [hR] at hr
          cases hr
  | some a =>
      have hl :
          (UnarySource.source
            (completion := P.completion_property
              (CloneSAP.CCO.cco_forward S cco)) I).colour x y =
              some (ownerCloneAtomToMarked S H ap C P cco I a) :=
        (marked_full_colour_some_iff S H ap C P cco I x y a).mpr hR
      simpa only [hR,Option.map_some] using hl

end
end CCO.CloneTupleGeometry
