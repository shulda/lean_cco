import CCO.CloneTupleGeometry.MarkedChildProduct

/-!
# B060 N02: original fine colours survive the ACTUAL marked child split

The actual B047 homogeneous marked-limit identification, not an arbitrary
subtype/label choice, gives each successor child as owner child times N.

For any old fine atom a on any two named sorts (including a same-sort
pair), occurrence of an old-tagged atom in the ACTUAL marked child's atom
palette is equivalent to occurrence of a in the actual owner-side Rank source.
The proof uses both directions of the genuine child-carrier bijection,
and the concrete B045 clone colour theorem. No colour is postulated to
occur or new hidden quotient automorphism group introduced.
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
/-- The old atomic colour is realized between two TRUE successor
child sorts iff it is realized between their owner children.
Both directions use real points with their actual B047 child tags,
not a source-side colour-realization hypothesis. -/
theorem marked_old_atom_occurs_iff
    (I : CloneMarkedIdentification S H C P cco)
    (a b : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I))
    (u : S.Atom a.1 b.1) :
    APCharacter.Rank.Occurs
        (CloneSAP.source S) (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)
        a b (Sum.inl u) ↔
    APCharacter.Rank.Occurs
        S (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (ownerChildTag S H C P cco I)
        a b u := by
  constructor
  · rintro ⟨x,y,hxy⟩
    refine ⟨(marked_child_equiv S H ap C P cco I a x).1,
      (marked_child_equiv S H ap C P cco I b y).1, ?_⟩
    exact (CloneSAP.colour_old_iff S x.val y.val u).mp hxy
  · rintro ⟨x,y,hxy⟩
    let px : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) a :=
      (marked_child_equiv S H ap C P cco I a).symm (x,0)
    let py : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) b :=
      (marked_child_equiv S H ap C P cco I b).symm (y,0)
    refine ⟨px,py,?_⟩
    change (CloneSAP.source S).colour (x.val,0) (y.val,0) = some (Sum.inl u)
    exact (CloneSAP.colour_old_iff S (x.val,0) (y.val,0) u).mpr hxy

include ap in
/-- Equality of original owners forces the marked child labels
to be identical. The proof works for same-sort descendants with
arbitrary different valid character bits; no direct child
equivalence or quotient assumptions are made. -/
theorem marked_owner_equal_child_bits
    (I : CloneMarkedIdentification S H C P cco)
    (i : ι) (ε η : UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I i)
    (x : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) ⟨i,ε⟩)
    (y : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) ⟨i,η⟩)
    (howner : x.val.1 = y.val.1) : ε = η := by
  have hx : ownerChildTag S H C P cco I i x.val.1 = ε :=
    (marked_child_tag_fibre S H ap C P cco I i x.val.1 x.val.2).symm.trans x.property
  have hy : ownerChildTag S H C P cco I i y.val.1 = η :=
    (marked_child_tag_fibre S H ap C P cco I i y.val.1 y.val.2).symm.trans y.property
  have hy' : ownerChildTag S H C P cco I i x.val.1 = η := by
    rw [howner]
    exact hy
  exact hx.symm.trans hy'

end
end CCO.CloneTupleGeometry
