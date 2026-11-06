import CCO.CloneTupleGeometry.MarkedChildProduct

/-!
# B060 successor's real clone diversity atom

The source is the genuine B047 homogeneous marked child, with its
actual old-reduct identification and inherited colour subtypes. Its
new clone marker is an ACTUAL occurring same-sort diversity atom in
EVERY child sort; it occurs exactly on distinct clones of one owner.

This is additional real binary-colour geometry beyond the carrier
bijection. The complete source-level isomorphism, finite tower and
infinite owner-type reconstruction remain separate obligations.
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

/-- Every SAME-SORT clone colour in the actual marked child is
precisely between two distinct clones with one original owner;
the possible matching atom is the REAL occurring subtype of
the genuine original clone marker, not an invented new atom. -/
theorem marked_child_clone_colour_iff
    (I : CloneMarkedIdentification S H C P cco)
    {c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x y : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) c) :
    (∃ e : (UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).Atom c c,
      e.val = Sum.inr ⟨rfl⟩ ∧ (UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).colour x y = some e) ↔
      x.val.1 = y.val.1 ∧ x.val.2 ≠ y.val.2 := by
  constructor
  · rintro ⟨e,he,hcol⟩
    have hc : (CloneSAP.source S).colour x.val y.val = some e.val :=
      (APCharacter.Rank.colour_some_iff
        (CloneSAP.source S) (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)
        (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) x y e).mp hcol
    rw [he] at hc
    exact (CloneSAP.source_clone_iff S x.val y.val).mp hc
  · intro h
    have hc : (CloneSAP.source S).colour x.val y.val =
        some (Sum.inr ⟨rfl⟩) :=
      (CloneSAP.source_clone_iff S x.val y.val).mpr h
    let e : (UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).Atom c c :=
      ⟨Sum.inr ⟨rfl⟩, ⟨x,y,hc⟩⟩
    refine ⟨e,rfl,?_⟩
    exact (APCharacter.Rank.colour_some_iff
      (CloneSAP.source S) (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)
      (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) x y e).mpr hc

include ap in
/-- The new clone marker occurs on every genuine marked successor
sort, regardless of the cardinality of its owner-child fibre.
The two witnessing real points are constructed from the
SAME owner and literal distinct natural-number clone indices. -/
theorem marked_child_has_clone_atom
    (I : CloneMarkedIdentification S H C P cco)
    (c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)) :
    ∃ e : (UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).Atom c c,
      e.val = Sum.inr ⟨rfl⟩ := by
  obtain ⟨q⟩ := owner_child_nonempty S H ap C P cco I c
  let x : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) c :=
    (marked_child_equiv S H ap C P cco I c).symm (q,0)
  let y : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) c :=
    (marked_child_equiv S H ap C P cco I c).symm (q,1)
  have hx : x.val = (q.val,0) := rfl
  have hy : y.val = (q.val,1) := rfl
  have hSame : x.val.1 = y.val.1 ∧ x.val.2 ≠ y.val.2 := by
    rw [hx,hy]
    constructor
    · rfl
    · change (0 : ℕ) ≠ 1
      decide
  have hc : (CloneSAP.source S).colour x.val y.val =
      some (Sum.inr ⟨rfl⟩) :=
    (CloneSAP.source_clone_iff S x.val y.val).mpr hSame
  let e : (UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).Atom c c :=
    ⟨Sum.inr ⟨rfl⟩, ⟨x,y,hc⟩⟩
  exact ⟨e,rfl⟩

end
end CCO.CloneTupleGeometry
