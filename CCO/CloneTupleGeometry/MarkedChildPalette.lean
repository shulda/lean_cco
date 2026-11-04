import CCO.CloneTupleGeometry.MarkedOldAtomWitness
import CCO.CloneTupleGeometry.MarkedCloneColours

/-!
# B060 N02: full actual marked-child atom palette classification

In the actual B047 homogeneous marked successor of a B045 pure-clone
source, every occurring atom is either a tagged ORIGINAL fine atom
of the genuine owner child or the clone marker of ONE and the SAME
child sort. The latter is never a colour between two different child
bits, even if they originate in the same old named sort.

This classifies the entire actual child atomic palette, not a
hypothetical unary expansion and not a bare equality/Top reduct.
A pointwise colour-isomorphism of the two complete atomic sources
will be assembled separately; no source-isomorphism is asserted here.
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
/-- In the true B047 marked child, any occurrence of the actual
B045 clone marker forces equality of the FULL target child labels,
not merely equality of their original parent named sorts. -/
theorem marked_clone_atom_forces_same_child
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (e : (UnarySource.source
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I).Atom c d)
    (h : ∃ t : PLift (c.1 = d.1), e.val = Sum.inr t) :
    c = d := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨x,y,hxy⟩ := e.property
  have hc : (CloneSAP.source S).colour x.val y.val = some (Sum.inr t) := by
    simpa only [ht] using hxy
  have howner :
      (⟨c.1,x.val.1⟩ : Sigma X) = ⟨d.1,y.val.1⟩ :=
    ((CloneSAP.colour_clone_iff S x.val y.val t).mp hc).1
  rcases c with ⟨i,ε⟩
  rcases d with ⟨j,η⟩
  rcases t with ⟨hij⟩
  subst j
  have hsame : x.val.1 = y.val.1 := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using howner
  have hbits : ε = η :=
    marked_owner_equal_child_bits S H ap C P cco I i ε η x y hsame
  cases hbits
  rfl

include ap in
/-- The real B047 clone marker exists between two child sorts IFF
the FULL child sort labels are identical. This is the missing
cross-child gate check; same parent sort with differing bit is NOT
sufficient. -/
theorem marked_clone_atom_exists_iff
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)) :
    (∃ e : (UnarySource.source
       (completion := P.completion_property
         (CloneSAP.CCO.cco_forward S cco)) I).Atom c d,
       ∃ t : PLift (c.1 = d.1), e.val = Sum.inr t) ↔
      c = d := by
  constructor
  · rintro ⟨e,h⟩
    exact marked_clone_atom_forces_same_child S H ap C P cco I e h
  · intro h
    subst d
    obtain ⟨e,he⟩ := marked_child_has_clone_atom S H ap C P cco I c
    exact ⟨e,⟨⟨rfl⟩,he⟩⟩

include ap in
/-- Every REAL occurring B047 marked-child atom is accounted for
by either one old owner fine atom or the uniquely possible same-child
clone marker; no third binary colour can occur. -/
theorem marked_child_full_atom_classification
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I))
    (e : (UnarySource.source
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I).Atom c d) :
    (∃ a : (owner_child_source S H ap C P cco I).Atom c d,
       e.val = Sum.inl a.val) ∨
    (c = d ∧ ∃ t : PLift (c.1 = d.1), e.val = Sum.inr t) := by
  cases h : e.val with
  | inl u =>
      left
      have hold : APCharacter.Rank.Occurs
          (CloneSAP.source S)
          (UnarySource.β (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I)
          (UnarySource.tag (completion := P.completion_property
            (CloneSAP.CCO.cco_forward S cco)) I)
          c d (Sum.inl u) := by
        simpa only [h] using e.property
      have howner := (marked_old_atom_occurs_iff
        S H ap C P cco I c d u).mp hold
      exact ⟨⟨u,howner⟩,h⟩
  | inr t =>
      right
      exact ⟨marked_clone_atom_forces_same_child
        S H ap C P cco I e ⟨t,h⟩,t,h⟩

include ap in
/-- Conversely, every actually occurring original owner-child atom
appears in the real marked successor as its original B045 fine tag.
No artificial owner colour or empty occurring atom is added. -/
theorem marked_owner_atom_occurs
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I))
    (a : (owner_child_source S H ap C P cco I).Atom c d) :
    ∃ e : (UnarySource.source
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I).Atom c d,
      e.val = Sum.inl a.val := by
  have hold := (marked_old_atom_occurs_iff
    S H ap C P cco I c d a.val).mpr a.property
  exact ⟨⟨Sum.inl a.val,hold⟩,rfl⟩

end
end CCO.CloneTupleGeometry
