import CCO.CloneTupleGeometry.MarkedChildPalette

/-!
# B060 N02: literal atom equivalence for the actual B047 clone successor

The actual marked child's occurring atom type is canonically in
bijection with the pure clone of the actual owner child source:
* original owner fine atoms map to their old B045 tag;
* the unique same-complete-child clone marker maps to its occurring
  B047 clone atom.

Both directions use the proved REAL marked child palette and its
literal occurrence witnesses. No abstract clone-sort hypothesis or
new source-level quotient action is imposed.

The point equivalences and exact binary-colour preservation, which
will yield a whole coloured-source isomorphism, are separate steps.
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

/-- The genuine marked successor's occurring atom type. -/
abbrev MarkedChildAtom
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)) :=
  (UnarySource.source (completion := P.completion_property
    (CloneSAP.CCO.cco_forward S cco)) I).Atom c d

/-- Literal pure clone of the genuine old-owner child source's atom type. -/
abbrev OwnerCloneChildAtom
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)) :=
  (CloneSAP.source (owner_child_source S H ap C P cco I)).Atom c d

/-- The B045 old tag of an owner atom, or the parent-sort projection
of the complete-child equality witnessing the new clone atom. -/
def ownerCloneChildAtomCode
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (a : OwnerCloneChildAtom S H ap C P cco I c d) :
    (CloneSAP.source S).Atom c.1 d.1 :=
  match a with
  | .inl u => .inl u.val
  | .inr h => .inr ⟨congrArg Sigma.fst h.down⟩

/-- The above literal code loses no original fine atom and no
same-child clone marker: equality proofs are irrelevant but the
OLD occurring atom names are retained injectively. -/
theorem ownerCloneChildAtomCode_injective
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)} :
    Function.Injective (ownerCloneChildAtomCode S H ap C P cco I
      (c := c) (d := d)) := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have h : a.val = b.val := Sum.inl.inj hab
          exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
          cases hab
  | inr a =>
      cases b with
      | inl b =>
          cases hab
      | inr b =>
          exact congrArg Sum.inr (Subsingleton.elim a b)

include ap in
/-- Every actual atom of the pure clone over the actual owner child
is realized by an atom of the TRUE marked successor, without adding
new names. -/
noncomputable def ownerCloneAtomToMarked
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (a : OwnerCloneChildAtom S H ap C P cco I c d) :
    MarkedChildAtom S H C P cco I c d := by
  classical
  cases a with
  | inl a =>
      exact ⟨Sum.inl a.val, (marked_old_atom_occurs_iff
        S H ap C P cco I c d a.val).mpr a.property⟩
  | inr h =>
      cases h.down
      exact Classical.choose (marked_child_has_clone_atom
        S H ap C P cco I c)

include ap in
/-- Explicit verification that the constructed marked atom uses
exactly the original B045 binary tag, not merely a corresponding
abstract palette element. -/
theorem ownerCloneAtomToMarked_code
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)}
    (a : OwnerCloneChildAtom S H ap C P cco I c d) :
    (ownerCloneAtomToMarked S H ap C P cco I a).val =
      ownerCloneChildAtomCode S H ap C P cco I a := by
  classical
  cases a with
  | inl a =>
      rfl
  | inr h =>
      cases h.down
      change (Classical.choose
        (marked_child_has_clone_atom S H ap C P cco I c)).val =
          Sum.inr ⟨rfl⟩
      exact Classical.choose_spec (marked_child_has_clone_atom
        S H ap C P cco I c)

include ap in
theorem ownerCloneAtomToMarked_injective
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)} :
    Function.Injective (ownerCloneAtomToMarked S H ap C P cco I
      (c := c) (d := d)) := by
  intro a b hab
  apply ownerCloneChildAtomCode_injective S H ap C P cco I
  calc
    ownerCloneChildAtomCode S H ap C P cco I a =
        (ownerCloneAtomToMarked S H ap C P cco I a).val :=
      (ownerCloneAtomToMarked_code S H ap C P cco I a).symm
    _ = (ownerCloneAtomToMarked S H ap C P cco I b).val :=
      congrArg Subtype.val hab
    _ = ownerCloneChildAtomCode S H ap C P cco I b :=
      ownerCloneAtomToMarked_code S H ap C P cco I b

include ap in
/-- Surjectivity uses the actual old-atom/clone-atom classification;
in particular it does not assume an arbitrary marked-age expansion
or that a clone marker appears between two differing child bits. -/
theorem ownerCloneAtomToMarked_surjective
    (I : CloneMarkedIdentification S H C P cco)
    {c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)} :
    Function.Surjective (ownerCloneAtomToMarked S H ap C P cco I
      (c := c) (d := d)) := by
  intro e
  rcases marked_child_full_atom_classification S H ap C P cco I c d e with
    ⟨a,ha⟩ | ⟨hcd,t,ht⟩
  · refine ⟨Sum.inl a,?_⟩
    apply Subtype.ext
    calc
      (ownerCloneAtomToMarked S H ap C P cco I (Sum.inl a)).val =
          ownerCloneChildAtomCode S H ap C P cco I (Sum.inl a) :=
        ownerCloneAtomToMarked_code S H ap C P cco I (Sum.inl a)
      _ = e.val := ha.symm
  · cases hcd
    refine ⟨Sum.inr ⟨rfl⟩,?_⟩
    apply Subtype.ext
    calc
      (ownerCloneAtomToMarked S H ap C P cco I (Sum.inr ⟨rfl⟩)).val =
          ownerCloneChildAtomCode S H ap C P cco I (Sum.inr ⟨rfl⟩) :=
        ownerCloneAtomToMarked_code S H ap C P cco I (Sum.inr ⟨rfl⟩)
      _ = e.val := by
        simpa only [ownerCloneChildAtomCode] using ht.symm

include ap in
/-- Genuine bijection of the ENTIRE occurring binary atom palettes
between one B047 marked successor and the pure clone of its actual
owner child source. The whole pointwise colour isomorphism is the
next separate source-level obligation. -/
noncomputable def actualMarkedCloneAtomEquiv
    (I : CloneMarkedIdentification S H C P cco)
    (c d : APCharacter.Rank.Child (UnarySource.β
      (completion := P.completion_property
        (CloneSAP.CCO.cco_forward S cco)) I)) :
    OwnerCloneChildAtom S H ap C P cco I c d ≃
      MarkedChildAtom S H C P cco I c d :=
  Equiv.ofBijective
    (ownerCloneAtomToMarked S H ap C P cco I)
    ⟨ownerCloneAtomToMarked_injective S H ap C P cco I,
      ownerCloneAtomToMarked_surjective S H ap C P cco I⟩

end
end CCO.CloneTupleGeometry
