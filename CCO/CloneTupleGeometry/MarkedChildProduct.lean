import CCO.CloneTupleGeometry.CharacterCloneGates
import CCO.APCharacter.SourceAge.Identification
import CCO.CloneSAP.CCO.Cycles

/-!
# B060 one actual homogeneous marked successor: owner-by-clone carriers

This is the real B047 marked-limit/back-and-forth source, not a chosen
unconstrained unary labelling. The actual global source-phase masks from the
proved identification are constant on clone fibres by CharacterCloneGates.
Hence every REAL successor child sort has its carrier canonically equivalent
to the induced owner child carrier times N, with no point-dependent choices.

The old fine pair colours are preserved through the literal child source.
An isomorphism of the entire successor coloured source with the pure clone
of the owner source, its SAP/CCO, iteration through the selected finite tower,
and infinite owner child types remain separate receiving obligations.
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

/-- The REAL B047 marked limit's old-reduct identification type,
with the entire complete source character masks. -/
abbrev CloneMarkedIdentification :=
  UnarySource.Identification (CloneSAP.source S) (CloneSAP.homogeneous S H)
    (P.completion_property (CloneSAP.CCO.cco_forward S cco))

/-- Build the actual identification from B047's reasonableness, global
marked completion and countable back-and-forth. It is not a supplied
identification or a new source hypothesis. -/
noncomputable def actualCloneIdentification [∀ i, Countable (X i)] :
    CloneMarkedIdentification S H C P cco := by
  letI : ∀ i : ι, Countable (CloneSAP.Carrier X i) := by
    intro i
    infer_instance
  exact APCharacter.SourceAge.actualIdentification P
    (CloneSAP.CCO.cco_forward S cco)

/-- Actual owner-side tag of the homogeneous marked child. It is
evaluated at a literal clone indexed zero, and its independence from
the clone index is proved below. -/
def ownerChildTag
    (I : CloneMarkedIdentification S H C P cco)
    (i : ι) (q : X i) : UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I i :=
  UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I i (q,0)

/-- In the actual homogeneous marked limit, child tags are independent
of the clone index. This uses the TRUE global masks inherited from its
finite marked age and the proved reachable-gate clone saturation. -/
include ap in
theorem marked_child_tag_fibre
    (I : CloneMarkedIdentification S H C P cco)
    (i : ι) (q : X i) (n : ℕ) :
    UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I i (q,n) = ownerChildTag S H C P cco I i q := by
  apply Subtype.ext
  exact pure_clone_character_marking_fibre_const S H ap C P
    (UnarySource.mark (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.global_marking (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) i q n 0

/-- Owner part of the REAL source's actual child type. -/
abbrev OwnerChild
    (I : CloneMarkedIdentification S H C P cco)
    (c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)) :=
  {q : X c.1 // ownerChildTag S H C P cco I c.1 q = c.2}

/-- The literal marked-limit child carrier is the owner child
times the unchanged infinite clone index. This is a concrete
bijection of the REAL successor's points, not a conditional
claim that arbitrary unary splits preserve clone fibres. -/
include ap in
noncomputable def marked_child_equiv
    (I : CloneMarkedIdentification S H C P cco)
    (c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)) :
    APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) c ≃
      OwnerChild S H C P cco I c × ℕ where
  toFun x :=
    (⟨x.val.1, (marked_child_tag_fibre S H ap C P cco I c.1 x.val.1 x.val.2).symm.trans
      x.property⟩,x.val.2)
  invFun x :=
    ⟨(x.1.val,x.2),
      (marked_child_tag_fibre S H ap C P cco I c.1 x.1.val x.2).trans x.1.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

/-- Every owner-side child sort of the ACTUAL homogeneous marked
successor is inhabited, derived from its actual singleton chart. -/
include ap in
theorem owner_child_nonempty
    (I : CloneMarkedIdentification S H C P cco)
    (c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)) :
    Nonempty (OwnerChild S H C P cco I c) := by
  obtain ⟨x⟩ := UnarySource.inhabited (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I c
  exact ⟨(marked_child_equiv S H ap C P cco I c x).1⟩

/-- The actual finite atomic owner-side reduct of the marked successor
has all its colours realized, rather than invented empty child sorts. -/
include ap in
noncomputable def owner_child_source
    (I : CloneMarkedIdentification S H C P cco) :
    AtomicSource (APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I))
      (OwnerChild S H C P cco I) := by
  letI : ∀ i : ι, Fintype (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I i) := by
    intro i
    infer_instance
  exact APCharacter.Rank.source S (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)
    (ownerChildTag S H C P cco I)
    (owner_child_nonempty S H ap C P cco I)

/-- Every old original fine pair colour on two actual marked
successor child points is literally preserved when we forget
the child-colour subtype and erase the pure-clone marker.
This includes mixed named sorts and real diagonal equality. -/
theorem marked_child_original_colour
    (I : CloneMarkedIdentification S H C P cco)
    {a b : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) a)
    (y : APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) b) :
    (((UnarySource.source (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I).colour x y).map Subtype.val).bind
        (CloneSAP.eraseAtom S) = S.colour x.val.1 y.val.1 := by
  rw [APCharacter.Rank.colour_map]
  exact CloneSAP.colour_erase S x.val y.val

/-- A concrete source identification and the genuine child-carrier
product equivalences, together in ONE actual source instance. -/
include ap in
theorem actual_marked_clone_child_products
    [∀ i, Countable (X i)] :
    ∃ I : CloneMarkedIdentification S H C P cco,
      ∀ c : APCharacter.Rank.Child (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I),
        Nonempty (APCharacter.Rank.Point (UnarySource.β (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)
          (UnarySource.tag (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I) c ≃ OwnerChild S H C P cco I c × ℕ) := by
  let I := actualCloneIdentification S H C P cco
  exact ⟨I,fun c => ⟨marked_child_equiv S H ap C P cco I c⟩⟩

end
end CCO.CloneTupleGeometry
