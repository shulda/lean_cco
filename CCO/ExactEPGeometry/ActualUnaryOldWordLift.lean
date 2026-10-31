import CCO.ExactEPGeometry.ActualUnaryExactTrace

/-!
# B062 C23: lift a REAL original RAW walk through actual child sorts

A canonical AP-character unary refinement has genuinely defined children
`(i,tag x)` for every ORIGINAL old point x. Each old walk witness carries
its actual intermediate old vertices; assigning to each its unique child
tag gives one correctly typed CURRENT RAW word. Its forgetting is
LITERALLY the original word, and the same real witness lives in the
current word profile.

The displayed child for an intermediate point is NOT chosen formally or
via a quotient section. Atomic child names are genuine occurring-colour
subtypes with an actual pair witness. Equality letters remain equality.
This is the pointwise/constructive old-to-current direction of C23, before
the source C24 full relation equality across an entire marked child pair.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryOldWordLift

open APCharacter APCharacter.SourceAge

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {M : MaskData S} {completion : Age.CompletionProperty S M}
variable (I : SourceAge.UnarySource.Identification S H completion)

/-- The ACTUAL canonical child sort of one original point. -/
def childOf {i : ι} (x : X i) :
    Rank.Child (SourceAge.UnarySource.β I) :=
  ⟨i,SourceAge.UnarySource.tag I i x⟩

/-- The very same original real point, as an actual member of its unique
canonical unary child. -/
def pointOf {i : ι} (x : X i) :
    Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I)
      (childOf I x) :=
  ⟨x,rfl⟩

/-- Every original ACTUAL RAW walk with a fixed pair of endpoints gives
one current child-labelled word with exactly the same old letters and
an ACTUAL witnessed middle point of the specified current child at each
atom step. The formal identity letter is retained literally. -/
theorem lift_old_word_with_witness :
    ∀ {i j : ι} (W : RawWord S i j) (x : X i) (z : X j),
      RawWord.relation S W x z →
      ∃ V : RawWord (SourceAge.UnarySource.source I)
          (childOf I x) (childOf I z),
        ProjectedWords.forgetWord S (SourceAge.UnarySource.source I)
          (SourceAge.actualProjection I) V = W ∧
        RawWord.relation (SourceAge.UnarySource.source I) V
          (pointOf I x) (pointOf I z) := by
  intro i j W
  induction W with
  | nil i =>
      intro x z hxz
      change x = z at hxz
      subst z
      exact ⟨.nil (childOf I x),rfl,rfl⟩
  | identity tail ih =>
      intro x z h
      obtain ⟨V,hV,hw⟩ := ih x z h
      refine ⟨.identity V, ?_, hw⟩
      exact congrArg RawWord.identity hV
  | @atom i j k a tail ih =>
      intro x z h
      obtain ⟨y,hxy,hyz⟩ := h
      obtain ⟨V,hV,hWalk⟩ := ih y z hyz
      let T := SourceAge.UnarySource.source I
      let cx := childOf I x
      let cy := childOf I y
      let x' : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) cx := pointOf I x
      let y' : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) cy := pointOf I y
      let a' : T.Atom cx cy :=
        ⟨a,⟨x',y',hxy⟩⟩
      have ha : T.atomRel a' x' y' := by
        change Rank.colour S (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) x' y' = some a'
        exact (Rank.colour_some_iff S
          (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I)
          x' y' a').mpr hxy
      refine ⟨.atom a' V, ?_, ⟨y',ha,hWalk⟩⟩
      change RawWord.atom a
        (ProjectedWords.forgetWord S T (SourceAge.actualProjection I) V) =
          RawWord.atom a tail
      rw [hV]
      rfl


/-- Lift an actual old RAW walk between the SPECIFIED current child endpoints.
Unlike the canonical `childOf` version, this keeps the endpoint bits as
indexed parameters throughout induction; no dependent equality transport of
word indices or additional marking axiom is needed. -/
theorem lift_old_word_with_fixed_bits :
    ∀ {i j : ι} (W : RawWord S i j)
      (bc : SourceAge.UnarySource.β I i)
      (bd : SourceAge.UnarySource.β I j)
      (x : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) ⟨i,bc⟩)
      (z : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) ⟨j,bd⟩),
      RawWord.relation S W x.val z.val →
      ∃ V : RawWord (SourceAge.UnarySource.source I) ⟨i,bc⟩ ⟨j,bd⟩,
        ProjectedWords.forgetWord S (SourceAge.UnarySource.source I)
          (SourceAge.actualProjection I) V = W ∧
        RawWord.relation (SourceAge.UnarySource.source I) V x z := by
  intro i j W
  induction W with
  | nil i =>
      intro bc bd x z hxz
      have hBit : bc = bd := by
        have ht := congrArg (SourceAge.UnarySource.tag I i) hxz
        exact x.property.symm.trans (ht.trans z.property)
      subst bd
      refine ⟨RawWord.nil (⟨i,bc⟩ :
        Rank.Child (SourceAge.UnarySource.β I)), ?_, ?_⟩
      · rfl
      · change x = z
        exact Subtype.ext hxz
  | identity tail ih =>
      intro bc bd x z h
      obtain ⟨V,hV,hw⟩ := ih bc bd x z h
      refine ⟨.identity V, ?_, hw⟩
      exact congrArg RawWord.identity hV
  | @atom i j k a tail ih =>
      intro bc bd x z h
      obtain ⟨y,hxy,hyz⟩ := h
      let byTag := SourceAge.UnarySource.tag I j y
      let y' : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) ⟨j,byTag⟩ := ⟨y,rfl⟩
      obtain ⟨V,hV,hWalk⟩ := ih byTag bd y' z hyz
      let T := SourceAge.UnarySource.source I
      let a' : T.Atom ⟨i,bc⟩ ⟨j,byTag⟩ :=
        ⟨a,⟨x,y',hxy⟩⟩
      have ha : T.atomRel a' x y' := by
        change Rank.colour S (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) x y' = some a'
        exact (Rank.colour_some_iff S
          (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I)
          x y' a').mpr hxy
      refine ⟨.atom a' V, ?_, ⟨y',ha,hWalk⟩⟩
      change RawWord.atom a
        (ProjectedWords.forgetWord S T (SourceAge.actualProjection I) V) =
          RawWord.atom a tail
      rw [hV]
      rfl

end
end CCO.ExactEPGeometry.ActualUnaryOldWordLift
