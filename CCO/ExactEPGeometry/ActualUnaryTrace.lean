import CCO.ExactEPGeometry.ProjectedHistory
import CCO.ExactEPGeometry.MarkedTrace
import CCO.ExactEPGeometry.PeirceEndpoints
import CCO.APCharacter.SourceAge.UnaryTransition

/-!
# B062 C23/C26: actual canonical child atom and identity traces

An accepted AP-character split is the ACTUAL marked Fraïssé limit,
identified by the proved old-reduct equivalence with the original source.
The current children are the genuine nonempty `Rank.Point` subtypes,
not nominal bits. The `SourceAge.actualProjection` retains precisely the
original fine atoms occurring between these children.

For each such current atom, its represented relation is EXACTLY the
real marked trace of its ORIGINAL atomic relation; similarly nil is the
actual equality. This is the base step needed for the two-way C23–C27
word induction. The general word reverse direction remains OPEN and
requires source C22 with nonempty displayed middle traces.

Every exactness witness below is an accepted RAW source presentation,
not a supplied independent provider or a diversity-only identity.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryTrace

open APCharacter
open APCharacter.SourceAge

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {M : MaskData S} {completion : Age.CompletionProperty S M}
variable (I : SourceAge.UnarySource.Identification S H completion)

/-- The real current ordered pair has exactly the original OLD atomic
code of its projected points, including `none` iff the points coincide. -/
theorem real_pair_code
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
    (y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d) :
    (Age.limitCoding S H completion).table.colour
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,y⟩) =
      Age.colourEquiv S (taggedColour S
        (⟨c.1,x.val⟩ : Sigma X) ⟨d.1,y.val⟩) := by
  have h := SourceAge.UnarySource.new_colour I
    (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I)
    (⟨d,y⟩ : SourceAge.UnarySource.NewPoint I)
  rw [SourceAge.UnarySource.erase_tagged I] at h
  exact h

/-- For ANY old invariant typed relation the actual present child pair
satisfies the marked trace iff its PROJECTED ORIGINAL points satisfy that
old relation. Source pair homogeneity supplies the only orbital transport. -/
theorem real_child_trace_iff
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (R : TRel X c.1 d.1) (hInv : TRel.Invariant (G := G) R)
    (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
    (y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d) :
    markedTrace S H completion R c.2.val d.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,y⟩) ↔
      R x.val y.val := by
  constructor
  · rintro ⟨_,_,u,v,huv,hCode⟩
    have hCurrent := real_pair_code I x y
    have hTags : taggedColour S (⟨c.1,x.val⟩ : Sigma X)
        (⟨d.1,y.val⟩ : Sigma X) =
      taggedColour S (⟨c.1,u⟩ : Sigma X) ⟨d.1,v⟩ :=
      (Age.colourEquiv S).injective (hCurrent.symm.trans hCode)
    have hOld : S.colour x.val y.val = S.colour u v := by
      simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and]
        using hTags
    exact invariant_of_same_actual_colour S H R hInv u v huv x.val y.val hOld
  · intro h
    exact ⟨SourceAge.UnarySource.new_owner I ⟨c,x⟩,
      SourceAge.UnarySource.new_owner I ⟨d,y⟩,
      x.val,y.val,h,real_pair_code I x y⟩

/-- C23 base atom: every ACTUAL occurring current fine colour is the
unmodified REAL marked trace of its named old atom. The current name is
a subtype with an actual witness, so no nonoccurring atom is introduced. -/
theorem real_current_atom_iff
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (a : (SourceAge.UnarySource.source I).Atom c d)
    (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
    (y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d) :
    markedTrace S H completion (S.atomRel a.val) c.2.val d.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,y⟩) ↔
      (SourceAge.UnarySource.source I).atomRel a x y := by
  have hInv : TRel.Invariant (G := G) (S.atomRel a.val) := by
    intro g u v huv
    exact (S.colourInvariant_of_homogeneous H g u v).trans huv
  exact (real_child_trace_iff I (S.atomRel a.val) hInv x y).trans
    (ProjectedWords.atom_iff S (SourceAge.UnarySource.source I)
      (SourceAge.actualProjection I) a x y).symm

/-- C23 genuine nil: a zero-length current word is current IDENTITY.
Old `none` is never a diversity atom between distinct current children. -/
theorem real_current_identity_iff
    {c : Rank.Child (SourceAge.UnarySource.β I)}
    (x y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c) :
    markedTrace S H completion (TRel.ident X c.1) c.2.val c.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨c,y⟩) ↔ x = y := by
  rw [markedTrace_identity_iff S H completion c.2.val
    (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
    (SourceAge.UnarySource.newEquiv I ⟨c,y⟩)]
  constructor
  · rintro ⟨h,_⟩
    have he : (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I) = ⟨c,y⟩ :=
      (SourceAge.UnarySource.newEquiv I).injective h
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using he
  · intro h
    subst y
    exact ⟨rfl,SourceAge.UnarySource.new_owner I ⟨c,x⟩⟩

/-- The CURRENT genuine diversity atomic relation is the exact trace of
an ORIGINAL equality-inclusive RAW atomic profile, with its REAL witness
and without appealing to any additional SAP or current word axiom. -/
theorem real_current_atom_old_exact
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (a : (SourceAge.UnarySource.source I).Atom c d) :
    ∃ D : RawExact.NonemptyExact S c.1 d.1,
      ∀ (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
        (y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d),
        markedTrace S H completion (RawExact.evaluate S D.words) c.2.val d.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨d,y⟩) ↔
          (SourceAge.UnarySource.source I).atomRel a x y := by
  refine ⟨RawExact.exactDiversityAtom S a.val, ?_⟩
  intro x y
  rw [RawExact.exactDiversityAtom_relation S a.val]
  exact real_current_atom_iff I a x y

/-- The CURRENT zero-word identity is the trace of ORIGINAL RAW identity
with its actual diagonal witness. The old `NonemptyExact` is constructed
by the accepted original identity-word provider. -/
theorem real_current_identity_old_exact
    {c : Rank.Child (SourceAge.UnarySource.β I)} :
    ∃ D : RawExact.NonemptyExact S c.1 c.1,
      ∀ (x y : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) c),
        markedTrace S H completion (RawExact.evaluate S D.words) c.2.val c.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨c,y⟩) ↔ x = y := by
  refine ⟨RawExact.exactIdentityAtom S c.1, ?_⟩
  intro x y
  rw [RawExact.exactIdentityAtom_relation S c.1]
  exact real_current_identity_iff I x y

/-- Concrete source instance of the forward current exact-profile
projection: the canonically identified AP-character child source has
the ACTUAL `UnaryReduct` projection, so every nonempty current exact
profile has an original nonempty RAW exact witness. Reverse equality
of the full profile is still C24–C27 and is not inferred here. -/
theorem real_current_exact_forget
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (D : RawExact.NonemptyExact (SourceAge.UnarySource.source I) c d) :
    ∃ E : RawExact.NonemptyExact S c.1 d.1,
      ∀ (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
        (y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d),
        RawExact.evaluate (SourceAge.UnarySource.source I) D.words x y →
          RawExact.evaluate S E.words x.val y.val := by
  refine ⟨ProjectedWords.forgetExact S
    (SourceAge.UnarySource.source I) (SourceAge.actualProjection I) D, ?_⟩
  intro x y hxy
  exact ProjectedWords.forgetExact_forward S
    (SourceAge.UnarySource.source I) (SourceAge.actualProjection I) D x y hxy

end CCO.ExactEPGeometry.ActualUnaryTrace
