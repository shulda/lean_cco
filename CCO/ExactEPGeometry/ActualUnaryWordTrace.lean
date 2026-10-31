import CCO.ExactEPGeometry.ActualUnaryDecode
import CCO.ExactEPGeometry.TraceProduct

/-!
# B062 C23–C26: exact RAW-word trace at a genuine AP-only child source

The ACCEPTED actual unary refinement is the child source of the entire
homogeneous marked age, with its real old-reduct identification.  A
CURRENT RAW word W carries a fixed child sort at every internal position.
If W is actually nonempty, it is EXACTLY the trace, between its endpoint
children, of the ORIGINAL RAW word obtained by forgetting child labels.

The difficult reverse inclusion uses genuine one-step AP-only C22,
including both nonempty displayed input traces.  The middle marked point
returned by C22 is decoded back into the SAME actual child via the
canonical bijection; no arbitrary old intermediate point or quotient
section is substituted.  Both true identity letters and equality
outputs of positive words are preserved.

This is a one-step represented-word theorem, not yet full finite-meet
exact-domain surjectivity nor arbitrary tower iteration (C27/C28).
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryWordTrace

open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : SourceAge.UnarySource.Identification S H (P.completion_property cco))

/-- For a genuinely nonempty CURRENT word, its full endpoint relation
equals the ACTUAL output-age trace of its exact ORIGINAL word.  Every
intermediate CURRENT sort is the same displayed child, not an
unspecified original parent. -/
theorem nonempty_current_word_iff_trace
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (W : RawWord (SourceAge.UnarySource.source I) c d) :
    TRel.Nonempty (RawWord.relation (SourceAge.UnarySource.source I) W) →
    ∀ (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
      (z : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d),
      RawWord.relation (SourceAge.UnarySource.source I) W x z ↔
        markedTrace S H (P.completion_property cco)
          (RawWord.relation S (ProjectedWords.forgetWord
            S (SourceAge.UnarySource.source I) (SourceAge.actualProjection I) W))
          c.2.val d.2.val
          (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
          (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
  induction W with
  | nil c =>
      intro _ x y
      exact (real_current_identity_iff I x y).symm
  | identity tail ih =>
      intro h x y
      exact ih h x y
  | @atom c e d a tail ih =>
      intro hWord x z
      let T := SourceAge.UnarySource.source I
      let proj := SourceAge.actualProjection I
      let oldTail := ProjectedWords.forgetWord S T proj tail
      obtain ⟨x₀,z₀,y₀,hAtom₀,hTail₀⟩ := hWord
      have hTailNE : TRel.Nonempty (RawWord.relation T tail) :=
        ⟨y₀,z₀,hTail₀⟩
      have hOldTailNE : TRel.Nonempty (RawWord.relation S oldTail) :=
        ⟨(proj.point e y₀),(proj.point d z₀),
          ProjectedWords.forgetWord_forward S T proj tail y₀ z₀ hTail₀⟩
      let D : RawExact.NonemptyExact S c.1 e.1 :=
        RawExact.exactDiversityAtom S a.val
      let E : RawExact.NonemptyExact S e.1 d.1 :=
        RawExact.singletonExact S oldTail hOldTailNE
      have hDrep : RawExact.evaluate S D.words = S.atomRel a.val :=
        RawExact.exactDiversityAtom_relation S a.val
      have hErep : RawExact.evaluate S E.words = RawWord.relation S oldTail :=
        RawExact.evaluate_single S oldTail
      have hInputD : ∃ p q : Age.Limit S H (P.completion_property cco),
          markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S D.words) c.2.val e.2.val p q := by
        refine ⟨SourceAge.UnarySource.newEquiv I ⟨c,x₀⟩,
          SourceAge.UnarySource.newEquiv I ⟨e,y₀⟩, ?_⟩
        rw [hDrep]
        exact (real_current_atom_iff I a x₀ y₀).mpr hAtom₀
      have hInputE : ∃ q p : Age.Limit S H (P.completion_property cco),
          markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S E.words) e.2.val d.2.val q p := by
        refine ⟨SourceAge.UnarySource.newEquiv I ⟨e,y₀⟩,
          SourceAge.UnarySource.newEquiv I ⟨d,z₀⟩, ?_⟩
        rw [hErep]
        exact (ih hTailNE y₀ z₀).mp hTail₀
      have hTP :=
        marked_trace_product S H P cco D E
          c.2.val e.2.val d.2.val hInputD hInputE
          (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
          (SourceAge.UnarySource.newEquiv I ⟨d,z⟩)
      have hRep :
          TRel.comp (RawExact.evaluate S D.words)
            (RawExact.evaluate S E.words) =
          RawWord.relation S (ProjectedWords.forgetWord S T proj (.atom a tail)) := by
        rw [hDrep,hErep]
        rfl
      constructor
      · rintro ⟨y,hxy,hyz⟩
        have hFirst : markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S D.words) c.2.val e.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨e,y⟩) := by
          rw [hDrep]
          exact (real_current_atom_iff I a x y).mpr hxy
        have hSecond : markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S E.words) e.2.val d.2.val
            (SourceAge.UnarySource.newEquiv I ⟨e,y⟩)
            (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
          rw [hErep]
          exact (ih hTailNE y z).mp hyz
        have hOld := hTP.mp ⟨SourceAge.UnarySource.newEquiv I ⟨e,y⟩,
          hFirst,hSecond⟩
        rw [hRep] at hOld
        exact hOld
      · intro hOld
        have hComp : markedTrace S H (P.completion_property cco)
            (TRel.comp (RawExact.evaluate S D.words)
              (RawExact.evaluate S E.words))
            c.2.val d.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
          rw [hRep]
          exact hOld
        obtain ⟨q,hFirst,hSecond⟩ := hTP.mpr hComp
        obtain ⟨y,hy⟩ :=
          ActualUnaryDecode.decode_child_of_bit I e q hFirst.2.1
        have hAtom : T.atomRel a x y := by
          apply (real_current_atom_iff I a x y).mp
          rw [hDrep] at hFirst
          rw [← hy]
          exact hFirst
        have hTail : RawWord.relation T tail y z := by
          apply (ih hTailNE y z).mpr
          rw [hErep] at hSecond
          rw [← hy]
          exact hSecond
        exact ⟨y,hAtom,hTail⟩

end
end CCO.ExactEPGeometry.ActualUnaryWordTrace
