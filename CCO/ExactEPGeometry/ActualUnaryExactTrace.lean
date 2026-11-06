import CCO.ExactEPGeometry.ActualUnaryWordTrace

/-!
# B062 / C26–C27: ACTUAL exact-domain lift for one full AP-character step

A genuine nonempty current RAW exact domain D in the canonical child
source has an ORIGINAL nonempty RAW exact presentation `forgetExact D`.
Their endpoint relations are EXACTLY equal on the two displayed children.
The forward direction projects real current witnesses.  Conversely, the
original intersection gives every forgotten word at the REAL projected
endpoints; because D was nonempty, EACH displayed current word is
individually nonempty. The proven C24 nonempty current-word ↔ marked
trace theorem therefore reconstructs the same full current profile.

No SAP, added quotient provider, mere palette inclusion, or fictional
diagonal edge; all intermediate child sorts in each word are fixed.
Arbitrary actual tower-prefix iteration and reverse old-exact-to-current
exactness remain separate source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryExactTrace

open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry RigidGroupoid.Phase
open CCO.ExactEPGeometry.ActualUnaryTrace
open CCO.ExactEPGeometry.ActualUnaryWordTrace

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : SourceAge.UnarySource.Identification S H (P.completion_property cco))

/-- C27, one genuine AP-only character split. For EVERY nonempty finite
equality-inclusive current exact presentation D, its actual original
forgetExact lift is nonempty and has literally the SAME marked trace on
the specified current endpoint children. This includes zero restrictions
(Top), the genuine nil identity and arbitrary repeated intermediate sorts. -/
theorem current_exact_iff_original_trace
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (D : RawExact.NonemptyExact (SourceAge.UnarySource.source I) c d)
    (x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c)
    (z : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) d) :
    let T := SourceAge.UnarySource.source I
    let old := ProjectedWords.forgetExact S T (SourceAge.actualProjection I) D
    RawExact.evaluate T D.words x z ↔
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S old.words) c.2.val d.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
  dsimp only
  let T := SourceAge.UnarySource.source I
  let proj := SourceAge.actualProjection I
  let old := ProjectedWords.forgetExact S T proj D
  have hOldInvariant : TRel.Invariant (G := G)
      (RawExact.evaluate S old.words) :=
    RawExact.presentation_invariant_of_homogeneous S H old.words
  have hReal :
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S old.words) c.2.val d.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) ↔
      RawExact.evaluate S old.words x.val z.val :=
    real_child_trace_iff I (RawExact.evaluate S old.words)
      hOldInvariant x z
  constructor
  · intro hCurrent
    apply hReal.mpr
    exact ProjectedWords.forgetExact_forward S T proj D x z hCurrent
  · intro hTrace
    have hOld : RawExact.evaluate S old.words x.val z.val :=
      hReal.mp hTrace
    intro W hW
    obtain ⟨x₀,z₀,hD₀⟩ := D.nonempty
    have hWordNonempty : TRel.Nonempty (RawWord.relation T W) :=
      ⟨x₀,z₀,hD₀ W hW⟩
    let oldW := ProjectedWords.forgetWord S T proj W
    have hOldWord : RawWord.relation S oldW x.val z.val :=
      hOld oldW (List.mem_map.mpr ⟨W,hW,rfl⟩)
    have hInvWord : TRel.Invariant (G := G)
        (RawWord.relation S oldW) :=
      RawExact.word_invariant_of_homogeneous S H oldW
    have hWordTrace :
        markedTrace S H (P.completion_property cco)
          (RawWord.relation S oldW) c.2.val d.2.val
          (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
          (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) :=
      (real_child_trace_iff I
        (RawWord.relation S oldW) hInvWord x z).mpr hOldWord
    exact (nonempty_current_word_iff_trace P cco I W
      hWordNonempty x z).mpr hWordTrace

/-- An existentially packaged old original source lift with a real
witness and exact full relation equality on the given current children.
The lift is the actual original `forgetExact` presentation, not a
postulated choice of a predecessor or a quotient-action representative. -/
theorem current_exact_has_original_lift
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (D : RawExact.NonemptyExact (SourceAge.UnarySource.source I) c d) :
    ∃ E : RawExact.NonemptyExact S c.1 d.1,
      ∀ (x : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) c)
        (z : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) d),
      RawExact.evaluate (SourceAge.UnarySource.source I) D.words x z ↔
        markedTrace S H (P.completion_property cco)
          (RawExact.evaluate S E.words) c.2.val d.2.val
          (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
          (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
  refine ⟨ProjectedWords.forgetExact S
    (SourceAge.UnarySource.source I) (SourceAge.actualProjection I) D, ?_⟩
  intro x z
  exact current_exact_iff_original_trace P cco I D x z

end
end CCO.ExactEPGeometry.ActualUnaryExactTrace
