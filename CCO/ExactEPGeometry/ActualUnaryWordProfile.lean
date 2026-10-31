import CCO.ExactEPGeometry.ActualUnaryOldWordLift
import CCO.ExactEPGeometry.ActualUnaryWordTrace

/-!
# B062 C23–C24: every realized ORIGINAL RAW-word trace is ONE current word

For the GENUINE canonical AP-character marked expansion, an original
typed RAW word with nonempty trace between two specified realized children
has a single current correctly typed RAW word profile with EXACTLY that
entire current trace. This is stronger than a union of profiles or a
per-endpoint choice: one old walk witness chooses concrete intermediate
child types, and the proved nonempty-current-word TP theorem upgrades
that witness to equality of full actual current relations.

The canonical old-reduct identification decodes the old endpoints. Each
actual old intermediate vertex carries its own unique child tag. The
construction preserves nil, identity letters and true equality outputs.
No quotient SAP, arbitrary parent-lift, hypothetical section or extra
source axiom is introduced. Finite profile intersections C25 remain a
separate step.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryWordProfile

open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
open CCO.ExactEPGeometry.ActualUnaryTrace
open CCO.ExactEPGeometry.ActualUnaryWordTrace
open CCO.ExactEPGeometry.ActualUnaryOldWordLift
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : SourceAge.UnarySource.Identification S H (P.completion_property cco))

/-- A point in a genuine child has exactly that child as the canonical
old-point tag, not just the same parent sort or the same bit label. -/
theorem childOf_actual_point
    {c : Rank.Child (SourceAge.UnarySource.β I)}
    (x : Rank.Point (SourceAge.UnarySource.β I)
      (SourceAge.UnarySource.tag I) c) :
    childOf I x.val = c := by
  rcases c with ⟨i,b⟩
  change (⟨i,SourceAge.UnarySource.tag I i x.val⟩ :
    Rank.Child (SourceAge.UnarySource.β I)) = ⟨i,b⟩
  rw [x.property]

/-- Source C23: a NONEMPTY marked trace of an original old word supplies
an ACTUAL current child-labelled word whose forgotten syntax is LITERALLY
the original W, and whose current relation has a genuine pair witness.
Neither the child endpoints nor intermediate points are hypothetical. -/
theorem realized_original_word_has_current_word
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (W : RawWord S c.1 d.1)
    (hTrace : ∃ a b : Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawWord.relation S W) c.2.val d.2.val a b) :
    ∃ V : RawWord (SourceAge.UnarySource.source I) c d,
      ProjectedWords.forgetWord S (SourceAge.UnarySource.source I)
        (SourceAge.actualProjection I) V = W ∧
      TRel.Nonempty (RawWord.relation (SourceAge.UnarySource.source I) V) := by
  obtain ⟨a,b,hTrace⟩ := hTrace
  obtain ⟨x,hx⟩ :=
    ActualUnaryDecode.decode_child_of_bit I c a hTrace.1
  obtain ⟨z,hz⟩ :=
    ActualUnaryDecode.decode_child_of_bit I d b hTrace.2.1
  have hInChild : markedTrace S H (P.completion_property cco)
      (RawWord.relation S W) c.2.val d.2.val
      (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
      (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
    rw [hx,hz]
    exact hTrace
  have hOld : RawWord.relation S W x.val z.val :=
    (real_child_trace_iff I (RawWord.relation S W)
      (RawExact.word_invariant_of_homogeneous S H W) x z).mp hInChild
  obtain ⟨V,hForgotten,hReal⟩ :=
    lift_old_word_with_witness I W x.val z.val hOld
  have hC : childOf I x.val = c := childOf_actual_point I x
  have hD : childOf I z.val = d := childOf_actual_point I z
  cases hC
  cases hD
  exact ⟨V,hForgotten,pointOf I x,pointOf I z,hReal⟩

/-- Source C24 for one ACTUAL AP-only full-character step. A single
labelled word represents the ENTIRE old word trace, with fixed original
endpoint children and no extra word-profile union. Both directions of
the equality follow from the previous genuinely nonempty current word
and already compiled one-step C22 TP. -/
theorem realized_original_word_one_profile
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (W : RawWord S c.1 d.1)
    (hTrace : ∃ a b : Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawWord.relation S W) c.2.val d.2.val a b) :
    ∃ V : RawWord (SourceAge.UnarySource.source I) c d,
      ProjectedWords.forgetWord S (SourceAge.UnarySource.source I)
        (SourceAge.actualProjection I) V = W ∧
      ∀ (x : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) c)
        (z : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) d),
        RawWord.relation (SourceAge.UnarySource.source I) V x z ↔
          markedTrace S H (P.completion_property cco)
            (RawWord.relation S W) c.2.val d.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
  obtain ⟨V,hV,hNE⟩ :=
    realized_original_word_has_current_word P cco I W hTrace
  refine ⟨V,hV,?_⟩
  intro x z
  have h := nonempty_current_word_iff_trace P cco I V hNE x z
  rw [hV] at h
  exact h

end
end CCO.ExactEPGeometry.ActualUnaryWordProfile
