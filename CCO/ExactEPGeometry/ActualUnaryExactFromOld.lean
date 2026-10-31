import CCO.ExactEPGeometry.ActualUnaryWordProfile
import CCO.ExactEPGeometry.ActualUnaryExactTrace

/-!
# B062 C25: a nonempty old exact trace has one actual current exact presentation

For the genuine AP-character marked limit, suppose the trace of one ORIGINAL
nonempty RAW exact presentation on a fixed pair of actual child sorts is
nonempty. Every one of its finitely many ORIGINAL word restrictions then
has a nonempty trace. C24 lifts each restriction to a CURRENT correctly
child-typed word with equality of its entire represented relation.
Taking the finite list of these words gives one nonempty CURRENT exact
presentation whose relation is the whole original trace.

There is no choice of an arbitrary current middle sort, no SAP, and no
fictitious equality-coloured diversity edge. The empty list remains Top.
The reverse current-to-original direction is independently C27.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryExactFromOld

open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry
open CCO.ExactEPGeometry.ActualUnaryTrace
open CCO.ExactEPGeometry.ActualUnaryWordProfile
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : SourceAge.UnarySource.Identification S H (P.completion_property cco))

/-- Source C25 at one genuinely realized step: a nonempty trace of an
ORIGINAL equality-inclusive RAW exact domain is again a nonempty RAW exact
domain in the ACTUAL marked child source. The child domain is constructed
as a finite list of genuine fixed-child words, not an assumed exact lift. -/
theorem original_exact_trace_has_current_exact
    {c d : Rank.Child (SourceAge.UnarySource.β I)}
    (D : RawExact.NonemptyExact S c.1 d.1)
    (hTrace : ∃ a b : Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S D.words) c.2.val d.2.val a b) :
    ∃ E : RawExact.NonemptyExact (SourceAge.UnarySource.source I) c d,
      ∀ (x : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) c)
        (z : Rank.Point (SourceAge.UnarySource.β I)
          (SourceAge.UnarySource.tag I) d),
        RawExact.evaluate (SourceAge.UnarySource.source I) E.words x z ↔
          markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S D.words) c.2.val d.2.val
            (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
            (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
  classical
  let T := SourceAge.UnarySource.source I
  have hOne (W : RawWord S c.1 d.1) (hW : W ∈ D.words) :
      ∃ a b : Age.Limit S H (P.completion_property cco),
        markedTrace S H (P.completion_property cco)
          (RawWord.relation S W) c.2.val d.2.val a b := by
    obtain ⟨a,b,ha,hb,x,z,hxz,hCode⟩ := hTrace
    exact ⟨a,b,ha,hb,x,z,hxz W hW,hCode⟩
  have hEach (q : {W : RawWord S c.1 d.1 // W ∈ D.words}) :
      ∃ V : RawWord T c d,
        ∀ (x : Rank.Point (SourceAge.UnarySource.β I)
            (SourceAge.UnarySource.tag I) c)
          (z : Rank.Point (SourceAge.UnarySource.β I)
            (SourceAge.UnarySource.tag I) d),
          RawWord.relation T V x z ↔
            RawWord.relation S q.val x.val z.val := by
    obtain ⟨V,_,hEq⟩ :=
      realized_original_word_one_profile P cco I q.val
        (hOne q.val q.property)
    refine ⟨V,?_⟩
    intro x z
    exact (hEq x z).trans
      (real_child_trace_iff I (RawWord.relation S q.val)
        (RawExact.word_invariant_of_homogeneous S H q.val) x z)
  let lift (q : {W : RawWord S c.1 d.1 // W ∈ D.words}) :
      RawWord T c d := Classical.choose (hEach q)
  have hLift (q : {W : RawWord S c.1 d.1 // W ∈ D.words})
      (x : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) c)
      (z : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) d) :
      RawWord.relation T (lift q) x z ↔
        RawWord.relation S q.val x.val z.val :=
    Classical.choose_spec (hEach q) x z
  let newWords : RawExact.Presentation T c d := D.words.attach.map lift
  have hEval
      (x : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) c)
      (z : Rank.Point (SourceAge.UnarySource.β I)
        (SourceAge.UnarySource.tag I) d) :
      RawExact.evaluate T newWords x z ↔
        RawExact.evaluate S D.words x.val z.val := by
    constructor
    · intro h W hW
      have hAttached :
          (⟨W,hW⟩ : {U : RawWord S c.1 d.1 // U ∈ D.words}) ∈
            D.words.attach := by
        simp
      have hMem : lift ⟨W,hW⟩ ∈ newWords := by
        exact List.mem_map.mpr ⟨⟨W,hW⟩,hAttached,rfl⟩
      exact (hLift ⟨W,hW⟩ x z).mp (h (lift ⟨W,hW⟩) hMem)
    · intro h V hV
      change V ∈ D.words.attach.map lift at hV
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hV
      exact (hLift q x z).mpr (h q.val q.property)
  obtain ⟨a,b,hAB⟩ := hTrace
  obtain ⟨x,hx⟩ :=
    ActualUnaryDecode.decode_child_of_bit I c a hAB.1
  obtain ⟨z,hz⟩ :=
    ActualUnaryDecode.decode_child_of_bit I d b hAB.2.1
  have hCurrentTrace :
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S D.words) c.2.val d.2.val
        (SourceAge.UnarySource.newEquiv I ⟨c,x⟩)
        (SourceAge.UnarySource.newEquiv I ⟨d,z⟩) := by
    rw [hx,hz]
    exact hAB
  have hInvariant : TRel.Invariant (G := G)
      (RawExact.evaluate S D.words) :=
    RawExact.presentation_invariant_of_homogeneous S H D.words
  have hOld : RawExact.evaluate S D.words x.val z.val :=
    (real_child_trace_iff I (RawExact.evaluate S D.words)
      hInvariant x z).mp hCurrentTrace
  let E : RawExact.NonemptyExact T c d :=
    ⟨newWords,⟨x,z,(hEval x z).mpr hOld⟩⟩
  refine ⟨E,?_⟩
  intro x' z'
  exact (hEval x' z').trans
    (real_child_trace_iff I (RawExact.evaluate S D.words)
      hInvariant x' z').symm

end
end CCO.ExactEPGeometry.ActualUnaryExactFromOld
