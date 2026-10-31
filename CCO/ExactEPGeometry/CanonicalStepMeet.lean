import CCO.ExactEPGeometry.MarkedSupports
import CCO.ExactEPGeometry.ActualUnaryDecode
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C47: real guarded exact-family support at one canonical AP split

This is NOT an abstract assumption on unary refinements.  The actual
FullCharacter SourcePhase and its genuine homogeneous marked-age limit
discharge the AP-only nonempty-mask primality for a finite family of
equality-inclusive RAW exact domains.  The old intersection must have
a REAL pair even when the displayed child traces are all nonempty.
Both output endpoints are decoded from the marked limit into the
SAME named child sorts via the actual entire-carrier equivalence.

The full finite-history theorem must induct using this real one-step
lemma, with the old-to-current exact trace certificates of C28.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C47 for one ACTUAL canonical split. If the original finite RAW
exact intersection is nonempty and each factor occurs on the two
specified new child sorts, the SAME child pair supports the WHOLE
intersection. No preservation of an empty old atomic intersection,
SAP, or extra identity-coloured diversity atom is asserted. -/
theorem canonical_step_exactFamily_support
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K)
    {c d : (SingleStep.successor B P).Sorts}
    (L : List (RawExact.NonemptyExact B.source c.1 d.1))
    (hOld : TRel.Nonempty (rawExactFamily B.source L))
    (hEach : ∀ D ∈ L,
      ∃ x : (SingleStep.successor B P).Point c,
      ∃ y : (SingleStep.successor B P).Point d,
      RawExact.evaluate B.source D.words
        ((SingleStep.projection B P).point c x)
        ((SingleStep.projection B P).point d y)) :
    ∃ x : (SingleStep.successor B P).Point c,
    ∃ y : (SingleStep.successor B P).Point d,
      ∀ D ∈ L,
        RawExact.evaluate B.source D.words
          ((SingleStep.projection B P).point c x)
          ((SingleStep.projection B P).point d y) := by
  let I := SingleStep.identification B P
  have ha :
      ∃ a : Age.Limit B.source B.homogeneous (P.completion_property B.cco),
        (Age.limitCoding B.source B.homogeneous
          (P.completion_property B.cco)).table.owner a =
          Age.ownerEquiv B.source (c.1,c.2.val) := by
    let x : (SingleStep.successor B P).Point c :=
      Classical.choice ((SingleStep.successor B P).source.nonemptySort c)
    exact ⟨UnarySource.newEquiv I ⟨c,x⟩,UnarySource.new_owner I ⟨c,x⟩⟩
  have hb :
      ∃ b : Age.Limit B.source B.homogeneous (P.completion_property B.cco),
        (Age.limitCoding B.source B.homogeneous
          (P.completion_property B.cco)).table.owner b =
          Age.ownerEquiv B.source (d.1,d.2.val) := by
    let y : (SingleStep.successor B P).Point d :=
      Classical.choice ((SingleStep.successor B P).source.nonemptySort d)
    exact ⟨UnarySource.newEquiv I ⟨d,y⟩,UnarySource.new_owner I ⟨d,y⟩⟩
  have hStageEach :
      ∀ D ∈ L, stageSupport B.source B.homogeneous P B.cco
        (RawExact.evaluate B.source D.words) c.2.val d.2.val := by
    intro D hD
    obtain ⟨x,y,hxy⟩ := hEach D hD
    have hInv : TRel.Invariant (G := B.G)
        (RawExact.evaluate B.source D.words) :=
      RawExact.presentation_invariant_of_homogeneous B.source
        B.homogeneous D.words
    refine ⟨UnarySource.newEquiv I ⟨c,x⟩,
      UnarySource.newEquiv I ⟨d,y⟩,?_⟩
    exact (ActualUnaryTrace.real_child_trace_iff I
      (RawExact.evaluate B.source D.words) hInv x y).mpr hxy
  obtain ⟨a,b,hab⟩ :=
    (stageSupport_exactFamily_iff B.source B.homogeneous
      P B.cco L c.2.val d.2.val hOld ha hb).mpr hStageEach
  obtain ⟨x,hx⟩ :=
    ActualUnaryDecode.decode_child_of_bit I c a hab.1
  obtain ⟨y,hy⟩ :=
    ActualUnaryDecode.decode_child_of_bit I d b hab.2.1
  have hInvFamily : TRel.Invariant (G := B.G)
      (rawExactFamily B.source L) := by
    intro g x y hxy D hD
    exact (RawExact.presentation_invariant_of_homogeneous
      B.source B.homogeneous D.words) g x y (hxy D hD)
  have hMarked :
      markedTrace B.source B.homogeneous
        (P.completion_property B.cco) (rawExactFamily B.source L)
          c.2.val d.2.val
          (UnarySource.newEquiv I ⟨c,x⟩)
          (UnarySource.newEquiv I ⟨d,y⟩) := by
    rw [hx,hy]
    exact hab
  have hResult :=
    (ActualUnaryTrace.real_child_trace_iff I
      (rawExactFamily B.source L) hInvFamily x y).mp hMarked
  exact ⟨x,y,fun D hD => hResult D hD⟩

end
end CCO.ExactEPGeometry
