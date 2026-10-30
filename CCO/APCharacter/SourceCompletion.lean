import CCO.APCharacter.MarkedSource

/-! A finite relative interval on the CURRENT original source produces the
actual maximal-character masks and a genuine marked completion/Fraisse age.
No caller supplies any mathematical completion, phase or limit provider. -/
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι}

include H cco in
theorem actual_finite_interval_marked_completion
    (E F : ColourEq S i) (hEF : E < F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ K : Kernel S i, ∃ P : SourcePhase S H
      (exactCalculus_of_homogeneous_CCO S H cco) K,
      P.masks.Calculus ∧ P.masks.FiniteSeedExtension ∧
      Age.CompletionProperty S P.masks ∧
      (Age.Language S).IsUltrahomogeneous (P.MarkedLimit cco) ∧
      (∀ {V : Type} (D : PartialDiagram S V) (bits : V → Bit),
        P.masks.LocalLegal D bits →
        (∀ C : SimpleCycle D, CycleHom C) →
        ∃ f : DiagramHom D, ∃ mark, P.masks.GlobalMarking mark ∧
          ∀ x, mark (f.image x) = bits x) := by
  obtain ⟨Y,U,_,_,_,_,K,⟨P⟩⟩ := finite_interval_character S H cco E F hEF a
  exact ⟨K,P,P.calculus cco,P.finite_seed_extension,P.completion_property cco,
    P.marked_homogeneous cco,P.completion_property cco⟩

end
end CCO.APCharacter
