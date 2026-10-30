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

include cco in
/-- Original old-cycle identity folding without a caller-supplied whole
homomorphism. Original semantic CCO discharges that temporary graph witness;
no character, marking, SAP or hidden homogeneous-limit provider is used. -/
theorem old_identity_fold {V : Type (max u v)} (D : PartialDiagram S V)
    (cycles : ∀ C : SimpleCycle D, CycleHom C)
    (x y : V) (hxy : x ≠ y) (sameSort : D.vertexSort x = D.vertexSort y)
    (missing : D.edge x y hxy = none) (bound : Completion.IdentityBound D x y) :
    ∃ f : DiagramHom D,
      ∀ C : SimpleCycle (Completion.foldDiagram D f x y hxy sameSort missing bound), CycleHom C := by
  obtain ⟨f⟩ := cco V D cycles
  exact ⟨f,Completion.identity_folding_cycles D f x y hxy sameSort missing bound⟩

end
end CCO.APCharacter
