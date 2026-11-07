import CCO.GuardedTwoRoot.UnarySource

/-! Actual closed singleton embeddings discharge unary admissibility.
A genuine HE into a fixed actual member embeds each WHOLE singleton
closure; the HN projection to an arbitrary ambient is not such a member. -/

universe u v w
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure CCO.GuardedTwoRoot

/-- This restriction works for mixed source/target universes and for
genuinely partial unary domains. No totality or finite-size premise is used. -/
theorem unaryAdmissible_of_homEmbedding {L : Signature.{u}}
    {V : Type v} {W : Type w} {C : Structure L V} {A : Structure L W}
    (f : Hom C A) (hf : f.HomEmbedding) : UnaryAdmissible C A := by
  intro x
  exact ⟨f.restrictionEmbedding (C.isClosed_closure {x})
    (hf _ (C.isClosed_closure {x}) (C.singleton_irreducible x))⟩

end CCO.TerminalHiddenHN
