import CCO.TypedOrbitFrames.CompletedOriginalAutomorphisms

/-! Source11 C60: the actual FULL original group embeds in full hidden
Aut. General presented old groups need not act faithfully, so injectivity
is asserted here exactly for the original typed permutation group. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.UnaryTermsReturn

universe u v w
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem original_completed_full_group_inclusion_injective
    (H : HomogeneousSource S (TerminalPowers.FullAut S))
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Function.Injective (originalCompletedMotionHom S H sap nr2) := by
  intro g h hgh
  apply Subtype.ext
  funext i
  apply Equiv.ext
  intro x
  have heq := congrArg (fun k : (originalCompletedStructure S H sap nr2).Aut =>
    k • (Sum.inl ⟨i,x⟩ : OriginalCompletedNamedCarrier S H)) hgh
  change (Sum.inl ⟨i,g.val i x⟩ : OriginalCompletedNamedCarrier S H) =
    Sum.inl ⟨i,h.val i x⟩ at heq
  simpa only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using heq

end CCO.TypedOrbitFrames
