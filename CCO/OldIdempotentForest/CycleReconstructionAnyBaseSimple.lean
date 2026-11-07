import CCO.OldIdempotentForest.CycleReconstructionAnyBaseGeometry

/-! Simplicity over ANY prescribed complete real base. Only the retained
original macro-root occurrences are fixed; every other original cycle
position is fresh from that whole base. No source completion map occurs. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
open CycleGeometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {sap : AgeSAP S} {nr2 : Selectors.OriginalNR2 S}
variable {P : Type z} [Finite P]
variable {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
variable {hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)}
variable {tests : BoundedJoinedPairTests S H sap nr2 F}
variable {hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i)}
namespace SupportedSpecifiedCycle
variable {original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)}
variable (data : SupportedSpecifiedCycle S H sap nr2 F hUnary tests hCover original)
variable (R : SourcePrunedForest S H sap nr2 F data.chain)
variable (prescribed : ChainPoints data.chain)
variable (walk : PinnedMacroPoints data.chain R prescribed)
variable (hAnchor : PositiveWord.represented S data.anchor.word
  (prescribed (Fin.last data.n)) (prescribed 0))

/-- Injectivity is required only on the actually RETAINED original
positions, with their actual prescribed typed real values. -/
def PrescribedRetainedInjective : Prop :=
  ∀ i : Fin (data.n+1), i.val ∈ R.pruning.retainedRoots 0 →
    ∀ j : Fin (data.n+1), j.val ∈ R.pruning.retainedRoots 0 →
      (⟨gapSort S H sap nr2 F (data.chain.root i),prescribed i⟩ : Sigma X) =
        ⟨gapSort S H sap nr2 F (data.chain.root j),prescribed j⟩ → i = j

theorem anyBasePins_injective
    (hinj : data.PrescribedRetainedInjective R prescribed) :
    ∀ p ∈ data.retainedPins R, ∀ q ∈ data.retainedPins R,
      (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),
        data.anyBaseCyclePoint R prescribed walk hAnchor p⟩ : Sigma X) =
      ⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices q),
        data.anyBaseCyclePoint R prescribed walk hAnchor q⟩ → p = q := by
  rintro p ⟨old,hold,hp⟩ q ⟨old',hold',hq⟩ heq
  obtain ⟨i,hi,hret⟩ := R.oldGenerator_occurrence hold
  obtain ⟨j,hj,hret'⟩ := R.oldGenerator_occurrence hold'
  have hip : original.vertices p = Sum.inl (data.chain.root i) :=
    hp.trans (congrArg Sum.inl hi.symm)
  have hjq : original.vertices q = Sum.inl (data.chain.root j) :=
    hq.trans (congrArg Sum.inl hj.symm)
  have hleft := data.anyBaseCyclePoint_retained_image R prescribed walk hAnchor p i hret hip
  have hright := data.anyBaseCyclePoint_retained_image R prescribed walk hAnchor q j hret' hjq
  have hij := hinj i hret j hret' (hleft.symm.trans (heq.trans hright))
  apply original.vertices.injective
  exact hip.trans ((congrArg (fun k => Sum.inl (data.chain.root k)) hij).trans hjq.symm)

/-- The accepted SAP finalizer retains the literal old base A, the SAME
prescribed retained points and all EXACT original sequential fine labels. -/
theorem exact_simple_cycle_from_prescribed_base (A : FiniteInduced (X := X))
    (hinj : data.PrescribedRetainedInjective R prescribed) :
    Nonempty (CompleteCycleReconstruction original A (data.retainedPins R)
      (data.anyBaseCyclePoint R prescribed walk hAnchor)) :=
  exact_simple_cycle_over_complete_base H sap original A
    (data.anyBaseCyclePoint R prescribed walk hAnchor)
    (data.anyBaseCyclePoint_edges R prescribed walk hAnchor)
    (data.retainedPins R) (data.anyBasePins_injective R prescribed walk hAnchor hinj)

theorem anyBase_reconstructed_retained_image (A : FiniteInduced (X := X))
    (result : CompleteCycleReconstruction original A (data.retainedPins R)
      (data.anyBaseCyclePoint R prescribed walk hAnchor))
    (p : Fin original.length) (i : Fin (data.n+1))
    (hi : i.val ∈ R.pruning.retainedRoots 0)
    (hp : original.vertices p = Sum.inl (data.chain.root i)) :
    result.cycle.image original p =
      ⟨gapSort S H sap nr2 F (data.chain.root i),prescribed i⟩ := by
  have hpin : p ∈ data.retainedPins R :=
    ⟨data.chain.root i,R.root_mem_oldGenerators i hi,hp⟩
  have hfixed := result.fixed p hpin
  exact (congrArg
    (fun x : X ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p)) =>
      (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),x⟩ : Sigma X))
    hfixed).trans (data.anyBaseCyclePoint_retained_image R prescribed walk hAnchor p i hi hp)

end SupportedSpecifiedCycle
end
end CCO.OldIdempotentForest
