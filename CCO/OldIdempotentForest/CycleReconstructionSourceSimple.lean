import CCO.OldIdempotentForest.CycleReconstructionSource

/-! The ACTUAL source reconstruction is made simple over the SAME one
complete real base. Pins are exactly original cyclic occurrences of the
retained OLD generators. Their prescribed values are the already chosen
split representatives, and every unpinned original occurrence is fresh.
No cycle label, anchor word or old representative is chosen again. -/

universe u v w r z
namespace CCO.OldIdempotentForest

open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
open CycleGeometry
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

namespace SourcePrunedForest

variable {S H sap nr2 F} {n : Nat} {C : SupportedMacroChain S H sap nr2 F n}

/-- An actual old generator is an endpoint of a retained ORIGINAL leaf,
at its original chain occurrence. No completion vertex is a generator. -/
theorem oldGenerator_occurrence (R : SourcePrunedForest S H sap nr2 F C)
    {old : P} (hold : old ∈ R.oldGenerators) :
    ∃ i : Fin (n+1), C.root i = old ∧ i.val ∈ R.pruning.retainedRoots 0 := by
  classical
  change old ∈ (R.pruning.retainedRoots 0).attach.image
    (fun i => C.root ⟨i.val,Nat.lt_succ_of_le (R.retained_root_bound i.property)⟩) at hold
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hold
  exact ⟨⟨i.val,Nat.lt_succ_of_le (R.retained_root_bound i.property)⟩,hi,i.property⟩

end SourcePrunedForest

namespace SupportedSpecifiedCycle

variable {S H sap nr2 F hUnary tests hCover}
variable {original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)}
variable (data : SupportedSpecifiedCycle S H sap nr2 F hUnary tests hCover original)
variable (R : SourcePrunedForest S H sap nr2 F data.chain)
variable {cco : SemanticCCO.{u,v,max u v,w} S}
variable (out : SourceReconstructionRequests S H sap nr2 F data.chain R hUnary cco
  data.root_injective data.anchor)

/-- Exactly the original specified-cycle occurrences of retained OLD
generators are pinned. Erased old roots and all private positions are
unpinned, and will be fresh from the entire complete real base. -/
def retainedPins : Set (Fin original.length) :=
  {p | ∃ old : P, old ∈ R.oldGenerators ∧ original.vertices p = Sum.inl old}

def sourceMacroWalk : ReconstructedMacroPoints out :=
  Classical.choice (reconstructed_macro_points out)

def sourceArcPoints : RootWordGeometry.CycleArcPoints
    (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)
    (typedRootWordSeeds (G := G) S H sap nr2 F hUnary tests hCover) data.sequence :=
  data.sequence.reconstructedArcPoints R out (data.sourceMacroWalk R out)

/-- The exact original cycle walk produced by the single whole-word
insertion, before the final fixed-base injectivisation. -/
def reconstructionPoint (p : Fin original.length) :
    X ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p)) :=
  (data.sourceArcPoints R out).gluedPoint p

theorem reconstructionPoint_edges (p : Fin original.length)
    (a : S.Atom
      ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p))
      ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort
        (original.vertices (cyclicNext original.length_pos p))))
    (ha : (G_typ S H sap nr2 F hUnary tests hCover).edge
      (original.vertices p) (original.vertices (cyclicNext original.length_pos p))
      (original.next_ne p) = some a) :
    S.colour (data.reconstructionPoint R out p)
      (data.reconstructionPoint R out (cyclicNext original.length_pos p)) = some a :=
  (data.sourceArcPoints R out).gluedPoint_preserves p (original.next_ne p) a ha

/-- At every retained original OLD occurrence, the reconstructed walk
reads the SAME representative from the ONE previously chosen real base. -/
theorem reconstructionPoint_retained_image (p : Fin original.length) (old : P)
    (hold : old ∈ R.oldGenerators) (hp : original.vertices p = Sum.inl old) :
    (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),
      data.reconstructionPoint R out p⟩ : Sigma X) =
      out.data.tagged ⟨old,F.subset_closure _ hold⟩ := by
  obtain ⟨i,hi,hretained⟩ := R.oldGenerator_occurrence hold
  subst old
  let walk := data.sourceMacroWalk R out
  have hfirst := data.sequence.originalRootAssignment_at R out walk i
  have hfixed := walk.fixed i hretained
  have hbase := requestRootPoint_mem out i (F.subset_closure _ hold)
  have hpoint := hfirst.trans (hfixed.trans hbase)
  have hroot := (data.sourceArcPoints R out).gluedPoint_root_image p (data.chain.root i) hp
  refine hroot.trans ?_
  exact congrArg
    (fun x : X (gapSort S H sap nr2 F (data.chain.root i)) =>
      (⟨gapSort S H sap nr2 F (data.chain.root i),x⟩ : Sigma X)) hpoint

theorem retainedPins_point_in_base (p : Fin original.length)
    (hp : p ∈ data.retainedPins R) :
    (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),
      data.reconstructionPoint R out p⟩ : Sigma X) ∈ out.data.base.vertices := by
  obtain ⟨old,hold,hp⟩ := hp
  rw [data.reconstructionPoint_retained_image R out p old hold hp]
  exact out.data.in_base ⟨old,F.subset_closure _ hold⟩

/-- Pin injectivity comes from the actual split representative map and
the ORIGINAL cycle's vertex embedding, not from a completion coincidence. -/
theorem retainedPins_injective :
    ∀ p ∈ data.retainedPins R, ∀ q ∈ data.retainedPins R,
      (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),
        data.reconstructionPoint R out p⟩ : Sigma X) =
      ⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices q),
        data.reconstructionPoint R out q⟩ → p = q := by
  rintro p ⟨old,hold,hp⟩ q ⟨old',hold',hq⟩ heq
  have hleft := data.reconstructionPoint_retained_image R out p old hold hp
  have hright := data.reconstructionPoint_retained_image R out q old' hold' hq
  have hrepresentatives : out.data.tagged ⟨old,F.subset_closure _ hold⟩ =
      out.data.tagged ⟨old',F.subset_closure _ hold'⟩ :=
    hleft.symm.trans (heq.trans hright)
  have hroots := out.data.injective hrepresentatives
  have hrootValues : old = old' := congrArg Subtype.val hroots
  apply original.vertices.injective
  exact hp.trans ((congrArg Sum.inl hrootValues).trans hq.symm)

/-- The original specified atomic cycle is SIMPLE in one finite complete
extension of the SAME old real base. Every retained representative is fixed
and every unpinned original position is fresh from that entire old base. -/
theorem reconstruct_simple_cycle :
    Nonempty (CompleteCycleReconstruction original out.data.base
      (data.retainedPins R) (data.reconstructionPoint R out)) :=
  exact_simple_cycle_over_complete_base H sap original out.data.base
    (data.reconstructionPoint R out) (data.reconstructionPoint_edges R out)
    (data.retainedPins R) (data.retainedPins_injective R out)

/-- The fixed pins are the literal previously chosen real representatives,
with their complete old colours preserved by the same induced inclusion. -/
theorem reconstructed_retained_image
    (result : CompleteCycleReconstruction original out.data.base
      (data.retainedPins R) (data.reconstructionPoint R out))
    (p : Fin original.length) (old : P) (hold : old ∈ R.oldGenerators)
    (hp : original.vertices p = Sum.inl old) :
    result.cycle.image original p = out.data.tagged ⟨old,F.subset_closure _ hold⟩ := by
  have hpin : p ∈ data.retainedPins R := ⟨old,hold,hp⟩
  have hfixed := result.fixed p hpin
  exact (congrArg
    (fun x : X ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p)) =>
      (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),x⟩ : Sigma X))
    hfixed).trans (data.reconstructionPoint_retained_image R out p old hold hp)

end SupportedSpecifiedCycle
end
end CCO.OldIdempotentForest
