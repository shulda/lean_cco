import CCO.OldIdempotentForest.CycleReconstructionAnyBaseSimple
import CCO.OldIdempotentForest.PlainBaseRequests

/-! Source16 C40(iii) over ANY supplied finite COMPLETE real base A.
The only endpoint assumptions are retained original-word profiles, maximal
gap RAW envelopes, and the fixed original anchor's own profile. The ONE
simultaneous insertion is constructed internally, without a hidden Hom,
OldBaseRealization, CCO premise or reconstruction callback. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
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
variable (A : FiniteInduced (X := X))
variable (roots : PlainBaseRoots S H sap nr2 F data.chain R A)

/-- Exact original-cycle reconstruction retaining the caller's SAME
complete base and prescribed retained OLD root representatives. -/
structure AnyBaseCycleReconstruction where
  originalPoint : ∀ p : Fin original.length,
    X ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p))
  result : CompleteCycleReconstruction original A (data.retainedPins R) originalPoint
  retained : ∀ (p : Fin original.length) (i : Fin (data.n+1)),
    i.val ∈ R.pruning.retainedRoots 0 →
    original.vertices p = Sum.inl (data.chain.root i) →
      result.cycle.image original p =
        ⟨gapSort S H sap nr2 F (data.chain.root i),roots.point i⟩

variable (hAnchor : S.menuRel (PositiveWord.profile S data.anchor.word)
  (roots.point (Fin.last data.n)) (roots.point 0))
variable (kept : PlainKeptProfiles S H sap nr2 F data.chain R A roots)
variable (gaps : PlainGapEnvelopes S H sap nr2 F data.chain R A roots)

/-- Readback helper for the actual ONE simultaneous insertion packet. -/
theorem reconstruct_simple_cycle_from_plain_requests
    (out : PlainBaseRequests S H sap nr2 F data.chain R A roots data.anchor hAnchor kept gaps) :
    Nonempty (data.AnyBaseCycleReconstruction R A roots) := by
  obtain ⟨walk⟩ := pinned_macro_points_of_piece_lines data.chain R A roots.point out.piece_line
  have hAnchorLine : PositiveWord.represented S data.anchor.word
      (roots.point (Fin.last data.n)) (roots.point 0) :=
    represented_of_actual_literal_line S out.anchor_line.toLiteralLine
  have hinj : data.PrescribedRetainedInjective R roots.point := roots.injective
  obtain ⟨result⟩ := data.exact_simple_cycle_from_prescribed_base R roots.point walk hAnchorLine A hinj
  exact ⟨{
    originalPoint := data.anyBaseCyclePoint R roots.point walk hAnchorLine
    result := result
    retained := fun p i hi hp =>
      data.anyBase_reconstructed_retained_image R roots.point walk hAnchorLine A result p i hi hp }⟩

include hAnchor kept gaps in
/-- C40(iii), with its ORIGINAL universal complete-base quantifier.
The actual insertion provider is DISCHARGED here. The kept profile, RAW
gap envelope and separate fixed-anchor gates are the only endpoint inputs. -/
theorem reconstruct_simple_cycle_over_any_base :
    Nonempty (data.AnyBaseCycleReconstruction R A roots) := by
  obtain ⟨out⟩ := plain_base_requests S H sap nr2 F data.chain R A roots data.anchor
    hAnchor kept gaps
  exact data.reconstruct_simple_cycle_from_plain_requests R A roots hAnchor kept gaps out

namespace AnyBaseCycleReconstruction
variable {data R A roots}
variable (out : data.AnyBaseCycleReconstruction R A roots)

/-- The ENTIRE supplied complete old base is retained literally, with
all its induced colours. Extra original unary values impose no new pins. -/
def old_embedding : InducedEmbedding S A out.result.base :=
  out.result.old_embedding original A (data.retainedPins R) out.originalPoint

theorem retained_in_old_base (p : Fin original.length) (i : Fin (data.n+1))
    (hi : i.val ∈ R.pruning.retainedRoots 0)
    (hp : original.vertices p = Sum.inl (data.chain.root i)) :
    out.result.cycle.image original p ∈ A.vertices := by
  rw [out.retained p i hi hp]
  exact roots.in_base i hi

theorem unpinned_fresh (p : Fin original.length) (hp : p ∉ data.retainedPins R) :
    out.result.cycle.image original p ∉ A.vertices := out.result.fresh p hp

end AnyBaseCycleReconstruction
end SupportedSpecifiedCycle
end
end CCO.OldIdempotentForest
