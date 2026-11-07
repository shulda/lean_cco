import CCO.OldIdempotentForest.CycleReconstructionSupportedLines
import CCO.OldIdempotentForest.CycleReconstructionGluing
import CCO.OldIdempotentForest.CycleReconstructionPieceWalks
import CCO.OldIdempotentForest.CycleReconstructionAssignments
import CCO.OldIdempotentForest.CycleReconstructionSimple
import CCO.OldIdempotentForest.VisibleBadCycle

/-! Concrete source reconstruction. The actual specified cycle supplies
its original supported chain and anchor; the received forest and the ONE
complete-base insertion supply every interval walk. All geometry, word
orientation and gluing are proved, with no reconstruction callback. -/

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

local notation "actualR" => typedRootWordSystem S H sap nr2 F hUnary tests hCover
local notation "actualP" => RootWordGeometry.privateBranchSystem actualR
local notation "actualSeed" => typedRootWordSeeds S H sap nr2 F hUnary tests hCover

private theorem represented_castEndpoints_root {b c b' c' : P}
    (side : SupportedMacroSide S H sap nr2 F b c) (hb : b = b') (hc : c = c')
    (point : ∀ p, X (gapSort S H sap nr2 F p)) :
    PositiveWord.represented S (side.castEndpoints hb hc).word (point b') (point c') ↔
      PositiveWord.represented S side.word (point b) (point c) := by
  cases hb
  cases hc
  rfl

namespace CycleGeometry.OrderedCycleSequence
variable {S H sap nr2 F hUnary tests hCover}
variable {C : (RootWordGeometry.privateBranchSystem
  (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)).Cycle}
variable (D : OrderedCycleSequence C)
variable (R : SourcePrunedForest S H sap nr2 F D.supportedChain)
variable {cco : SemanticCCO.{u,v,max u v,w} S}
variable (out : SourceReconstructionRequests S H sap nr2 F D.supportedChain R hUnary cco
  D.chain_root_injective D.anchor)

def originalRootAssignment (walk : ReconstructedMacroPoints out) :
    ∀ p : P, X ((typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover).sort p) :=
  extendTypedRootPoints S (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover).sort
    ⟨D.supportedChain.root,D.chain_root_injective⟩ walk.point

theorem originalRootAssignment_at (walk : ReconstructedMacroPoints out)
    (i : Fin (D.complementCount+1)) :
    D.originalRootAssignment R out walk (D.supportedChain.root i) = walk.point i :=
  extendTypedRootPoints_at S (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover).sort
    ⟨D.supportedChain.root,D.chain_root_injective⟩ walk.point i

/-- All ORIGINAL arc words, including the separate fixed anchor, are
realized at the SAME constructed old-root assignment. -/
theorem original_arc_represented (walk : ReconstructedMacroPoints out) (i : Fin D.cuts.count) :
    PositiveWord.represented S (D.arcSupportedSide i).word
      (D.originalRootAssignment R out walk (D.root i.castSucc))
      (D.originalRootAssignment R out walk (D.root i.succ)) := by
  by_cases hi : i.val < D.complementCount
  · let j : Fin D.complementCount := ⟨i.val,hi⟩
    change PositiveWord.represented S (D.supportedChain.side j).word
      (D.originalRootAssignment R out walk (D.supportedChain.root j.castSucc))
      (D.originalRootAssignment R out walk (D.supportedChain.root j.succ))
    rw [D.originalRootAssignment_at,D.originalRootAssignment_at]
    exact walk.sides j
  · have hcount := D.cuts.two
    have he : i = D.anchorIndex := by
      apply Fin.ext
      dsimp [anchorIndex,complementCount] at *
      omega
    subst i
    have hfirst : D.originalRootAssignment R out walk (D.supportedChain.root 0) =
        out.data.point R.anchorRight := by
      rw [D.originalRootAssignment_at]
      exact walk.first.trans (requestRootPoint_mem out 0 R.anchorRight.property)
    have hlast : D.originalRootAssignment R out walk
        (D.supportedChain.root (Fin.last D.complementCount)) =
        out.data.point R.anchorLeft := by
      rw [D.originalRootAssignment_at]
      exact walk.last.trans (requestRootPoint_mem out (Fin.last D.complementCount) R.anchorLeft.property)
    have hp : PositiveWord.represented S D.anchor.word
        (D.originalRootAssignment R out walk (D.supportedChain.root (Fin.last D.complementCount)))
        (D.originalRootAssignment R out walk (D.supportedChain.root 0)) := by
      rw [hfirst,hlast]
      exact represented_of_actual_literal_line S out.anchor_line.toLiteralLine
    unfold anchor at hp
    exact (represented_castEndpoints_root S H sap nr2 F (D.arcSupportedSide D.anchorIndex)
      rfl _ (D.originalRootAssignment R out walk)).mp hp

def reconstructedArcPoints (walk : ReconstructedMacroPoints out) :
    RootWordGeometry.CycleArcPoints
      (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)
      (typedRootWordSeeds (G := G) S H sap nr2 F hUnary tests hCover) D := by
  classical
  let arc i := Classical.choice (supported_arc_points S H sap nr2 F hUnary tests hCover
    (D.arc i) (D.arcTraversal i)
    (D.originalRootAssignment R out walk (D.root i.castSucc))
    (D.originalRootAssignment R out walk (D.root i.succ))
    (D.original_arc_represented R out walk i))
  exact {
    rootPoint := D.originalRootAssignment R out walk
    point := fun i => (arc i).point
    first_image := fun i => (arc i).first_image
    last_image := fun i => (arc i).last_image
    preserves_step := fun i => (arc i).preserves_step }

end CycleGeometry.OrderedCycleSequence

/-- Actual source-facing cycle data. The chain and anchor below are
computed from the exact original cyclic enumeration, rather than fields
which may contain arbitrary words or a supplied contraction provider. -/
structure SupportedSpecifiedCycle
    (original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)) where
  sequence : OrderedCycleSequence (guardedPrivateCycle S H sap nr2 F hUnary tests hCover original)

namespace SupportedSpecifiedCycle
variable {S H sap nr2 F hUnary tests hCover}
variable {original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)}
variable (data : SupportedSpecifiedCycle S H sap nr2 F hUnary tests hCover original)
def n : Nat := data.sequence.complementCount
theorem positive : 0 < data.n := data.sequence.complement_positive
def chain : SupportedMacroChain S H sap nr2 F data.n := data.sequence.supportedChain
theorem root_injective : Function.Injective data.chain.root := data.sequence.chain_root_injective
def anchor : SupportedMacroSide S H sap nr2 F
    (data.chain.root (Fin.last data.n)) (data.chain.root 0) := data.sequence.anchor

/-- C37--C40/C56: ONE complete-base whole-original-word insertion maps
back to EVERY fine edge of the EXACT specified original cycle. -/
theorem reconstruct_cycle_hom (R : SourcePrunedForest S H sap nr2 F data.chain)
    {cco : SemanticCCO.{u,v,max u v,w} S}
    (out : SourceReconstructionRequests S H sap nr2 F data.chain R hUnary cco
      data.root_injective data.anchor) : CycleHom original := by
  obtain ⟨walk⟩ := reconstructed_macro_points out
  let arcs := data.sequence.reconstructedArcPoints R out walk
  refine ⟨arcs.gluedPoint,?_⟩
  intro p a ha
  exact arcs.gluedPoint_preserves p (original.next_ne p) a ha

end SupportedSpecifiedCycle

/-- No extra internal/noninternal case or contraction premise is needed:
every actual specified simple cycle has at least two distinct OLD roots. -/
theorem supported_specified_cycle_exists
    (original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)) :
    Nonempty (SupportedSpecifiedCycle S H sap nr2 F hUnary tests hCover original) := by
  obtain ⟨sequence⟩ := exists_ordered_cycle_sequence
    (guardedPrivateCycle S H sap nr2 F hUnary tests hCover original)
  exact ⟨⟨sequence⟩⟩

end
end CCO.OldIdempotentForest
