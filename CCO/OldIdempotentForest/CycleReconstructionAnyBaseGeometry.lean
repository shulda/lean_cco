import CCO.OldIdempotentForest.CycleReconstructionAnyBaseArrays
import CCO.OldIdempotentForest.CycleReconstructionSourceSimple

/-! Read back an arbitrary prescribed retained-root assignment through the
actual ORIGINAL cycle. This geometry uses no hidden Hom or split base. -/

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

private theorem represented_castEndpoints_prescribed {b c b' c' : P}
    (side : SupportedMacroSide S H sap nr2 F b c) (hb : b = b') (hc : c = c')
    (point : ∀ p, X (gapSort S H sap nr2 F p)) :
    PositiveWord.represented S (side.castEndpoints hb hc).word (point b') (point c') ↔
      PositiveWord.represented S side.word (point b) (point c) := by
  cases hb
  cases hc
  rfl

namespace SupportedSpecifiedCycle
variable {original : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)}
variable (data : SupportedSpecifiedCycle S H sap nr2 F hUnary tests hCover original)
variable (R : SourcePrunedForest S H sap nr2 F data.chain)
variable (prescribed : ChainPoints data.chain)
variable (walk : PinnedMacroPoints data.chain R prescribed)

def anyBaseRootAssignment : ∀ p : P, X (gapSort S H sap nr2 F p) :=
  extendTypedRootPoints S (gapSort S H sap nr2 F)
    ⟨data.chain.root,data.root_injective⟩ walk.point

theorem anyBaseRootAssignment_at (i : Fin (data.n+1)) :
    data.anyBaseRootAssignment R prescribed walk (data.chain.root i) = walk.point i :=
  extendTypedRootPoints_at S (gapSort S H sap nr2 F)
    ⟨data.chain.root,data.root_injective⟩ walk.point i

/-- The separate EXACT anchor word is required in addition to all
complementary path pieces, at the SAME prescribed old endpoints. -/
theorem anyBaseArcRepresented
    (hAnchor : PositiveWord.represented S data.anchor.word
      (prescribed (Fin.last data.n)) (prescribed 0)) (i : Fin data.sequence.cuts.count) :
    PositiveWord.represented S (data.sequence.arcSupportedSide i).word
      (data.anyBaseRootAssignment R prescribed walk (data.sequence.root i.castSucc))
      (data.anyBaseRootAssignment R prescribed walk (data.sequence.root i.succ)) := by
  by_cases hi : i.val < data.n
  · let j : Fin data.n := ⟨i.val,hi⟩
    change PositiveWord.represented S (data.chain.side j).word
      (data.anyBaseRootAssignment R prescribed walk (data.chain.root j.castSucc))
      (data.anyBaseRootAssignment R prescribed walk (data.chain.root j.succ))
    rw [data.anyBaseRootAssignment_at,data.anyBaseRootAssignment_at]
    exact walk.sides j
  · have hcount := data.sequence.cuts.two
    have he : i = data.sequence.anchorIndex := by
      apply Fin.ext
      dsimp [n,OrderedCycleSequence.anchorIndex,OrderedCycleSequence.complementCount] at *
      omega
    subst i
    have hp : PositiveWord.represented S data.anchor.word
        (data.anyBaseRootAssignment R prescribed walk (data.chain.root (Fin.last data.n)))
        (data.anyBaseRootAssignment R prescribed walk (data.chain.root 0)) := by
      rw [data.anyBaseRootAssignment_at,data.anyBaseRootAssignment_at,walk.first,walk.last]
      exact hAnchor
    change PositiveWord.represented S data.sequence.anchor.word _ _ at hp
    unfold OrderedCycleSequence.anchor at hp
    exact (represented_castEndpoints_prescribed (data.sequence.arcSupportedSide data.sequence.anchorIndex)
      rfl _ (data.anyBaseRootAssignment R prescribed walk)).mp hp

def anyBaseArcPoints
    (hAnchor : PositiveWord.represented S data.anchor.word
      (prescribed (Fin.last data.n)) (prescribed 0)) :
    RootWordGeometry.CycleArcPoints
      (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)
      (typedRootWordSeeds (G := G) S H sap nr2 F hUnary tests hCover) data.sequence := by
  classical
  let arc i := Classical.choice (supported_arc_points S H sap nr2 F hUnary tests hCover
    (data.sequence.arc i) (data.sequence.arcTraversal i)
    (data.anyBaseRootAssignment R prescribed walk (data.sequence.root i.castSucc))
    (data.anyBaseRootAssignment R prescribed walk (data.sequence.root i.succ))
    (data.anyBaseArcRepresented R prescribed walk hAnchor i))
  exact {
    rootPoint := data.anyBaseRootAssignment R prescribed walk
    point := fun i => (arc i).point
    first_image := fun i => (arc i).first_image
    last_image := fun i => (arc i).last_image
    preserves_step := fun i => (arc i).preserves_step }

def anyBaseCyclePoint
    (hAnchor : PositiveWord.represented S data.anchor.word
      (prescribed (Fin.last data.n)) (prescribed 0)) (p : Fin original.length) :
    X ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p)) :=
  (data.anyBaseArcPoints R prescribed walk hAnchor).gluedPoint p

theorem anyBaseCyclePoint_edges
    (hAnchor : PositiveWord.represented S data.anchor.word
      (prescribed (Fin.last data.n)) (prescribed 0)) (p : Fin original.length)
    (a : S.Atom
      ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p))
      ((G_typ S H sap nr2 F hUnary tests hCover).vertexSort
        (original.vertices (cyclicNext original.length_pos p))))
    (ha : (G_typ S H sap nr2 F hUnary tests hCover).edge
      (original.vertices p) (original.vertices (cyclicNext original.length_pos p))
      (original.next_ne p) = some a) :
    S.colour (data.anyBaseCyclePoint R prescribed walk hAnchor p)
      (data.anyBaseCyclePoint R prescribed walk hAnchor (cyclicNext original.length_pos p)) = some a :=
  (data.anyBaseArcPoints R prescribed walk hAnchor).gluedPoint_preserves p (original.next_ne p) a ha

/-- Every retained ORIGINAL root occurrence reads its originally
prescribed real point. Deleted roots are free internal word positions. -/
theorem anyBaseCyclePoint_retained_image
    (hAnchor : PositiveWord.represented S data.anchor.word
      (prescribed (Fin.last data.n)) (prescribed 0))
    (p : Fin original.length) (i : Fin (data.n+1))
    (hi : i.val ∈ R.pruning.retainedRoots 0)
    (hp : original.vertices p = Sum.inl (data.chain.root i)) :
    (⟨(G_typ S H sap nr2 F hUnary tests hCover).vertexSort (original.vertices p),
      data.anyBaseCyclePoint R prescribed walk hAnchor p⟩ : Sigma X) =
      ⟨gapSort S H sap nr2 F (data.chain.root i),prescribed i⟩ := by
  have hroot := (data.anyBaseArcPoints R prescribed walk hAnchor).gluedPoint_root_image
    p (data.chain.root i) hp
  have hpoint := (data.anyBaseRootAssignment_at R prescribed walk i).trans (walk.fixed i hi)
  exact hroot.trans (congrArg
    (fun x : X (gapSort S H sap nr2 F (data.chain.root i)) =>
      (⟨gapSort S H sap nr2 F (data.chain.root i),x⟩ : Sigma X)) hpoint)

end SupportedSpecifiedCycle
end
end CCO.OldIdempotentForest
