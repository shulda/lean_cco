import CCO.OldIdempotentForest.CycleContractionSequence
import CCO.OldIdempotentForest.VisibleBranches
import CCO.OldIdempotentForest.GapReverse
import CCO.OldIdempotentForest.MacroIntervalsSourceChain
import CCO.GuardedOldSeams.LiftSource

/-! Actual source-supported contraction of the fixed guarded visible
lift. Every ordered arc retains its actual branch identifier, the exact
original word (or its literal reverse), and the SAME complete old pair
model. No macro-sequence or source-equation provider is assumed. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
open CycleGeometry
noncomputable section

namespace CycleGeometry.OrderedCycleSequence

variable {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
variable {Q : PrivateBranchSystem Roots Gadgets Branches V} {C : Q.Cycle}

/-- Pure occurrence count, independent of any source interpretation. -/
def complementCount (D : OrderedCycleSequence C) : Nat := D.cuts.count - 1

theorem complement_positive (D : OrderedCycleSequence C) : 0 < D.complementCount := by
  have h := D.cuts.two
  change 0 < D.cuts.count - 1
  omega

def anchorIndex (D : OrderedCycleSequence C) : Fin D.cuts.count :=
  ⟨D.cuts.count - 1,by have h := D.cuts.two; omega⟩

end CycleGeometry.OrderedCycleSequence

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

namespace SupportedMacroSide
variable {S H sap nr2 F} {b c b' c' : P}

/-- Only equality transport of the SAME supported old side. -/
def castEndpoints (side : SupportedMacroSide S H sap nr2 F b c) (hb : b = b') (hc : c = c') :
    SupportedMacroSide S H sap nr2 F b' c' := by
  cases hb
  cases hc
  exact side

theorem castEndpoints_word (side : SupportedMacroSide S H sap nr2 F b c)
    (hb : b = b') (hc : c = c') : HEq (side.castEndpoints hb hc).word side.word := by
  cases hb
  cases hc
  rfl

theorem castEndpoints_model (side : SupportedMacroSide S H sap nr2 F b c)
    (hb : b = b') (hc : c = c') : HEq (side.castEndpoints hb hc).model side.model := by
  cases hb
  cases hc
  rfl

end SupportedMacroSide

variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

local notation "actualR" => typedRootWordSystem S H sap nr2 F hUnary tests hCover
local notation "actualP" => RootWordGeometry.privateBranchSystem actualR

/-- The exact original branch of the ONE fixed local source package. -/
def sourceBranchSide (b : RootWordGeometry.Branch actualR) :
    SupportedMacroSide S H sap nr2 F ((actualR).left b.1) ((actualR).right b.1) :=
  SupportedMacroSide.ofGuardedPackage hUnary tests hCover b.1.val
    (RootWordGeometry.branchWord actualR b) (List.get_mem _ b.2)

theorem sourceBranchSide_word (b : RootWordGeometry.Branch actualR) :
    (sourceBranchSide S H sap nr2 F hUnary tests hCover b).word =
      RootWordGeometry.branchWord actualR b := rfl

theorem sourceBranchSide_model (b : RootWordGeometry.Branch actualR) :
    (sourceBranchSide S H sap nr2 F hUnary tests hCover b).model =
      guardedPairEmbedding S H sap nr2 F hUnary tests b.1.val := rfl

/-- A traversal is turned into its ACTUAL original supported side. The
backwards case reverses that word and swaps the generators of that SAME
old complete factor; no new model or same-profile word is selected. -/
def supportedSideOfTraversal (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal) :
    SupportedMacroSide S H sap nr2 F Q.left Q.right :=
  if hf : T.forward = true then
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch).castEndpoints
      (by
        have he : Q.left = if T.forward then (actualR).left T.branch.1 else (actualR).right T.branch.1 := T.left_eq
        simpa [hf] using he.symm)
      (by
        have he : Q.right = if T.forward then (actualR).right T.branch.1 else (actualR).left T.branch.1 := T.right_eq
        simpa [hf] using he.symm)
  else
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch).reverse.castEndpoints
      (by
        have hfalse : T.forward = false := by cases hb : T.forward <;> simp_all
        have he : Q.left = if T.forward then (actualR).left T.branch.1 else (actualR).right T.branch.1 := T.left_eq
        simpa [hfalse] using he.symm)
      (by
        have hfalse : T.forward = false := by cases hb : T.forward <;> simp_all
        have he : Q.right = if T.forward then (actualR).right T.branch.1 else (actualR).left T.branch.1 := T.right_eq
        simpa [hfalse] using he.symm)

theorem supportedSideOfTraversal_word_forward
    (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal) (hf : T.forward = true) :
    HEq (supportedSideOfTraversal S H sap nr2 F hUnary tests hCover Q T).word
      (RootWordGeometry.branchWord actualR T.branch) := by
  rw [supportedSideOfTraversal,dite_eq_left hf]
  exact SupportedMacroSide.castEndpoints_word
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch) _ _

theorem supportedSideOfTraversal_word_reverse
    (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal) (hf : T.forward = false) :
    HEq (supportedSideOfTraversal S H sap nr2 F hUnary tests hCover Q T).word
      (StrongExact.reverseWord S (RootWordGeometry.branchWord actualR T.branch)) := by
  have hn : T.forward ≠ true := by simp [hf]
  rw [supportedSideOfTraversal,dite_eq_right hn]
  exact SupportedMacroSide.castEndpoints_word
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch).reverse _ _

theorem supportedSideOfTraversal_model_forward
    (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal) (hf : T.forward = true) :
    HEq (supportedSideOfTraversal S H sap nr2 F hUnary tests hCover Q T).model
      (guardedPairEmbedding S H sap nr2 F hUnary tests T.branch.1.val) := by
  rw [supportedSideOfTraversal,dite_eq_left hf]
  exact SupportedMacroSide.castEndpoints_model
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch) _ _

theorem supportedSideOfTraversal_model_reverse
    (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal) (hf : T.forward = false) :
    HEq (supportedSideOfTraversal S H sap nr2 F hUnary tests hCover Q T).model
      (pairSwapEmbedding S H sap nr2 F
        (b := (actualR).right T.branch.1) (c := (actualR).left T.branch.1)
        (guardedPairEmbedding S H sap nr2 F hUnary tests T.branch.1.val)) := by
  have hn : T.forward ≠ true := by simp [hf]
  rw [supportedSideOfTraversal,dite_eq_right hn]
  exact SupportedMacroSide.castEndpoints_model
    (sourceBranchSide S H sap nr2 F hUnary tests hCover T.branch).reverse _ _

namespace CycleGeometry.OrderedCycleSequence
variable {S H sap nr2 F hUnary tests hCover}
variable {C : (RootWordGeometry.privateBranchSystem
  (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)).Cycle}

def arcTraversal (D : OrderedCycleSequence C) (i : Fin D.cuts.count) : (D.arc i).OriginalBranchTraversal :=
  Classical.choice (D.arc i).original_branch_traversal

def arcSupportedSide (D : OrderedCycleSequence C) (i : Fin D.cuts.count) :
    SupportedMacroSide S H sap nr2 F (D.root i.castSucc) (D.root i.succ) :=
  supportedSideOfTraversal S H sap nr2 F hUnary tests hCover (D.arc i) (D.arcTraversal i)

/-- Every supported word has the exact original occurrence geometry of
the specified cycle, with the chosen original branch and rank orientation. -/
theorem arc_original_position (D : OrderedCycleSequence C)
    (i : Fin D.cuts.count) (d : Fin ((D.arc i).length + 1)) :
    C.vertex (cycleShift C.positive D.start (D.cuts.cut i.castSucc + d.val)) =
      RootWordGeometry.indexedVertex
        (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)
        (D.arcTraversal i).branch ((D.arcTraversal i).position d) :=
  (D.arc_vertex i d).symm.trans ((D.arcTraversal i).point d)

theorem arc_original_rank (D : OrderedCycleSequence C)
    (i : Fin D.cuts.count) (d : Fin ((D.arc i).length + 1)) :
    ((D.arcTraversal i).position d).val =
      if (D.arcTraversal i).forward then d.val
      else TypedPrefix.length S (RootWordGeometry.branchWord
        (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover) (D.arcTraversal i).branch) - d.val :=
  (D.arcTraversal i).rank d

theorem arcSupportedSide_word_forward (D : OrderedCycleSequence C) (i : Fin D.cuts.count)
    (hf : (D.arcTraversal i).forward = true) :
    HEq (D.arcSupportedSide i).word (RootWordGeometry.branchWord
      (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover) (D.arcTraversal i).branch) :=
  supportedSideOfTraversal_word_forward S H sap nr2 F hUnary tests hCover _ _ hf

theorem arcSupportedSide_word_reverse (D : OrderedCycleSequence C) (i : Fin D.cuts.count)
    (hf : (D.arcTraversal i).forward = false) :
    HEq (D.arcSupportedSide i).word
      (StrongExact.reverseWord S (RootWordGeometry.branchWord
        (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover) (D.arcTraversal i).branch)) :=
  supportedSideOfTraversal_word_reverse S H sap nr2 F hUnary tests hCover _ _ hf

/-- The first count-1 ORIGINAL arcs are the complementary supported
macro path. Every side is generated from its same original local factor. -/
def supportedChain (D : OrderedCycleSequence C) :
    SupportedMacroChain S H sap nr2 F D.complementCount where
  root (p : Fin (D.complementCount + 1)) := D.root ⟨p.val,by
    have hp : p.val < D.cuts.count - 1 + 1 := p.isLt
    have hc : 2 ≤ D.cuts.count := D.cuts.two
    omega⟩
  side (i : Fin D.complementCount) := D.arcSupportedSide ⟨i.val,by
    have hi : i.val < D.cuts.count - 1 := i.isLt
    omega⟩

theorem chain_root_injective (D : OrderedCycleSequence C) :
    Function.Injective D.supportedChain.root := by
  intro i j hij
  have hcount := D.cuts.two
  let i' : Fin D.cuts.count := ⟨i.val,by have hi := i.isLt; dsimp [complementCount] at hi; omega⟩
  let j' : Fin D.cuts.count := ⟨j.val,by have hj := j.isLt; dsimp [complementCount] at hj; omega⟩
  have heq : D.root i'.castSucc = D.root j'.castSucc := hij
  have hindices := D.injective_initial heq
  have hvalues : i.val = j.val :=
    congrArg (fun k : Fin D.cuts.count => k.val) hindices
  exact Fin.ext hvalues

/-- The last ORIGINAL traversed branch is the fixed anchor. Only its
closing endpoint is transported along the literal old root equality. -/
def anchor (D : OrderedCycleSequence C) : SupportedMacroSide S H sap nr2 F
    (D.supportedChain.root (Fin.last D.complementCount)) (D.supportedChain.root 0) :=
  (D.arcSupportedSide D.anchorIndex).castEndpoints rfl (by
    change D.root D.anchorIndex.succ = D.root 0
    have hi : D.anchorIndex.succ = Fin.last D.cuts.count := by
      apply Fin.ext
      dsimp [anchorIndex]
      have h := D.cuts.two
      omega
    rw [hi]
    exact D.closed)

theorem anchor_word_forward (D : OrderedCycleSequence C)
    (hf : (D.arcTraversal D.anchorIndex).forward = true) :
    HEq D.anchor.word
      (RootWordGeometry.branchWord
        (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover) (D.arcTraversal D.anchorIndex).branch) := by
  unfold anchor
  exact (SupportedMacroSide.castEndpoints_word (D.arcSupportedSide D.anchorIndex) _ _).trans
    (D.arcSupportedSide_word_forward D.anchorIndex hf)

theorem anchor_word_reverse (D : OrderedCycleSequence C)
    (hf : (D.arcTraversal D.anchorIndex).forward = false) :
    HEq D.anchor.word
      (StrongExact.reverseWord S (RootWordGeometry.branchWord
        (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover) (D.arcTraversal D.anchorIndex).branch)) := by
  unfold anchor
  exact (SupportedMacroSide.castEndpoints_word (D.arcSupportedSide D.anchorIndex) _ _).trans
    (D.arcSupportedSide_word_reverse D.anchorIndex hf)

theorem anchor_model_transport (D : OrderedCycleSequence C) :
    HEq D.anchor.model (D.arcSupportedSide D.anchorIndex).model := by
  unfold anchor
  exact SupportedMacroSide.castEndpoints_model (D.arcSupportedSide D.anchorIndex) _ _

end CycleGeometry.OrderedCycleSequence

/-- The ACTUAL fixed guarded lift cycle supplies its ordered OLD roots,
its original complementary supported chain and its exact fixed anchor.
All data are constructed; no contraction or side-equation callback occurs. -/
theorem exists_supported_cycle (C : (RootWordGeometry.privateBranchSystem
    (typedRootWordSystem (G := G) S H sap nr2 F hUnary tests hCover)).Cycle) :
    ∃ D : OrderedCycleSequence C,
      ∃ chain : SupportedMacroChain S H sap nr2 F D.complementCount,
        ∃ anchor : SupportedMacroSide S H sap nr2 F
            (chain.root (Fin.last D.complementCount)) (chain.root 0),
          chain = D.supportedChain ∧ HEq anchor D.anchor ∧
            0 < D.complementCount ∧ Function.Injective chain.root := by
  obtain ⟨D⟩ := exists_ordered_cycle_sequence C
  exact ⟨D,D.supportedChain,D.anchor,rfl,HEq.rfl,D.complement_positive,D.chain_root_injective⟩

end
end CCO.OldIdempotentForest
