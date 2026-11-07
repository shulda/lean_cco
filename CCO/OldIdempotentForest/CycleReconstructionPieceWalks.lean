import CCO.OldIdempotentForest.CycleReconstructionArrays
import CCO.OldIdempotentForest.CycleReconstructionIntervals
import CCO.OldIdempotentForest.CycleReconstructionAssignments
import CCO.OldIdempotentForest.ReconstructionRequests
import CCO.StrongExact.ThetaWordLineReadout

/-! The ONE actual simultaneous insertion supplies the original interval
walks. Their original side arrays are glued while fixing every retained
OLD root. No fresh completion, profile or macro decomposition is assumed. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section

theorem represented_of_actual_literal_line {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) {i j : ι} {word : PositiveWord S i j}
    {x : X i} {y : X j} (line : LiteralLine S word x y) :
    PositiveWord.represented S word x y := by
  have h := represented_of_literal_word_line S word line.point line.edges
  rw [line.source,line.target] at h
  exact h

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {sap : AgeSAP S} {nr2 : Selectors.OriginalNR2 S}
variable {P : Type z} [Finite P]
variable {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
variable {n : Nat} {C : SupportedMacroChain S H sap nr2 F n}
variable {R : SourcePrunedForest S H sap nr2 F C}
variable {hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)}
variable {cco : SemanticCCO.{u,v,max u v,w} S} {hC : Function.Injective C.root}
variable {anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)}
variable (out : SourceReconstructionRequests S H sap nr2 F C R hUnary cco hC anchor)

/-- Only retained roots are constrained. Outside the retained source the
dummy values are arbitrary and are never used as prescribed gap interiors. -/
def requestRootPoint : ChainPoints C := fun i =>
  extendTypedRootPoints S (gapSort S H sap nr2 F)
    (⟨Subtype.val,Subtype.val_injective⟩ : F.closure (R.oldGenerators : Set P) ↪ P)
    out.data.point (C.root i)

theorem requestRootPoint_mem (i : Fin (n+1))
    (hi : C.root i ∈ F.closure (R.oldGenerators : Set P)) :
    requestRootPoint out i = out.data.point ⟨C.root i,hi⟩ := by
  exact extendTypedRootPoints_at S (gapSort S H sap nr2 F)
    (⟨Subtype.val,Subtype.val_injective⟩ : F.closure (R.oldGenerators : Set P) ↪ P)
    out.data.point ⟨C.root i,hi⟩

theorem request_piece_macro_walk (q : LocatedPiece (Fin n))
    (hq : q ∈ locate 0 R.pruning.pieces) :
    Nonempty (IntervalMacroWalk C (requestRootPoint out) q.start q.stop) := by
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hq
  change R.indexedPiece k = q at hk
  subst q
  let q := R.indexedPiece k
  let hq := R.indexedPiece_mem k
  have hb : q.start < q.stop ∧ q.stop ≤ n := R.locatedBounds hq
  have hp := represented_of_actual_literal_line S (out.piece_line k).toLiteralLine
  have hx := requestRootPoint_mem out ⟨q.start,by omega⟩ (R.pieceLeft q hq).property
  have hy := requestRootPoint_mem out ⟨q.stop,by omega⟩ (R.pieceRight q hq).property
  have hrep : PositiveWord.represented S (C.intervalPath q.start q.stop hb.1 hb.2).flatten
      (requestRootPoint out ⟨q.start,by omega⟩) (requestRootPoint out ⟨q.stop,by omega⟩) := by
    rw [hx,hy]
    exact hp
  obtain ⟨point,hfirst,hlast,hsides⟩ := C.represented_interval_original_sides
    q.start q.stop hb.1 hb.2 _ _ hrep
  exact ⟨{
    positive := hb.1
    bounded := hb.2
    point := point
    first := fun _ => hfirst
    last := fun _ => hlast
    sides := hsides }⟩

structure ReconstructedMacroPoints where
  point : ChainPoints C
  sides : ∀ k : Fin n, PositiveWord.represented S (C.side k).word
    (point k.castSucc) (point k.succ)
  fixed : ∀ i : Fin (n+1), i.val ∈ R.pruning.retainedRoots 0 →
    point i = requestRootPoint out i
  first : point 0 = requestRootPoint out 0
  last : point (Fin.last n) = requestRootPoint out (Fin.last n)

/-- Actual interval witnesses from the simultaneous insertion reconstruct
the original macro-side walks while retaining ALL old boundary values. -/
theorem reconstructed_macro_points : Nonempty (ReconstructedMacroPoints out) := by
  have hne : R.pruning.pieces ≠ [] := by
    intro hz
    have hn := R.pruning.word_ne_nil
    rw [← R.pruning.pieces_word,hz] at hn
    exact hn rfl
  obtain ⟨joined⟩ := recompose_piece_macro_walks C R.pruning.pieces hne 0
    (request_piece_macro_walk out)
  have hlength : (piecesWord R.pruning.pieces).length = n := by
    rw [R.pruning.pieces_word,R.prunes.word,R.forest.original_yield,List.length_finRange]
  refine ⟨{
    point := joined.walk.point
    sides := ?_
    fixed := ?_
    first := joined.walk.first (by omega)
    last := ?_ }⟩
  · intro k
    apply joined.walk.sides k (Nat.zero_le _)
    simpa only [hlength,Nat.zero_add] using k.isLt
  · intro i hi
    obtain ⟨q,hq,_,he⟩ := R.pruning.retainedRoot_piece 0 hi
    have hf := joined.boundaries q hq
    rcases he with he | he
    · have hh : ChainFixedAt C joined.walk.point (requestRootPoint out) i.val := by simpa only [he] using hf.1
      exact hh i.isLt
    · have hh : ChainFixedAt C joined.walk.point (requestRootPoint out) i.val := by simpa only [he] using hf.2
      exact hh i.isLt
  · have hi : 0+(piecesWord R.pruning.pieces).length = n := by omega
    have hf := ChainFixedAt.congr C hi joined.walk.last
    exact hf (Nat.lt_succ_self n)

end
end CCO.OldIdempotentForest
