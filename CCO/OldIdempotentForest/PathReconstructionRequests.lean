import CCO.OldIdempotentForest.ReconstructionRequests
import CCO.OldIdempotentForest.CycleReconstructionArrays
import CCO.OldIdempotentForest.CycleReconstructionIntervals
import CCO.OldIdempotentForest.CycleReconstructionAssignments
import CCO.StrongExact.ThetaWordLineReadout

/-! Standalone positive supported path compression. The located retained
letters and maximal original gaps issue their requests over ONE actual
complete real base. This construction needs no closing anchor. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)

/-- Only the original path pieces are requested, in their actual located
order. The common base and split Hom are constructed from the actual
retained-source Hom; no unrelated closing side is required. -/
structure PathReconstructionRequests
    (R : SourcePrunedForest S H sap nr2 F C)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root) where
  data : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P))
  insertion : SimultaneousWords S data.base (R.pieceRequest hUnary cco hC data)

theorem path_reconstruction_requests_of_hom
    (R : SourcePrunedForest S H sap nr2 F C)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (f : Hom (F.closureStructure (R.oldGenerators : Set P)) (originalPartialTarget S H sap nr2)) :
    Nonempty (PathReconstructionRequests S H sap nr2 F C R hUnary cco hC) := by
  obtain ⟨D⟩ := oldBaseRealization_of_hom S H sap nr2 _ f
  have hbase (k : R.PieceIndex) : (R.pieceRequest hUnary cco hC D k).InBase S D.base :=
    ⟨D.in_base _,D.in_base _⟩
  obtain ⟨out⟩ := simultaneous_word_insertion S H sap D.base (R.pieceRequest hUnary cco hC D) hbase
  exact ⟨⟨D,out⟩⟩

namespace PathReconstructionRequests
variable {S H sap nr2 F C}
variable {R : SourcePrunedForest S H sap nr2 F C}
variable {hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)}
variable {cco : SemanticCCO.{u,v,max u v,w} S} {hC : Function.Injective C.root}
variable (out : PathReconstructionRequests S H sap nr2 F C R hUnary cco hC)

def piece_line (k : R.PieceIndex) :
    FreshWordLine S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
      (out.data.point (R.pieceLeft (R.indexedPiece k) (R.indexedPiece_mem k)))
      (out.data.point (R.pieceRight (R.indexedPiece k) (R.indexedPiece_mem k))) out.data.base.vertices :=
  out.insertion.line k

theorem piece_represented (k : R.PieceIndex) :
    PositiveWord.represented S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
      (out.data.point (R.pieceLeft (R.indexedPiece k) (R.indexedPiece_mem k)))
      (out.data.point (R.pieceRight (R.indexedPiece k) (R.indexedPiece_mem k))) := by
  have h := CCO.StrongExact.represented_of_literal_word_line S
    (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
    (out.piece_line k).point (out.piece_line k).edges
  rw [(out.piece_line k).source,(out.piece_line k).target] at h
  exact h

theorem piece_inBase (k : R.PieceIndex) :
    (R.pieceRequest hUnary cco hC out.data k).InBase S out.data.base :=
  out.insertion.endpoints_old k

theorem old_base_subset : out.data.base.vertices ⊆ out.insertion.base.vertices :=
  out.insertion.old_subset

/-- Prescribed real values extend to unused old positions without
changing any point in the actual retained closure. -/
def rootPoint : ChainPoints C := fun i =>
  extendTypedRootPoints S (gapSort S H sap nr2 F)
    (⟨Subtype.val,Subtype.val_injective⟩ : F.closure (R.oldGenerators : Set P) ↪ P)
    out.data.point (C.root i)

theorem rootPoint_mem (i : Fin (n+1))
    (hi : C.root i ∈ F.closure (R.oldGenerators : Set P)) :
    out.rootPoint i = out.data.point ⟨C.root i,hi⟩ :=
  extendTypedRootPoints_at S (gapSort S H sap nr2 F)
    (⟨Subtype.val,Subtype.val_injective⟩ : F.closure (R.oldGenerators : Set P) ↪ P)
    out.data.point ⟨C.root i,hi⟩

theorem piece_interval_walk (q : LocatedPiece (Fin n))
    (hq : q ∈ locate 0 R.pruning.pieces) : C.IntervalWalk out.rootPoint q.start q.stop := by
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hq
  change R.indexedPiece k = q at hk
  subst q
  let q := R.indexedPiece k
  let hq := R.indexedPiece_mem k
  have hb : q.start < q.stop ∧ q.stop ≤ n := R.locatedBounds hq
  refine ⟨hb.1,hb.2,?_⟩
  rw [out.rootPoint_mem ⟨q.start,by omega⟩ (R.pieceLeft q hq).property,
    out.rootPoint_mem ⟨q.stop,by omega⟩ (R.pieceRight q hq).property]
  exact out.piece_represented k

/-- The RAW readout is the WHOLE exact original positive path, with
the same actual outer representatives. There is no closing anchor. -/
theorem whole_original_path : C.IntervalWalk out.rootPoint 0 n :=
  Prunes.recompose_original_path S H sap nr2 F C out.rootPoint R.prunes
    R.forest.original_yield out.piece_interval_walk

theorem piece_macro_walk (q : LocatedPiece (Fin n))
    (hq : q ∈ locate 0 R.pruning.pieces) :
    Nonempty (IntervalMacroWalk C out.rootPoint q.start q.stop) := by
  obtain ⟨hlo,hhi,hrep⟩ := out.piece_interval_walk q hq
  obtain ⟨point,hfirst,hlast,hsides⟩ := C.represented_interval_original_sides
    q.start q.stop hlo hhi _ _ hrep
  exact ⟨{ positive := hlo
           bounded := hhi
           point := point
           first := fun _ => hfirst
           last := fun _ => hlast
           sides := hsides }⟩

/-- The original macro-side array is realized, retaining EVERY original
kept root value, including all old gap boundaries. -/
structure ReconstructedPathPoints where
  point : ChainPoints C
  sides : ∀ k : Fin n, PositiveWord.represented S (C.side k).word
    (point k.castSucc) (point k.succ)
  fixed : ∀ i : Fin (n+1), i.val ∈ R.pruning.retainedRoots 0 → point i = out.rootPoint i
  first : point 0 = out.rootPoint 0
  last : point (Fin.last n) = out.rootPoint (Fin.last n)

theorem ReconstructedPathPoints.retained_reading (walk : ReconstructedPathPoints out)
    (i : Fin (n+1)) (hi : i.val ∈ R.pruning.retainedRoots 0) :
    rootMap S H sap nr2 (F.sort (C.root i)) (walk.point i) =
      out.data.hom.point ⟨C.root i,F.subset_closure _ (R.root_mem_oldGenerators i hi)⟩ := by
  have hmem := F.subset_closure (R.oldGenerators : Set P) (R.root_mem_oldGenerators i hi)
  rw [walk.fixed i hi,out.rootPoint_mem i hmem]
  exact out.data.reading ⟨C.root i,hmem⟩

theorem reconstruct_macro_path : Nonempty (ReconstructedPathPoints out) := by
  have hne : R.pruning.pieces ≠ [] := by
    intro hz
    have hn := R.pruning.word_ne_nil
    rw [← R.pruning.pieces_word,hz] at hn
    exact hn rfl
  obtain ⟨joined⟩ := recompose_piece_macro_walks C R.pruning.pieces hne 0 out.piece_macro_walk
  have hlength : (piecesWord R.pruning.pieces).length = n := by
    rw [R.pruning.pieces_word,R.prunes.word,R.forest.original_yield,List.length_finRange]
  refine ⟨{ point := joined.walk.point
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
    · have hh : ChainFixedAt C joined.walk.point out.rootPoint i.val := by
        simpa only [he] using hf.1
      exact hh i.isLt
    · have hh : ChainFixedAt C joined.walk.point out.rootPoint i.val := by
        simpa only [he] using hf.2
      exact hh i.isLt
  · have hi : 0+(piecesWord R.pruning.pieces).length = n := by omega
    exact (ChainFixedAt.congr C hi joined.walk.last) (Nat.lt_succ_self n)

end PathReconstructionRequests

/-- The actual received forest gives the standalone source path's
compression. Only OLD source generators enter the bound. Every actual
Hom of that retained closure yields the anchor-free simultaneous request
packet, with every piece's exact original word and endpoints. -/
theorem source_path_compression
    (hn : 0 < n)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root) :
    ∃ R : SourcePrunedForest S H sap nr2 F C,
      R.pruning.leaves ≤ 2 ^ (3 * Nat.card (TypedProfileState S)) ∧
      R.oldGenerators.card ≤ 2 ^ (3 * Nat.card (TypedProfileState S)+1) ∧
      Nat.card (F.closure (R.oldGenerators : Set P)) ≤
        originalSourceUniformNormalCodeBudget S H * 2 ^ (3 * Nat.card (TypedProfileState S)+1) ∧
      ∀ f : Hom (F.closureStructure (R.oldGenerators : Set P)) (originalPartialTarget S H sap nr2),
        Nonempty (PathReconstructionRequests S H sap nr2 F C R hUnary cco hC) := by
  obtain ⟨R⟩ := sourcePrunedForest_exists S H sap nr2 F C hn
  exact ⟨R,R.retained_bounds.1,R.oldGenerators_card,R.old_closure_bound hUnary,
    fun f => path_reconstruction_requests_of_hom S H sap nr2 F C R hUnary cco hC f⟩

/-- Standalone C36/factor-path source export. The actual forest and
source counts are unconditional. Every actual retained-closure Hom
reconstructs all original macro sides and pins, and the exact whole
positive RAW path, using one simultaneous insertion without an anchor. -/
theorem source_macro_path_compression
    (hn : 0 < n)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root) :
    ∃ R : SourcePrunedForest S H sap nr2 F C,
      R.pruning.leaves ≤ 2 ^ (3 * Nat.card (TypedProfileState S)) ∧
      R.oldGenerators.card ≤ 2 ^ (3 * Nat.card (TypedProfileState S)+1) ∧
      Nat.card (F.closure (R.oldGenerators : Set P)) ≤
        originalSourceUniformNormalCodeBudget S H * 2 ^ (3 * Nat.card (TypedProfileState S)+1) ∧
      ∀ f : Hom (F.closureStructure (R.oldGenerators : Set P)) (originalPartialTarget S H sap nr2),
        ∃ out : PathReconstructionRequests S H sap nr2 F C R hUnary cco hC,
          Nonempty (PathReconstructionRequests.ReconstructedPathPoints out) ∧
            C.IntervalWalk out.rootPoint 0 n := by
  obtain ⟨R,hLeaves,hRoots,hClosure,hPacket⟩ :=
    source_path_compression S H sap nr2 F C hn hUnary cco hC
  refine ⟨R,hLeaves,hRoots,hClosure,?_⟩
  intro f
  obtain ⟨out⟩ := hPacket f
  exact ⟨out,out.reconstruct_macro_path,out.whole_original_path⟩

end
end CCO.OldIdempotentForest
