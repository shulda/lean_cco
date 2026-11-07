import CCO.OldIdempotentForest.CycleReconstructionPieceWalks

/-! Boundary-preserving reconstruction from literal inserted piece lines.
The prescribed retained points are arbitrary real points, without a hidden
homomorphism or a source-splitting witness. -/

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
variable {n : Nat} (C : SupportedMacroChain S H sap nr2 F n)
variable (R : SourcePrunedForest S H sap nr2 F C)

structure PinnedMacroPoints (prescribed : ChainPoints C) where
  point : ChainPoints C
  sides : ∀ k : Fin n, PositiveWord.represented S (C.side k).word
    (point k.castSucc) (point k.succ)
  fixed : ∀ i : Fin (n+1), i.val ∈ R.pruning.retainedRoots 0 → point i = prescribed i
  first : point 0 = prescribed 0
  last : point (Fin.last n) = prescribed (Fin.last n)

/-- Read an actual inserted ORIGINAL interval line and split only along
its ORIGINAL macro indices, keeping the two prescribed values. -/
theorem interval_macro_walk_of_literal_line (fixed : ChainPoints C)
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (line : LiteralLine S (R.piecePath q hq).flatten
      (fixed ⟨q.start,by have hb := R.locatedBounds hq; omega⟩)
      (fixed ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩)) :
    Nonempty (IntervalMacroWalk C fixed q.start q.stop) := by
  have hb : q.start < q.stop ∧ q.stop ≤ n := R.locatedBounds hq
  have hp := represented_of_actual_literal_line S line
  obtain ⟨point,hfirst,hlast,hsides⟩ := C.represented_interval_original_sides
    q.start q.stop hb.1 hb.2 _ _ hp
  exact ⟨{
    positive := hb.1
    bounded := hb.2
    point := point
    first := fun _ => hfirst
    last := fun _ => hlast
    sides := hsides }⟩

/-- Every actual original piece line is used once, at the SAME retained
boundary values. No hidden Hom or reconstruction provider is assumed. -/
theorem pinned_macro_points_of_piece_lines
    (A : FiniteInduced (X := X)) (fixed : ChainPoints C)
    (lines : ∀ k : R.PieceIndex,
      FreshWordLine S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
        (fixed ⟨(R.indexedPiece k).start,by
          have hb := R.locatedBounds (R.indexedPiece_mem k); omega⟩)
        (fixed ⟨(R.indexedPiece k).stop,by
          have hb := R.locatedBounds (R.indexedPiece_mem k); omega⟩) A.vertices) :
    Nonempty (PinnedMacroPoints C R fixed) := by
  have given : ∀ q ∈ locate 0 R.pruning.pieces,
      Nonempty (IntervalMacroWalk C fixed q.start q.stop) := by
    intro q hq
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hq
    change R.indexedPiece k = q at hk
    subst q
    exact interval_macro_walk_of_literal_line C R fixed _ _ (lines k).toLiteralLine
  have hne : R.pruning.pieces ≠ [] := by
    intro hz
    have hn := R.pruning.word_ne_nil
    rw [← R.pruning.pieces_word,hz] at hn
    exact hn rfl
  obtain ⟨joined⟩ := recompose_piece_macro_walks C R.pruning.pieces hne 0 given
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
    · have hh : ChainFixedAt C joined.walk.point fixed i.val := by simpa only [he] using hf.1
      exact hh i.isLt
    · have hh : ChainFixedAt C joined.walk.point fixed i.val := by simpa only [he] using hf.2
      exact hh i.isLt
  · have hi : 0+(piecesWord R.pruning.pieces).length = n := by omega
    have hf := ChainFixedAt.congr C hi joined.walk.last
    exact hf (Nat.lt_succ_self n)

end
end CCO.OldIdempotentForest
