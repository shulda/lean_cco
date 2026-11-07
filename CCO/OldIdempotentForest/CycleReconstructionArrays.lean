import CCO.OldIdempotentForest.MacroIntervalsSourceChain
import CCO.OldIdempotentForest.PruningBounds

/-! Gluing actual realizations of the ORIGINAL interval words preserves
EVERY retained boundary representative. Merely choosing another walk of
the concatenated word would not preserve these intermediate old pins. -/

universe u v w r z a
namespace CCO.OldIdempotentForest
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {sap : AgeSAP S} {nr2 : Selectors.OriginalNR2 S}
variable {P : Type z} [Finite P]
variable {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
variable {n : Nat} (C : SupportedMacroChain S H sap nr2 F n)

abbrev ChainPoints := ∀ k : Fin (n+1), X (gapSort S H sap nr2 F (C.root k))

def ChainFixedAt (actual fixed : ChainPoints C) (i : Nat) : Prop :=
  ∀ hi : i < n+1, actual ⟨i,hi⟩ = fixed ⟨i,hi⟩

def ChainSideWalks (point : ChainPoints C) (lo hi : Nat) : Prop :=
  ∀ k : Fin n, lo ≤ k.val → k.val < hi →
    PositiveWord.represented S (C.side k).word (point k.castSucc) (point k.succ)

structure IntervalMacroWalk (fixed : ChainPoints C) (lo hi : Nat) where
  positive : lo < hi
  bounded : hi ≤ n
  point : ChainPoints C
  first : ChainFixedAt C point fixed lo
  last : ChainFixedAt C point fixed hi
  sides : ChainSideWalks C point lo hi

def splicePoints (left right : ChainPoints C) (middle : Nat) : ChainPoints C :=
  fun k => if k.val < middle then left k else right k

namespace IntervalMacroWalk
variable {C} {fixed : ChainPoints C} {lo mid hi : Nat}
variable (left : IntervalMacroWalk C fixed lo mid) (right : IntervalMacroWalk C fixed mid hi)

theorem middle_eq (hmid : mid < n+1) :
    left.point ⟨mid,hmid⟩ = right.point ⟨mid,hmid⟩ :=
  (left.last hmid).trans (right.first hmid).symm

def append : IntervalMacroWalk C fixed lo hi where
  positive := left.positive.trans right.positive
  bounded := right.bounded
  point := splicePoints C left.point right.point mid
  first h := by
    simp only [splicePoints,ite_eq_left left.positive]
    exact left.first h
  last h := by
    have hm : ¬ hi < mid := by have := right.positive; omega
    simp only [splicePoints,ite_eq_right hm]
    exact right.last h
  sides := by
    intro k hklo hkhi
    by_cases hkm : k.val < mid
    · have hs := left.sides k hklo hkm
      by_cases hsucc : k.val+1 < mid
      · simpa only [splicePoints,Fin.val_castSucc,Fin.val_succ,ite_eq_left hkm,
          ite_eq_left hsucc] using hs
      · have he : k.val+1 = mid := by omega
        subst mid
        have hsame : left.point k.succ = right.point k.succ := left.middle_eq right k.succ.isLt
        rw [hsame] at hs
        simpa only [splicePoints,Fin.val_castSucc,Fin.val_succ,ite_eq_left hkm,
          ite_eq_right hsucc] using hs
    · have hm : mid ≤ k.val := by omega
      have hs := right.sides k hm hkhi
      have hsucc : ¬ k.val+1 < mid := by omega
      simpa only [splicePoints,Fin.val_castSucc,Fin.val_succ,ite_eq_right hkm,
        ite_eq_right hsucc] using hs

theorem append_agrees_left (k : Fin (n+1)) (hk : k.val ≤ mid) :
    (left.append right).point k = left.point k := by
  by_cases hlt : k.val < mid
  · simp only [append,splicePoints,ite_eq_left hlt]
  · have he : k.val = mid := by omega
    have hmid : mid < n+1 := by omega
    have hk' : k = ⟨mid,hmid⟩ := Fin.ext he
    rw [hk']
    change (if mid < mid then _ else _) = _
    rw [ite_eq_right (Nat.lt_irrefl _)]
    exact (left.middle_eq right hmid).symm

theorem append_agrees_right (k : Fin (n+1)) (hk : mid ≤ k.val) :
    (left.append right).point k = right.point k := by
  have hlt : ¬ k.val < mid := by omega
  simp only [append,splicePoints,ite_eq_right hlt]

end IntervalMacroWalk

structure PieceMacroWalk (fixed : ChainPoints C) {A : Type a}
    (start : Nat) (pieces : List (Piece A)) where
  walk : IntervalMacroWalk C fixed start (start+(piecesWord pieces).length)
  boundaries : ∀ q ∈ locate start pieces,
    ChainFixedAt C walk.point fixed q.start ∧ ChainFixedAt C walk.point fixed q.stop

/-- Original interval witnesses are spliced at their SAME old root
points, preserving all retained boundary pins throughout the partition. -/
theorem recompose_piece_macro_walks {fixed : ChainPoints C} {A : Type a}
    (pieces : List (Piece A)) (hne : pieces ≠ []) (start : Nat)
    (given : ∀ q ∈ locate start pieces, Nonempty (IntervalMacroWalk C fixed q.start q.stop)) :
    Nonempty (PieceMacroWalk C fixed start pieces) := by
  induction pieces generalizing start with
  | nil => exact False.elim (hne rfl)
  | cons piece rest ih =>
    let head : LocatedPiece A := ⟨start,piece⟩
    obtain ⟨first⟩ := given head (by simp [head,locate])
    change IntervalMacroWalk C fixed start (start+piece.word.length) at first
    cases rest with
    | nil =>
      refine ⟨{
        walk := {
          positive := by simpa only [piecesWord_cons,piecesWord_nil,List.length_append,List.length_nil,Nat.add_zero] using first.positive
          bounded := by simpa only [piecesWord_cons,piecesWord_nil,List.length_append,List.length_nil,Nat.add_zero] using first.bounded
          point := first.point
          first := first.first
          last := by simpa only [piecesWord_cons,piecesWord_nil,List.length_append,List.length_nil,Nat.add_zero] using first.last
          sides := by simpa only [piecesWord_cons,piecesWord_nil,List.length_append,List.length_nil,Nat.add_zero] using first.sides }
        boundaries := ?_ }⟩
      intro q hq
      simp only [locate,List.mem_cons,List.not_mem_nil,or_false] at hq
      subst q
      exact ⟨first.first,first.last⟩
    | cons next tail =>
      obtain ⟨later⟩ := ih (by simp) (start+piece.word.length)
        (fun q hq => given q (List.mem_cons_of_mem _ hq))
      let combined := first.append later.walk
      refine ⟨{
        walk := {
          positive := by simpa only [piecesWord_cons,List.length_append,Nat.add_assoc] using combined.positive
          bounded := by simpa only [piecesWord_cons,List.length_append,Nat.add_assoc] using combined.bounded
          point := combined.point
          first := combined.first
          last := by simpa only [piecesWord_cons,List.length_append,Nat.add_assoc] using combined.last
          sides := by simpa only [piecesWord_cons,List.length_append,Nat.add_assoc] using combined.sides }
        boundaries := ?_ }⟩
      intro q hq
      rw [locate,List.mem_cons] at hq
      rcases hq with rfl | hq
      · constructor
        · intro h
          exact (first.append_agrees_left later.walk ⟨start,h⟩ (by simp [head,LocatedPiece.stop])).trans (first.first h)
        · intro h
          exact (first.append_agrees_right later.walk ⟨start+piece.word.length,h⟩ (Nat.le_refl _)).trans (later.walk.first h)
      · have hbound := locate_bounds hq
        have hf := later.boundaries q hq
        constructor
        · intro h
          exact (first.append_agrees_right later.walk ⟨q.start,h⟩ hbound.1).trans (hf.1 h)
        · intro h
          exact (first.append_agrees_right later.walk ⟨q.stop,h⟩
            (by change start+piece.word.length ≤ q.stop; omega)).trans (hf.2 h)

/-- Conversely, every recorded retained OLD root is the endpoint of an
actual retained original singleton piece. This lets reconstruction pins
be read from the literal piece-boundary equalities above. -/
theorem PruningTree.retainedRoot_piece {A : Type a} (p : PruningTree A)
    (start : Nat) {i : Nat} (hi : i ∈ p.retainedRoots start) :
    ∃ q ∈ locate start p.pieces, q.piece.IsKept ∧ (q.start = i ∨ q.stop = i) := by
  induction p generalizing start with
  | leaf x =>
    simp only [PruningTree.retainedRoots,Finset.mem_insert,Finset.mem_singleton] at hi
    refine ⟨⟨start,.kept x⟩,by simp [PruningTree.pieces,locate],True.intro,?_⟩
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | branch left middle right ihl ihr =>
    simp only [PruningTree.retainedRoots,Finset.mem_union] at hi
    rw [PruningTree.locate_branch]
    rcases hi with hi | hi
    · obtain ⟨q,hq,hkeep,hend⟩ := ihl start hi
      exact ⟨q,List.mem_append_left _ (List.mem_append_left _ hq),hkeep,hend⟩
    · obtain ⟨q,hq,hkeep,hend⟩ := ihr (start+left.word.length+middle.length) hi
      exact ⟨q,List.mem_append_right _ hq,hkeep,hend⟩

end
end CCO.OldIdempotentForest
