import Mathlib.Data.List.Range

/-! Ordered positive pieces retain the ORIGINAL list, including repeated
letter occurrences. Cumulative lengths give contiguous half-open intervals;
their occurrence indices partition the original word exactly once. -/

universe u
namespace CCO.OldIdempotentForest

inductive Piece (A : Type u) where
  | kept (letter : A)
  | gap (word : List A) (nonempty : word ≠ [])

namespace Piece
variable {A : Type u}
def word : Piece A → List A
  | .kept a => [a]
  | .gap w _ => w
def IsKept : Piece A → Prop
  | .kept _ => True
  | .gap _ _ => False
theorem word_ne_nil (p : Piece A) : p.word ≠ [] := by
  cases p with
  | kept a => simp [word]
  | gap w h => exact h
theorem length_pos (p : Piece A) : 0 < p.word.length :=
  List.length_pos_iff.mpr p.word_ne_nil
end Piece

def piecesWord {A : Type u} (pieces : List (Piece A)) : List A :=
  pieces.flatMap Piece.word

@[simp] theorem piecesWord_nil {A : Type u} : piecesWord ([] : List (Piece A)) = [] := rfl
@[simp] theorem piecesWord_cons {A : Type u} (p : Piece A) (ps : List (Piece A)) :
    piecesWord (p :: ps) = p.word ++ piecesWord ps := rfl
@[simp] theorem piecesWord_append {A : Type u} (ps qs : List (Piece A)) :
    piecesWord (ps ++ qs) = piecesWord ps ++ piecesWord qs := List.flatMap_append

structure LocatedPiece (A : Type u) where
  start : Nat
  piece : Piece A

def LocatedPiece.stop {A : Type u} (p : LocatedPiece A) : Nat := p.start + p.piece.word.length

def locate {A : Type u} (start : Nat) : List (Piece A) → List (LocatedPiece A)
  | [] => []
  | p :: ps => ⟨start,p⟩ :: locate (start + p.word.length) ps

theorem locate_append {A : Type u} (start : Nat) (ps qs : List (Piece A)) :
    locate start (ps ++ qs) = locate start ps ++
      locate (start + (piecesWord ps).length) qs := by
  induction ps generalizing start with
  | nil => simp [locate]
  | cons p ps ih => simp [locate,ih,List.length_append,Nat.add_assoc]

theorem locate_bounds {A : Type u} {start : Nat} {ps : List (Piece A)}
    {p : LocatedPiece A} (hp : p ∈ locate start ps) :
    start ≤ p.start ∧ p.start < p.stop ∧ p.stop ≤ start + (piecesWord ps).length := by
  induction ps generalizing start with
  | nil => simp [locate] at hp
  | cons q qs ih =>
    simp only [locate,List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hq := q.length_pos
      simp only [LocatedPiece.stop,piecesWord_cons,List.length_append]
      omega
    · have h := ih hp
      simp only [piecesWord_cons,List.length_append]
      omega

theorem locate_ordered {A : Type u} (start : Nat) (ps : List (Piece A)) :
    (locate start ps).Pairwise (fun p q => p.stop ≤ q.start) := by
  induction ps generalizing start with
  | nil => exact List.Pairwise.nil
  | cons p ps ih =>
    apply List.Pairwise.cons _ (ih _)
    intro q hq
    exact (locate_bounds hq).1

/-- The interval list covers every original occurrence once, in order. -/
theorem locate_indices {A : Type u} (start : Nat) (ps : List (Piece A)) :
    (locate start ps).flatMap (fun p => List.range' p.start p.piece.word.length) =
      List.range' start (piecesWord ps).length := by
  induction ps generalizing start with
  | nil => simp [locate]
  | cons p ps ih =>
    simp only [locate,List.flatMap_cons,piecesWord_cons,List.length_append]
    rw [ih,← List.range'_append_1]

/-- Each output piece is literally a contiguous block of the original
word, at the recorded original occurrence position. -/
theorem locate_original_split {A : Type u} {start : Nat} {ps : List (Piece A)}
    {p : LocatedPiece A} (hp : p ∈ locate start ps) :
    ∃ before after : List A,
      piecesWord ps = before ++ p.piece.word ++ after ∧
      p.start = start + before.length := by
  induction ps generalizing start with
  | nil => simp [locate] at hp
  | cons q qs ih =>
    simp only [locate,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨[],piecesWord qs,rfl,by simp⟩
    · obtain ⟨before,after,heq,hstart⟩ := ih hp
      refine ⟨q.word ++ before,after,?_,?_⟩
      · simp only [piecesWord_cons,heq,List.append_assoc]
      · simp only [List.length_append]
        omega

theorem locate_disjoint {A : Type u} (start : Nat) (ps : List (Piece A)) :
    (locate start ps).Pairwise
      (fun p q => ∀ i, p.start ≤ i → i < p.stop → ¬ (q.start ≤ i ∧ i < q.stop)) := by
  apply (locate_ordered start ps).imp
  intro p q hpq i hpi hip hqi
  omega

theorem locate_piece_mem {A : Type u} {start : Nat} {ps : List (Piece A)}
    {p : LocatedPiece A} (hp : p ∈ locate start ps) : p.piece ∈ ps := by
  induction ps generalizing start with
  | nil => simp [locate] at hp
  | cons q qs ih =>
    simp only [locate,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp)

/-- Cumulative positions name the canonical ORIGINAL interval slice. -/
theorem locate_canonical_slice {A : Type u} {ps : List (Piece A)}
    {p : LocatedPiece A} (hp : p ∈ locate 0 ps) :
    ((piecesWord ps).drop p.start).take (p.stop - p.start) = p.piece.word := by
  obtain ⟨before,after,heq,hstart⟩ := locate_original_split hp
  simp only [LocatedPiece.stop,Nat.add_sub_cancel_left]
  simp [heq,hstart]

end CCO.OldIdempotentForest
