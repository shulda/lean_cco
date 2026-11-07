import CCO.StrongExact.ThetaLineRank
import CCO.GuardedTwoRoot.TypedPrefixStates
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

/-! The canonical ordered indices of the EXACT original positive word.
This is a literal word-position equivalence, not an arbitrary enumeration
of a finite vertex set. Every original atomic step is retained. -/

universe u v w
namespace CCO.OldIdempotentForest
open CCO.StrongExact CCO.GuardedTwoRoot
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def wordPositionEquiv {i j : ι} : (word : PositiveWord S i j) →
    wordPositions S word ≃ Fin (TypedPrefix.length S word + 1)
  | .single _ => finTwoEquiv.symm
  | .cons _ tail => (Equiv.optionCongr (wordPositionEquiv tail)).trans
      (finSuccEquiv (TypedPrefix.length S tail + 1)).symm

@[simp] theorem wordPositionEquiv_none {i j k : ι}
    (a : S.Atom i j) (tail : PositiveWord S j k) :
    wordPositionEquiv S (.cons a tail) none = 0 := by
  change (finSuccEquiv (TypedPrefix.length S tail + 1)).symm none = 0
  exact finSuccEquiv_symm_none

@[simp] theorem wordPositionEquiv_some {i j k : ι}
    (a : S.Atom i j) (tail : PositiveWord S j k) (p : wordPositions S tail) :
    wordPositionEquiv S (.cons a tail) (some p) = (wordPositionEquiv S tail p).succ := by
  change (finSuccEquiv (TypedPrefix.length S tail + 1)).symm
    (some (wordPositionEquiv S tail p)) = _
  exact finSuccEquiv_symm_some _

@[simp] theorem wordPositionEquiv_source {i j : ι} (word : PositiveWord S i j) :
    wordPositionEquiv S word (wordSource S word) = 0 := by
  cases word with
  | single a => rfl
  | cons a tail => exact wordPositionEquiv_none S a tail

@[simp] theorem wordPositionEquiv_target {i j : ι} (word : PositiveWord S i j) :
    wordPositionEquiv S word (wordTarget S word) = Fin.last (TypedPrefix.length S word) := by
  induction word with
  | single a => rfl
  | cons a tail ih =>
      change wordPositionEquiv S (.cons a tail) (some (wordTarget S tail)) = _
      rw [wordPositionEquiv_some,ih]
      rfl

theorem wordPositionEquiv_val {i j : ι} (word : PositiveWord S i j)
    (p : wordPositions S word) :
    (wordPositionEquiv S word p).val = wordPositionRank S word p := by
  induction word with
  | single a => cases p <;> rfl
  | cons a tail ih =>
      cases p with
      | none => rfl
      | some p =>
          rw [wordPositionEquiv_some]
          change (wordPositionEquiv S tail p).val + 1 = 1 + wordPositionRank S tail p
          rw [ih p]
          omega

/-- Every consecutive original index is the SAME original atomic letter,
including the first letter at a cons and the singleton-word case. -/
theorem original_edge_at_index {i j : ι} (word : PositiveWord S i j)
    (p : Fin (TypedPrefix.length S word)) :
    ∃ e : wordEdgeIndex S word,
      wordPositionEquiv S word (wordEdgeSource S word e) = p.castSucc ∧
      wordPositionEquiv S word (wordEdgeTarget S word e) = p.succ := by
  induction word with
  | single a =>
      change Fin 1 at p
      have hp : p = (0 : Fin 1) := Fin.eq_zero p
      subst p
      exact ⟨PUnit.unit,rfl,rfl⟩
  | cons a tail ih =>
      refine Fin.cases ?_ (fun q => ?_) p
      · refine ⟨Sum.inl PUnit.unit,?_,?_⟩
        · exact wordPositionEquiv_none S a tail
        · change wordPositionEquiv S (.cons a tail) (some (wordSource S tail)) = _
          rw [wordPositionEquiv_some,wordPositionEquiv_source]
          rfl
      · obtain ⟨e,hs,ht⟩ := ih q
        refine ⟨Sum.inr e,?_,?_⟩
        · change wordPositionEquiv S (.cons a tail) (some (wordEdgeSource S tail e)) = _
          rw [wordPositionEquiv_some,hs]
          rfl
        · change wordPositionEquiv S (.cons a tail) (some (wordEdgeTarget S tail e)) = _
          rw [wordPositionEquiv_some,ht]
          rfl

/-- Adjacency of literal word positions is precisely adjacency of their
ordered indices; this transports the actual path to a private-branch system. -/
theorem original_word_adjacent_iff {i j : ι} (word : PositiveWord S i j)
    (x y : wordPositions S word) :
    (∃ e : wordEdgeIndex S word,
      (wordEdgeSource S word e = x ∧ wordEdgeTarget S word e = y) ∨
      (wordEdgeSource S word e = y ∧ wordEdgeTarget S word e = x)) ↔
    (wordPositionEquiv S word x).val + 1 = (wordPositionEquiv S word y).val ∨
      (wordPositionEquiv S word y).val + 1 = (wordPositionEquiv S word x).val := by
  constructor
  · rintro ⟨e,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · left
      simpa only [wordPositionEquiv_val] using (wordEdge_rank_step S word e).symm
    · right
      simpa only [wordPositionEquiv_val] using (wordEdge_rank_step S word e).symm
  · intro h
    have forward (p q : wordPositions S word)
        (hpq : (wordPositionEquiv S word p).val + 1 = (wordPositionEquiv S word q).val) :
        ∃ e : wordEdgeIndex S word,
          wordEdgeSource S word e = p ∧ wordEdgeTarget S word e = q := by
      let t : Fin (TypedPrefix.length S word) :=
        ⟨(wordPositionEquiv S word p).val,by have := (wordPositionEquiv S word q).isLt; omega⟩
      obtain ⟨e,hs,ht⟩ := original_edge_at_index S word t
      refine ⟨e,(wordPositionEquiv S word).injective ?_,(wordPositionEquiv S word).injective ?_⟩
      · exact hs.trans (Fin.ext rfl)
      · exact ht.trans (Fin.ext hpq)
    rcases h with h | h
    · obtain ⟨e,hs,ht⟩ := forward x y h
      exact ⟨e,Or.inl ⟨hs,ht⟩⟩
    · obtain ⟨e,hs,ht⟩ := forward y x h
      exact ⟨e,Or.inr ⟨hs,ht⟩⟩

end CCO.OldIdempotentForest
