import CCO.OldIdempotentForest.Intervals
import CCO.FactorizationForest.Provider

/-! Supplied-tree pruning. A retained node has two children and an opaque
whole original middle word. No pruning data is constructed inside a deleted
middle. The original ordered yield is preserved literally. -/

universe u v
namespace CCO.OldIdempotentForest

inductive PruningTree (A : Type u) where
  | leaf (letter : A)
  | branch (left : PruningTree A) (middle : List A) (right : PruningTree A)

namespace PruningTree
variable {A : Type u}
def word : PruningTree A → List A
  | .leaf a => [a]
  | .branch l middle r => l.word ++ middle ++ r.word
def height : PruningTree A → Nat
  | .leaf _ => 0
  | .branch l _ r => 1 + max l.height r.height
def leaves : PruningTree A → Nat
  | .leaf _ => 1
  | .branch l _ r => l.leaves + r.leaves
def nodes : PruningTree A → Nat
  | .leaf _ => 1
  | .branch l _ r => 1 + l.nodes + r.nodes
noncomputable def pieces : PruningTree A → List (Piece A)
  | .leaf a => [.kept a]
  | .branch l middle r => by
      classical
      exact l.pieces ++ (if h : middle = [] then [] else [.gap middle h]) ++ r.pieces

theorem pieces_word (p : PruningTree A) : piecesWord p.pieces = p.word := by
  induction p with
  | leaf a => rfl
  | branch l middle r ihl ihr =>
    classical
    by_cases h : middle = [] <;> simp [pieces,Piece.word,word,h,ihl,ihr]

theorem word_ne_nil (p : PruningTree A) : p.word ≠ [] := by
  induction p with
  | leaf a => simp [word]
  | branch l middle r ihl ihr => simp [word,ihl]

def gapWords : PruningTree A → List (List A)
  | .leaf _ => []
  | .branch l middle r => l.gapWords ++ (if middle = [] then [] else [middle]) ++ r.gapWords

theorem gapWords_nonempty {p : PruningTree A} {g : List A} (hg : g ∈ p.gapWords) : g ≠ [] := by
  induction p with
  | leaf a => simp [gapWords] at hg
  | branch l middle r ihl ihr =>
    simp only [gapWords,List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact ihl hg
    · split at hg
      · simp at hg
      · have he : g = middle := List.mem_singleton.mp hg
        exact he ▸ ‹middle ≠ []›
    · exact ihr hg
end PruningTree

/-- This relation records the actual stopped algorithm. At an idempotent
node only first and last receive recursive proofs; the WHOLE middle yield
is copied, and its descendants produce no deletion records. A two-child
idempotent node has an empty middle and therefore records no gap. -/
inductive Prunes {A : Type u} : FactorizationTree A → PruningTree A → Prop
  | leaf (a : A) : Prunes (.leaf a) (.leaf a)
  | binary {l r : FactorizationTree A} {pl pr : PruningTree A}
      (left : Prunes l pl) (right : Prunes r pr) :
      Prunes (.binary l r) (.branch pl [] pr)
  | idempotent {l r : FactorizationTree A} (middle : List (FactorizationTree A))
      {pl pr : PruningTree A} (left : Prunes l pl) (right : Prunes r pr) :
      Prunes (.idempotent (l :: middle ++ [r]))
        (.branch pl (FactorizationTree.listValue middle) pr)

private theorem split_nonempty_last {A : Type u} (xs : List A) (h : xs ≠ []) :
    ∃ before last, xs = before ++ [last] := by
  induction xs with
  | nil => exact False.elim (h rfl)
  | cons a xs ih =>
    cases xs with
    | nil => exact ⟨[],a,rfl⟩
    | cons b bs =>
      obtain ⟨before,last,heq⟩ := ih (by simp)
      exact ⟨a :: before,last,congrArg (List.cons a) heq⟩

private theorem split_children {A : Type u} (xs : List A) (h : 2 ≤ xs.length) :
    ∃ first middle last, xs = first :: middle ++ [last] := by
  cases xs with
  | nil => simp at h
  | cons first tail =>
    have hn : tail ≠ [] := by intro he; simp [he] at h
    obtain ⟨middle,last,heq⟩ := split_nonempty_last tail hn
    exact ⟨first,middle,last,congrArg (List.cons first) heq⟩

theorem exists_stopped_pruning {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M) (t : FactorizationTree A) (ht : t.IsRamsey eval) :
    ∃ p : PruningTree A, Prunes t p := by
  induction t using FactorizationTree.induction_on with
  | h_leaf a => exact ⟨.leaf a,.leaf a⟩
  | h_binary l r ihl ihr =>
    rw [FactorizationTree.isRamsey_binary] at ht
    obtain ⟨pl,hpl⟩ := ihl ht.1
    obtain ⟨pr,hpr⟩ := ihr ht.2
    exact ⟨.branch pl [] pr,.binary hpl hpr⟩
  | h_idempotent children ih =>
    rw [FactorizationTree.isRamsey_idempotent,FactorizationTree.listIsRamsey_iff] at ht
    obtain ⟨first,middle,last,heq⟩ := split_children children ht.1
    subst children
    obtain ⟨pl,hpl⟩ := ih first (by simp) (ht.2.1 first (by simp))
    obtain ⟨pr,hpr⟩ := ih last (by simp) (ht.2.1 last (by simp))
    exact ⟨.branch pl (FactorizationTree.listValue middle) pr,.idempotent middle hpl hpr⟩

noncomputable def stoppedPruning {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M) (t : FactorizationTree A) (ht : t.IsRamsey eval) : PruningTree A :=
  Classical.choose (exists_stopped_pruning eval t ht)

theorem stoppedPruning_spec {A : Type u} {M : Type v} [Semigroup M]
    (eval : List A → M) (t : FactorizationTree A) (ht : t.IsRamsey eval) :
    Prunes t (stoppedPruning eval t ht) := Classical.choose_spec (exists_stopped_pruning eval t ht)

theorem tree_listValue_append {A : Type u} (xs ys : List (FactorizationTree A)) :
    FactorizationTree.listValue (xs ++ ys) =
      FactorizationTree.listValue xs ++ FactorizationTree.listValue ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [FactorizationTree.listValue,ih,List.append_assoc]

theorem Prunes.word {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (h : Prunes t p) : p.word = t.value := by
  induction h with
  | leaf a => rfl
  | binary hl hr ihl ihr => simp [PruningTree.word,FactorizationTree.value,ihl,ihr]
  | idempotent middle hl hr ihl ihr =>
    simp [PruningTree.word,FactorizationTree.value,FactorizationTree.listValue,
      tree_listValue_append,ihl,ihr,List.append_assoc]

theorem Prunes.height_le {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (h : Prunes t p) : p.height ≤ t.height := by
  induction h with
  | leaf a => exact Nat.le_refl _
  | binary hl hr ihl ihr =>
    exact Nat.add_le_add_left (max_le_max ihl ihr) 1
  | @idempotent l r middle pl pr hl hr ihl ihr =>
    apply Nat.add_le_add_left
    apply max_le
    · exact ihl.trans (FactorizationTree.height_le_listHeight (by simp))
    · exact ihr.trans (FactorizationTree.height_le_listHeight (by simp))

/-- A supplied valid tree's pieces are exact ORIGINAL contiguous intervals
in order; the index equality also records every occurrence exactly once. -/
theorem Prunes.exact_partition {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (h : Prunes t p) :
    piecesWord p.pieces = t.value ∧
    (locate 0 p.pieces).flatMap (fun q => List.range' q.start q.piece.word.length) =
      List.range' 0 t.value.length ∧
    (locate 0 p.pieces).Pairwise (fun q r => q.stop ≤ r.start) := by
  refine ⟨p.pieces_word.trans h.word,?_,locate_ordered _ _⟩
  rw [locate_indices,p.pieces_word,h.word]

theorem Prunes.located_bounds {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (h : Prunes t p) {q : LocatedPiece A} (hq : q ∈ locate 0 p.pieces) :
    q.start < q.stop ∧ q.stop ≤ t.value.length := by
  have hb := locate_bounds hq
  rw [p.pieces_word,h.word] at hb
  simpa using hb.2

theorem Prunes.located_slice {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (h : Prunes t p) {q : LocatedPiece A} (hq : q ∈ locate 0 p.pieces) :
    (t.value.drop q.start).take (q.stop - q.start) = q.piece.word := by
  have hs := locate_canonical_slice hq
  rw [p.pieces_word,h.word] at hs
  exact hs

end CCO.OldIdempotentForest
