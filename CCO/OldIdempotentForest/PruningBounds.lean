import CCO.OldIdempotentForest.StoppedPruning
import Mathlib.Data.Finset.Card

/-! Binary retention bounds and persistence of literal ORIGINAL root
positions. Gaps may separate retained leaves, so the correct root bound
is twice their number, rather than their number plus one. -/

universe u
namespace CCO.OldIdempotentForest
namespace PruningTree
variable {A : Type u}

def retainedRoots (p : PruningTree A) (start : Nat) : Finset Nat :=
  match p with
  | .leaf _ => {start,start + 1}
  | .branch l middle r => l.retainedRoots start ∪
      r.retainedRoots (start + l.word.length + middle.length)

theorem first_root_mem (p : PruningTree A) (start : Nat) : start ∈ p.retainedRoots start := by
  induction p generalizing start with
  | leaf a => simp [retainedRoots]
  | branch l middle r ihl ihr => exact Finset.mem_union_left _ (ihl start)

theorem last_root_mem (p : PruningTree A) (start : Nat) :
    start + p.word.length ∈ p.retainedRoots start := by
  induction p generalizing start with
  | leaf a => simp [word,retainedRoots]
  | branch l middle r ihl ihr =>
    apply Finset.mem_union_right
    simpa only [word,List.length_append,Nat.add_assoc] using
      ihr (start + l.word.length + middle.length)

theorem retainedRoots_bounds {p : PruningTree A} {start i : Nat}
    (hi : i ∈ p.retainedRoots start) : start ≤ i ∧ i ≤ start + p.word.length := by
  induction p generalizing start with
  | leaf a =>
    simp only [retainedRoots,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [word,List.length_singleton]
    rcases hi with rfl | rfl <;> omega
  | branch l middle r ihl ihr =>
    simp only [retainedRoots,Finset.mem_union] at hi
    simp only [word,List.length_append]
    rcases hi with hi | hi
    · have h := ihl hi
      omega
    · have h := ihr hi
      omega

theorem locate_branch (l : PruningTree A) (middle : List A) (r : PruningTree A) (start : Nat) :
    locate start (PruningTree.branch l middle r).pieces =
      locate start l.pieces ++
      (if h : middle = [] then [] else [⟨start + l.word.length,.gap middle h⟩]) ++
      locate (start + l.word.length + middle.length) r.pieces := by
  classical
  by_cases hm : middle = [] <;>
    simp [pieces,hm,locate_append,pieces_word,locate,Piece.word,Nat.add_assoc]

/-- Every retained piece AND every whole deleted interval has both old
boundary positions among endpoints of the retained ORIGINAL leaves. -/
theorem piece_boundaries_mem (p : PruningTree A) (start : Nat)
    {q : LocatedPiece A} (hq : q ∈ locate start p.pieces) :
    q.start ∈ p.retainedRoots start ∧ q.stop ∈ p.retainedRoots start := by
  induction p generalizing start with
  | leaf a =>
    simp only [pieces,locate,List.mem_cons,List.not_mem_nil,or_false] at hq
    subst q
    simp [retainedRoots,LocatedPiece.stop,Piece.word]
  | branch l middle r ihl ihr =>
    rw [locate_branch] at hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · have h := ihl start hq
      exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2⟩
    · split at hq
      · simp at hq
      · have he := List.mem_singleton.mp hq
        subst q
        exact ⟨Finset.mem_union_left _ (l.last_root_mem start),
          Finset.mem_union_right _ (r.first_root_mem (start + l.word.length + middle.length))⟩
    · have h := ihr (start + l.word.length + middle.length) hq
      exact ⟨Finset.mem_union_right _ h.1,Finset.mem_union_right _ h.2⟩

theorem leaves_le_pow_height (p : PruningTree A) : p.leaves ≤ 2 ^ p.height := by
  induction p with
  | leaf a => exact Nat.le_refl _
  | branch l middle r ihl ihr =>
    have hl := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_max_left l.height r.height)
    have hr := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_max_right l.height r.height)
    change l.leaves + r.leaves ≤ 2 ^ (1 + max l.height r.height)
    rw [Nat.add_comm 1, Nat.pow_succ]
    omega

theorem nodes_add_one (p : PruningTree A) : p.nodes + 1 = 2 * p.leaves := by
  induction p with
  | leaf a => rfl
  | branch l middle r ihl ihr =>
    simp only [nodes,leaves]
    omega

theorem nodes_le_pow_height (p : PruningTree A) : p.nodes ≤ 2 ^ (p.height + 1) - 1 := by
  have hl := p.leaves_le_pow_height
  have hn := p.nodes_add_one
  rw [Nat.pow_succ]
  omega

theorem retainedRoots_card_le (p : PruningTree A) (start : Nat) :
    (p.retainedRoots start).card ≤ 2 * p.leaves := by
  induction p generalizing start with
  | leaf a => simp [retainedRoots,leaves]
  | branch l middle r ihl ihr =>
    have hc := Finset.card_union_le (l.retainedRoots start)
      (r.retainedRoots (start + l.word.length + middle.length))
    have hl := ihl start
    have hr := ihr (start + l.word.length + middle.length)
    change (l.retainedRoots start ∪
      r.retainedRoots (start + l.word.length + middle.length)).card ≤ 2 * (l.leaves + r.leaves)
    omega

theorem retainedRoots_card_le_pow (p : PruningTree A) (start : Nat) :
    (p.retainedRoots start).card ≤ 2 ^ (p.height + 1) := by
  have hc := p.retainedRoots_card_le start
  have hl := p.leaves_le_pow_height
  rw [Nat.pow_succ]
  omega

end PruningTree

/-- C28--C29: the SAME supplied forest height controls retained leaves,
binary nodes and OLD roots, including all gap boundaries. -/
theorem Prunes.uniform_bounds {A : Type u} {t : FactorizationTree A} {p : PruningTree A}
    (hp : Prunes t p) :
    p.leaves ≤ 2 ^ t.height ∧ p.nodes ≤ 2 ^ (t.height + 1) - 1 ∧
      (p.retainedRoots 0).card ≤ 2 ^ (t.height + 1) := by
  have hh := hp.height_le
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hh
  have hpow' := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.add_le_add_right hh 1)
  exact ⟨p.leaves_le_pow_height.trans hpow,
    p.nodes_le_pow_height.trans (Nat.sub_le_sub_right hpow' 1),
    (p.retainedRoots_card_le_pow 0).trans hpow'⟩

end CCO.OldIdempotentForest
