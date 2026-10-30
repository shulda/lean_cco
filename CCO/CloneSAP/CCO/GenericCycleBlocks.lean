import CCO.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! A cyclic sequence of pairwise vertex-disjoint simple path blocks,
joined by actual bridge edges, is a genuine simple cycle. Empty blocks
(one vertex) are permitted. All block and bridge edges are retained. -/
universe z
namespace CCO.CloneSAP.CCO
variable {V : Type z} (G : SimpleGraph V)

structure WalkBlock where
  first : V
  last : V
  walk : G.Walk first last

namespace WalkBlock
variable {G}

def prefixWalk {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (k : Fin (n+1)) : G.Walk (bs 0).first (bs k).last :=
  Fin.induction (bs 0).walk
    (fun i p => p.append (.cons (bridge i) (bs i.succ).walk)) k

@[simp] theorem prefixWalk_zero {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first) :
    prefixWalk bs bridge 0 = (bs 0).walk := rfl

@[simp] theorem prefixWalk_succ {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first) (k : Fin n) :
    prefixWalk bs bridge k.succ =
      (prefixWalk bs bridge k.castSucc).append (.cons (bridge k) (bs k.succ).walk) := rfl

/-- Every vertex in the concatenation still lies in its original block. -/
theorem prefix_support {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (k : Fin (n+1)) :
    ∀ x ∈ (prefixWalk bs bridge k).support,
      ∃ i : Fin (n+1), i.val ≤ k.val ∧ x ∈ (bs i).walk.support := by
  induction k using Fin.induction with
  | zero =>
    intro x hx
    exact ⟨0,le_rfl,by simpa only [prefixWalk_zero] using hx⟩
  | succ k ih =>
    intro x hx
    rw [prefixWalk_succ,SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons,List.tail_cons,List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i,hi,hx⟩ := ih x hx
      exact ⟨i,by have := hi; simp only [Fin.val_castSucc,Fin.val_succ] at *; omega,hx⟩
    · exact ⟨k.succ,le_rfl,hx⟩

theorem prefix_isPath {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (hp : ∀ i, (bs i).walk.IsPath)
    (disj : ∀ i j, i ≠ j → (bs i).walk.support.Disjoint (bs j).walk.support)
    (k : Fin (n+1)) : (prefixWalk bs bridge k).IsPath := by
  induction k using Fin.induction with
  | zero => exact hp 0
  | succ k ih =>
    apply SimpleGraph.Walk.IsPath.mk'
    rw [prefixWalk_succ,SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons,List.tail_cons,List.nodup_append]
    refine ⟨ih.support_nodup,(hp k.succ).support_nodup,?_⟩
    intro a ha b hb hab
    subst b
    obtain ⟨i,hi,ha⟩ := prefix_support bs bridge k.castSucc a ha
    have hne : i ≠ k.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_succ] at hi hv
      omega
    exact disj i k.succ hne ha hb

/-- Each connector contributes a real edge, even if all blocks are nil. -/
theorem prefix_length {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (k : Fin (n+1)) : k.val ≤ (prefixWalk bs bridge k).length := by
  induction k using Fin.induction with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    simp only [prefixWalk_succ,SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons,Fin.val_succ,Fin.val_castSucc] at *
    omega

theorem prefix_block_edges {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (k : Fin (n+1)) :
    ∀ (i : Fin (n+1)), i.val ≤ k.val → ∀ e,
      e ∈ (bs i).walk.edges → e ∈ (prefixWalk bs bridge k).edges := by
  induction k using Fin.induction with
  | zero =>
    intro i hi e he
    have hei : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hi)
    subst i
    exact he
  | succ k ih =>
    intro i hi e he
    rw [prefixWalk_succ,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,List.mem_append]
    by_cases hei : i = k.succ
    · subst i
      exact Or.inr (List.mem_cons_of_mem _ he)
    · exact Or.inl (ih i (by
        have hn : i.val ≠ k.val+1 := fun hh => hei (Fin.ext hh)
        simp only [Fin.val_succ,Fin.val_castSucc] at *
        omega) e he)

theorem prefix_bridge_edges {n : ℕ} (bs : Fin (n+1) → WalkBlock G)
    (bridge : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first)
    (k : Fin (n+1)) :
    ∀ (i : Fin n), i.val < k.val →
      s((bs i.castSucc).last,(bs i.succ).first) ∈ (prefixWalk bs bridge k).edges := by
  induction k using Fin.induction with
  | zero => intro i hi; exact (Nat.not_lt_zero _ hi).elim
  | succ k ih =>
    intro i hi
    rw [prefixWalk_succ,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,List.mem_append]
    by_cases hei : i = k
    · subst i
      exact Or.inr (List.mem_cons_self)
    · exact Or.inl (ih i (by
        have hn : i.val ≠ k.val := fun hh => hei (Fin.ext hh)
        simp only [Fin.val_succ,Fin.val_castSucc] at *
        omega))

end WalkBlock

/-- Contracting each disjoint path block gives the designated cycle of
blocks. Expanding the blocks retains a genuine original simple cycle,
with every original internal and bridge edge available for readout. -/
theorem cyclic_blocks {n : ℕ} (hn : 3 ≤ n) (bs : Fin n → WalkBlock G)
    (hp : ∀ i, (bs i).walk.IsPath)
    (disj : ∀ i j, i ≠ j → (bs i).walk.support.Disjoint (bs j).walk.support)
    (bridge : ∀ i, G.Adj (bs i).last (bs (cyclicNext (by omega) i)).first) :
    ∃ x, ∃ r : G.Walk x x, r.IsCycle ∧
      (∀ i e, e ∈ (bs i).walk.edges → e ∈ r.edges) ∧
      (∀ i, s((bs i).last,(bs (cyclicNext (by omega) i)).first) ∈ r.edges) := by
  cases n with
  | zero => omega
  | succ n =>
    have hpos : 0 < n+1 := by omega
    have hnext (i : Fin n) : cyclicNext hpos i.castSucc = i.succ :=
      Fin.ext (Nat.mod_eq_of_lt i.succ.isLt)
    let linear : ∀ i : Fin n, G.Adj (bs i.castSucc).last (bs i.succ).first :=
      fun i => by simpa only [hnext] using bridge i.castSucc
    have hlast : cyclicNext hpos (Fin.last n) = 0 := Fin.ext (Nat.mod_self _)
    have close : G.Adj (bs (Fin.last n)).last (bs 0).first := by
      simpa only [hlast] using bridge (Fin.last n)
    let p := WalkBlock.prefixWalk bs linear (Fin.last n)
    let r : G.Walk (bs (Fin.last n)).last (bs (Fin.last n)).last := .cons close p
    refine ⟨_,r,?_,?_,?_⟩
    · apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · dsimp only [r]
        rw [SimpleGraph.Walk.tail_cons]
        exact (SimpleGraph.Walk.isPath_copy p (SimpleGraph.Walk.getVert_zero p).symm rfl).mpr
          (WalkBlock.prefix_isPath bs linear hp disj (Fin.last n))
      · have hh := WalkBlock.prefix_length bs linear (Fin.last n)
        change 3 ≤ p.length+1
        change n ≤ p.length at hh
        omega
    · intro i e he
      apply List.mem_cons_of_mem
      exact WalkBlock.prefix_block_edges bs linear (Fin.last n) i (by
        have := i.isLt
        simp only [Fin.val_last]
        omega) e he
    · intro i
      by_cases hi : i = Fin.last n
      · subst i
        change s((bs (Fin.last n)).last,(bs (cyclicNext hpos (Fin.last n))).first) ∈ _
        rw [hlast]
        exact List.mem_cons_self
      · have hlt : i.val < n := by
          have hne : i.val ≠ n := fun he => hi (Fin.ext he)
          have := i.isLt
          omega
        let j : Fin n := ⟨i.val,hlt⟩
        have hcast : j.castSucc = i := Fin.ext rfl
        have hsucc : cyclicNext hpos i = j.succ := by rw [← hcast,hnext]
        rw [hsucc,← hcast]
        apply List.mem_cons_of_mem
        exact WalkBlock.prefix_bridge_edges bs linear (Fin.last n) j (by simpa using hlt)

end CCO.CloneSAP.CCO
