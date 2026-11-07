import Mathlib.Data.List.Chain
import Mathlib.Data.List.Duplicate
import Lean.Elab.Tactic.Omega

/-! Loop deletion in a finite directed state trace. The first state is
retained. In the source application it is the prefix after the FIRST
diversity letter, never an empty prefix or an adjoined STRONG identity. -/

namespace CCO.GuardedTwoRoot.TypedPrefix
variable {A : Type*} {R : A → A → Prop}

theorem duplicate_split {x : A} {l : List A} (h : List.Duplicate x l) :
    ∃ a b c : List A, l = a ++ x :: (b ++ x :: c) := by
  induction h with
  | cons_mem h =>
    obtain ⟨b,c,hbc⟩ := List.mem_iff_append.mp h
    exact ⟨[],b,c,by simp only [List.nil_append,hbc]⟩
  | @cons_duplicate y l h ih =>
    obtain ⟨a,b,c,he⟩ := ih
    exact ⟨y :: a,b,c,by simp only [List.cons_append,he]⟩

/-- Deleting the return loop preserves the two endpoint states and all
remaining directed steps; the retained occurrence of x is not deleted. -/
theorem delete_return_loop (a b c : List A) (x : A)
    (h : (a ++ x :: (b ++ x :: c)).IsChain R) :
    (a ++ x :: c).IsChain R ∧
      (a ++ x :: c).head? = (a ++ x :: (b ++ x :: c)).head? ∧
      (a ++ x :: c).getLast? = (a ++ x :: (b ++ x :: c)).getLast? ∧
      (a ++ x :: c).length < (a ++ x :: (b ++ x :: c)).length := by
  have hFirst := (List.isChain_split.mp h).1
  have hAfter := (List.isChain_split.mp h).2
  have hLast := (List.isChain_cons_split.mp hAfter).2
  refine ⟨?_,?_,?_,?_⟩
  · have hc := List.IsChain.append_overlap hFirst
      (show ([x] ++ c).IsChain R from hLast) (by simp)
    simpa only [List.append_assoc,List.singleton_append] using hc
  · cases a <;> rfl
  · have he : a ++ x :: (b ++ x :: c) = (a ++ x :: b) ++ x :: c := by
      simp only [List.append_assoc,List.cons_append]
    rw [he,List.getLast?_append_cons,List.getLast?_append_cons]
  · simp only [List.length_append,List.length_cons]
    omega

/-- A shortest state trace cannot repeat a state. There is no zeroth
state in this lemma's positive-prefix application. -/
theorem shortest_chain_nodup (l : List A) (hChain : l.IsChain R)
    (minimal : ∀ m : List A, m.IsChain R → m.head? = l.head? →
      m.getLast? = l.getLast? → l.length ≤ m.length) : l.Nodup := by
  classical
  by_contra hNodup
  obtain ⟨x,hx⟩ := List.exists_duplicate_iff_not_nodup.mpr hNodup
  obtain ⟨a,b,c,rfl⟩ := duplicate_split hx
  obtain ⟨hc,hh,hl,hlt⟩ := delete_return_loop a b c x hChain
  exact Nat.not_lt_of_ge (minimal (a ++ x :: c) hc hh hl) hlt

end CCO.GuardedTwoRoot.TypedPrefix
