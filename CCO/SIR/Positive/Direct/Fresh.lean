import CCO.SIR.Positive.Direct.Homogeneity
import CCO.SIR.Positive.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

namespace CCO.SIR.Positive.Direct

/-- A parent is anchored precisely when the displayed real base meets it. -/
def Anchored (C : Finset Point) (p : ℕ) : Prop := ∃ c ∈ C, parent c = p

noncomputable def parentBound (B C : Finset Point) : ℕ := (B ∪ C).sup parent + 1
noncomputable def indexBound (B C : Finset Point) : ℕ := (B ∪ C).sup index + 1

theorem parent_lt_bound {B C : Finset Point} {x : Point} (hx : x ∈ B ∪ C) :
    parent x < parentBound B C :=
  Nat.lt_succ_of_le (Finset.le_sup hx)
theorem index_lt_bound {B C : Finset Point} {x : Point} (hx : x ∈ B ∪ C) :
    index x < indexBound B C :=
  Nat.lt_succ_of_le (Finset.le_sup hx)

noncomputable def freshParent (B C : Finset Point) (p : ℕ) : ℕ := by
  classical
  exact if Anchored C p then p else parentBound B C + p

theorem freshParent_injective (B C : Finset Point) :
    Function.Injective (freshParent B C) := by
  classical
  intro p q h
  unfold freshParent at h
  split_ifs at h with hp hq hq
  · exact h
  · rcases hp with ⟨c,hc,rfl⟩
    have hb := parent_lt_bound (B := B) (C := C) (Finset.mem_union_right B hc)
    omega
  · rcases hq with ⟨c,hc,rfl⟩
    have hb := parent_lt_bound (B := B) (C := C) (Finset.mem_union_right B hc)
    omega
  · exact Nat.add_left_cancel h

/-- Keep the prescribed base, move every other real point into a fresh
fibre location, and move unanchored parents to fresh parents. -/
noncomputable def freshen (B C : Finset Point) (x : Point) : Point := by
  classical
  exact if x ∈ C then x else
    (freshParent B C (parent x), sheet x, indexBound B C + index x)

@[simp] theorem freshen_fixed {B C : Finset Point} {x : Point} (hx : x ∈ C) :
    freshen B C x = x := by
  classical
  simp [freshen,hx]

@[simp] theorem freshen_sheet (B C : Finset Point) (x : Point) :
    sheet (freshen B C x) = sheet x := by
  classical
  unfold freshen
  split_ifs <;> rfl

@[simp] theorem freshen_parent (B C : Finset Point) (x : Point) :
    parent (freshen B C x) = freshParent B C (parent x) := by
  classical
  unfold freshen
  split_ifs with hx
  · simp only [freshParent, if_pos (show Anchored C (parent x) from ⟨x,hx,rfl⟩)]
  · rfl

theorem freshen_index_of_not_mem {B C : Finset Point} {x : Point} (hx : x ∉ C) :
    index (freshen B C x) = indexBound B C + index x := by
  classical
  simp [freshen,hx,index]

theorem freshen_injective (B C : Finset Point) : Function.Injective (freshen B C) := by
  classical
  intro x y h
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · simpa only [freshen_fixed hx,freshen_fixed hy] using h
  · have hi := congrArg index h
    rw [freshen_fixed hx, freshen_index_of_not_mem hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hx)
    omega
  · have hi := congrArg index h
    rw [freshen_index_of_not_mem hx, freshen_fixed hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hy)
    omega
  · have hp := congrArg parent h
    simp only [freshen_parent] at hp
    have he := freshParent_injective B C hp
    have hs := congrArg sheet h
    simp only [freshen_sheet] at hs
    have hi := congrArg index h
    rw [freshen_index_of_not_mem hx, freshen_index_of_not_mem hy] at hi
    exact Prod.ext he (Prod.ext hs (Nat.add_left_cancel hi))

theorem freshen_colour (B C : Finset Point) (x y : Point) :
    colour (freshen B C x) (freshen B C y) = colour x y := by
  classical
  unfold colour
  simp only [(freshen_injective B C).eq_iff, F, freshen_parent,
    (freshParent_injective B C).eq_iff, freshen_sheet]
  rfl

/-- An off-base point cannot land on ANY point of the fixed finite right side. -/
theorem freshen_mem_right {B C : Finset Point} {x : Point}
    (h : freshen B C x ∈ B) : x ∈ C := by
  classical
  by_contra hx
  have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_left C h)
  rw [freshen_index_of_not_mem hx] at hl
  omega

/-- A shared target parent must be anchored in the actual real base. -/
theorem freshen_parent_shared {B C : Finset Point} {x b : Point}
    (hb : b ∈ B) (h : F (freshen B C x) b) : Anchored C (parent b) := by
  classical
  by_cases ha : Anchored C (parent x)
  · have hp : parent x = parent b := by simpa [F,freshParent,ha] using h
    exact hp ▸ ha
  · have hh : parentBound B C + parent x = parent b := by
      simpa [F,freshParent,ha] using h
    have hl := parent_lt_bound (B := B) (C := C) (Finset.mem_union_left C hb)
    omega

/-- The literal parent-based real independence relation from the source. -/
def Independent (A C B : Finset Point) : Prop :=
  (∀ x ∈ A, x ∈ B → x ∈ C) ∧
  ∀ a ∈ A, a ∉ C → ∀ b ∈ B, b ∉ C → F a b → Anchored C (parent a)

theorem independent_freshen (A B C : Finset Point) :
    Independent (A.image (freshen B C)) C B := by
  classical
  constructor
  · intro x hx hb
    rcases Finset.mem_image.mp hx with ⟨a,ha,rfl⟩
    have hc := freshen_mem_right hb
    simpa only [freshen_fixed hc] using hc
  · intro a ha hac b hb hbc hab
    rcases Finset.mem_image.mp ha with ⟨x,hx,rfl⟩
    have hh := freshen_parent_shared hb hab
    exact hab ▸ hh

/-- Existence over the fixed REAL copy of B∪C, not just an abstract age copy. -/
theorem independent_existence (A B C : Finset Point) :
    ∃ g : Aut, (∀ c ∈ C, g • c = c) ∧ Independent (transport g A) C B := by
  classical
  obtain ⟨g,hg⟩ := finite_extension (fun x : ↥(A ∪ C) => x.val)
    (fun x => freshen B C x.val) (fun x y => (freshen_colour B C x y).symm)
  refine ⟨g,fun c hc => ?_,?_⟩
  · exact (hg ⟨c,Finset.mem_union_right A hc⟩).trans (freshen_fixed hc)
  · have ht : transport g A = A.image (freshen B C) := by
      ext x
      rw [mem_transport,Finset.mem_image]
      constructor <;> rintro ⟨a,ha,he⟩ <;> refine ⟨a,ha,?_⟩
      · exact (hg ⟨a,Finset.mem_union_left C ha⟩).symm.trans he
      · exact (hg ⟨a,Finset.mem_union_left C ha⟩).trans he
    rw [ht]
    exact independent_freshen A B C

end CCO.SIR.Positive.Direct
