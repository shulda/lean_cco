import CCO.OldIdempotentForest.PruningBounds
import CCO.OldIdempotentForest.StoppedPruningAlgebra

/-! Exact controls for maximal stopped gaps, short paths and the sharp
twice-leaf OLD endpoint count. These are finite combinatorial theorems,
not a replacement for the general forest existence theorem. -/

namespace CCO.OldIdempotentForest

def nestedWideTree : FactorizationTree Nat := .idempotent
  [.leaf 0,.idempotent [.leaf 1,.leaf 2,.leaf 3],.leaf 4]

def nestedWidePruning : PruningTree Nat := .branch (.leaf 0) [1,2,3] (.leaf 4)

/-- The discarded wide child contributes ONE whole gap, with no nested
deletion record for its own middle leaf. -/
theorem nested_middle_stops : Prunes nestedWideTree nestedWidePruning :=
  .idempotent [.idempotent [.leaf 1,.leaf 2,.leaf 3]] (.leaf 0) (.leaf 4)

theorem nested_middle_exact_gap : nestedWidePruning.gapWords = [[1,2,3]] := by decide

theorem nested_middle_original_indices : nestedWidePruning.word = [0,1,2,3,4] := rfl

/-- Two separated retained original letters really can need FOUR old
root positions. The leafcount+1 estimate would be false. -/
theorem twice_leaf_root_count_needed :
    (nestedWidePruning.retainedRoots 0).card = 4 ∧ nestedWidePruning.leaves + 1 = 3 := by
  decide

/-- Upstream Ramsey idempotent constructors allow two children: this is
a binary retention node, with no empty deletion interval. -/
theorem two_idempotent_children_no_gap :
    Prunes (.idempotent [.leaf (0 : Nat),.leaf 1])
      (.branch (.leaf 0) [] (.leaf 1)) ∧
      (PruningTree.branch (.leaf 0) [] (.leaf 1)).gapWords = [] :=
  ⟨.idempotent [] (.leaf 0) (.leaf 1),by decide⟩

/-- Exactly three children yield the one positive middle child. -/
theorem three_children_one_middle :
    Prunes (.idempotent [.leaf (0 : Nat),.leaf 1,.leaf 2])
      (.branch (.leaf 0) [1] (.leaf 2)) ∧
      (PruningTree.branch (.leaf 0) [1] (.leaf 2)).gapWords = [[1]] :=
  ⟨.idempotent [.leaf 1] (.leaf 0) (.leaf 2),by decide⟩

theorem one_letter_height_zero :
    Prunes (.leaf (0 : Nat)) (.leaf 0) ∧
      (PruningTree.leaf (0 : Nat)).height = 0 ∧
      (PruningTree.leaf (0 : Nat)).gapWords = [] ∧
      (PruningTree.leaf (0 : Nat)).retainedRoots 0 = {0,1} :=
  ⟨.leaf 0,rfl,rfl,rfl⟩

end CCO.OldIdempotentForest
