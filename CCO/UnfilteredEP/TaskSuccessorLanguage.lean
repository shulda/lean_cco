import CCO.UnfilteredEP.TaskPrefixLanguage
import Lean.Elab.Tactic.Omega

/-! Exact same-map successor-prefix embedding codec. A successor adds
precisely one actual task relation and no function or domain. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

def nextPrefixTask (i : Fin (taskCount B ht)) : PrefixTask B ht (i.val+1) :=
  ⟨i,Nat.lt_succ_self i.val⟩

theorem prefixTask_before_or_next (i : Fin (taskCount B ht))
    (k : PrefixTask B ht (i.val+1)) :
    (∃ j : PrefixTask B ht i.val,
      prefixTaskInclusion B ht (Nat.le_succ i.val) j = k) ∨ k = nextPrefixTask B ht i := by
  by_cases hk : k.val.val < i.val
  · exact Or.inl ⟨⟨k.val,hk⟩,Subtype.ext rfl⟩
  · right
    apply Subtype.ext
    apply Fin.ext
    change k.val.val = i.val
    have h := k.property
    omega

/-- An induced old-prefix map plus the ONE added comparison supplies
exactly an induced successor map, on the same partial-unary carrier. -/
def successorPrefixEmbeddingOfTask (i : Fin (taskCount B ht)) {V : Type z} {W : Type a}
    {C : Structure (PrefixFullCodeLanguage B ht (i.val+1)) V}
    {D : Structure (PrefixFullCodeLanguage B ht (i.val+1)) W}
    (old : Structure.Embedding
      (C.reduct (prefixInclusion B ht (Nat.le_succ i.val)))
      (D.reduct (prefixInclusion B ht (Nat.le_succ i.val))))
    (current : ∀ x y, D.binary (.inr (nextPrefixTask B ht i)) (old.point x) (old.point y) ↔
      C.binary (.inr (nextPrefixTask B ht i)) x y) : Structure.Embedding C D where
  point := old.point
  injective := old.injective
  sort_eq := old.sort_eq
  map_func := old.map_func
  reflect_func := old.reflect_func
  unary_iff := old.unary_iff
  binary_iff R x y := by
    cases R with
    | inl R => exact old.binary_iff (.inl R) x y
    | inr k =>
      rcases prefixTask_before_or_next B ht i k with ⟨j,rfl⟩ | rfl
      · exact old.binary_iff (.inr j) x y
      · exact current x y

end
end CCO.UnfilteredEP
