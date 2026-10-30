import CCO.ResetOrder.Hierarchy.Synchronize

/-! Reverse ONE complete task orbit, keeping all strict coarser tasks fixed. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
namespace System
variable {I : Type u} {H : Schedule I} {X : I → Type v} (S : System H X)

theorem agree_below (t s : S.Tasks) (bound : ℕ) (ht : ∀ i, H.rank i < bound → t i = s i) :
    ∀ i, H.rank i < bound → S.normalizeTasks t i = S.normalizeTasks s i := by
  intro i
  induction i using (measure H.rank).wf.induction with
  | h i ih =>
    intro hi
    apply TotalOrder.ext
    intro x y
    rw [S.normalize_lt_iff, S.normalize_lt_iff]
    apply or_congr
    · unfold KeyLex
      apply exists_congr
      intro a
      exact and_congr Iff.rfl (Iff.of_eq (congrArg
        (fun q : TotalOrder (X (H.coordinate i a)) => q.lt (S.up i a x) (S.up i a y))
        (ih (H.coordinate i a) (H.coordinate_rank i a) ((H.coordinate_rank i a).trans hi))))
    · exact and_congr Iff.rfl (Iff.of_eq (congrArg (fun q : FibreOrder (S.parent i) => q.lt x y) (ht i hi)))

noncomputable def reverseTasks (t : S.Tasks) (selected : I → Prop) : S.Tasks := by
  classical
  exact fun i => if selected i then (t i).reverse (S.parent_symm i) else t i

theorem reverseTasks_selected (t : S.Tasks) (selected : I → Prop) (i : I) (hi : selected i)
    (x y : X i) : (S.reverseTasks t selected i).lt x y ↔ (t i).lt y x := by
  classical
  simp only [reverseTasks, if_pos hi]
  rfl

theorem reverse_coarser_unchanged (t : S.Tasks) (selected : I → Prop) (rank : ℕ)
    (hr : ∀ i, selected i → H.rank i = rank) (i : I) (hi : H.rank i < rank) :
    S.normalizeTasks (S.reverseTasks t selected) i = S.normalizeTasks t i := by
  apply S.agree_below _ _ rank _ i hi
  intro j hj
  have hn : ¬ selected j := fun h => (Nat.ne_of_lt hj) (hr j h)
  simp only [reverseTasks, if_neg hn]
end System

namespace Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {S : System H X} {representative : ∀ r, J r}
variable (C : Charting.{u,v,w} S representative)

noncomputable def reverseOrbit (o : S.Orders) (r : R) : S.Orders :=
  S.normalizeTasks (S.reverseTasks (C.localTasks o) (fun i => i.1 = r))

theorem reverseOrbit_coarser (o : S.Orders) (r : R) (i : Sigma J)
    (hi : H.rank i < H.rank ⟨r,C.representative r⟩) : C.reverseOrbit o r i = C.normalize o i := by
  apply S.reverse_coarser_unchanged _ _ _ _ i hi
  intro j hj
  obtain ⟨r',j⟩ := j
  change r' = r at hj
  subst r'
  exact C.rank_orbit r j

theorem reverseOrbit_local (o : S.Orders) (r : R) (j : J r) (x y : X ⟨r,j⟩)
    (hp : S.parent ⟨r,j⟩ x y) :
    (C.reverseOrbit o r ⟨r,j⟩).lt x y ↔ (C.localTasks o ⟨r,j⟩).lt y x := by
  exact (S.normalized_fibre _ _ hp).trans
    (S.reverseTasks_selected (C.localTasks o) (fun i : Sigma J => i.1 = r) ⟨r,j⟩ rfl x y)
end Charting
end CCO.ResetOrder.Hierarchy
