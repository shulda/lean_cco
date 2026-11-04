import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic

/-!
# B060 N03: the infinite finite-palette monochromatic pair lemma

An infinite set with finitely many unordered pair colours has an
infinite monochromatic subset. We prove the infinite-selection step
directly from the strong infinite pigeonhole principle and iterate
nested infinite tails. The resulting pivots are genuinely distinct;
the final infinite monochromatic colour is selected by a SECOND
infinite pigeonhole application.

This elementary combinatorial input is independent of clones,
homogeneity, group actions, AP, SAP, CCO and any Ramsey expansion.
-/

universe u v
namespace CCO.CloneTupleGeometry
noncomputable section

/-- Select an infinite monochromatic tail from an arbitrary infinite
subset after deleting one actual pivot. The deletion ensures that all
subsequent selected pivots are distinct. -/
theorem infinite_colour_tail
    {α : Type u} {β : Type v} [Finite β]
    (colour : α → α → β) {s : Set α} (hs : s.Infinite) :
    ∃ x : α, x ∈ s ∧ ∃ b : β, ∃ t : Set α,
      t.Infinite ∧ t ⊆ s \ {x} ∧
        ∀ y ∈ t, colour x y = b := by
  classical
  obtain ⟨x,hx,_⟩ := hs.exists_notMem_finset (∅ : Finset α)
  let T : Set α := s \ {x}
  have hT : T.Infinite := hs.sdiff (Set.finite_singleton x)
  letI : Infinite T := hT.to_subtype
  let f : T → β := fun y => colour x y.val
  obtain ⟨b,hb⟩ := Finite.exists_infinite_fiber f
  let U : Set T := f ⁻¹' {b}
  letI : Infinite U := hb
  let t : Set α := {y | y ∈ T ∧ colour x y = b}
  have ht : t.Infinite := by
    let p : U → α := fun z => z.val.val
    have hp : Function.Injective p := by
      intro y z h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    apply Set.infinite_of_injective_forall_mem hp
    intro z
    refine ⟨z.val.property, ?_⟩
    simpa only [U, f, Set.mem_preimage, Set.mem_singleton_iff] using z.property
  refine ⟨x,hx,b,t,ht,?_,?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private structure InfiniteCarrier (α : Type u) where
  carrier : Set α
  infinite : carrier.Infinite

private structure InfiniteColourStep {α : Type u} {β : Type v}
    (colour : α → α → β) (s : Set α) where
  pivot : α
  colour_value : β
  rest : InfiniteCarrier α
  pivot_mem : pivot ∈ s
  rest_subset : rest.carrier ⊆ s \ {pivot}
  colour_eq : ∀ y ∈ rest.carrier, colour pivot y = colour_value

private noncomputable def chooseInfiniteStep
    {α : Type u} {β : Type v} [Finite β]
    (colour : α → α → β) (D : InfiniteCarrier α) :
    InfiniteColourStep colour D.carrier :=
  Classical.choice (show Nonempty (InfiniteColourStep colour D.carrier) from by
    obtain ⟨x,hx,b,t,ht,hsub,hc⟩ :=
      infinite_colour_tail colour D.infinite
    exact ⟨⟨x,b,⟨t,ht⟩,hx,hsub,hc⟩⟩)

/-- Infinite Ramsey for pairs in a finite symmetric palette, proved
from infinite pigeonhole without assuming any pre-existing Ramsey theorem.
No reflexive diagonal colour is required: all pairs are distinct. -/
theorem infinite_monochromatic_pairs
    {α : Type u} {β : Type v}
    [Infinite α] [Finite β]
    (colour : α → α → β)
    (hsym : ∀ x y, colour x y = colour y x) :
    ∃ b : β, ∃ f : ℕ ↪ α,
      ∀ i j : ℕ, i ≠ j → colour (f i) (f j) = b := by
  classical
  let first : InfiniteCarrier α := ⟨Set.univ, Set.infinite_univ⟩
  let states : ℕ → InfiniteCarrier α :=
    Nat.rec first (fun _ T => (chooseInfiniteStep colour T).rest)
  let pivot : ℕ → α := fun n => (chooseInfiniteStep colour (states n)).pivot
  let selected : ℕ → β :=
    fun n => (chooseInfiniteStep colour (states n)).colour_value
  have hNext (n : ℕ) :
      (states (n + 1)).carrier ⊆ (states n).carrier \ {pivot n} := by
    change (chooseInfiniteStep colour (states n)).rest.carrier ⊆
      (states n).carrier \ {(chooseInfiniteStep colour (states n)).pivot}
    exact (chooseInfiniteStep colour (states n)).rest_subset
  have hNested (i j : ℕ) (hij : i ≤ j) :
      (states j).carrier ⊆ (states i).carrier := by
    induction hij with
    | refl => exact Set.Subset.rfl
    | @step j _ ih =>
        exact ((hNext j).trans Set.diff_subset).trans ih
  have hLater (i j : ℕ) (hij : i < j) :
      pivot j ∈ (chooseInfiniteStep colour (states i)).rest.carrier := by
    have hj : pivot j ∈ (states j).carrier :=
      (chooseInfiniteStep colour (states j)).pivot_mem
    have hm : pivot j ∈ (states (i + 1)).carrier :=
      hNested (i + 1) j (Nat.succ_le_iff.mpr hij) hj
    exact hm
  have hForward (i j : ℕ) (hij : i < j) :
      colour (pivot i) (pivot j) = selected i :=
    (chooseInfiniteStep colour (states i)).colour_eq (pivot j) (hLater i j hij)
  have hPivots : Function.Injective pivot := by
    intro i j he
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hnot : pivot j ≠ pivot i :=
        (Set.mem_sdiff.mp ((hNext i) (hLater i j hij'))).2
      exact hnot he.symm
    · have hnot : pivot i ≠ pivot j :=
        (Set.mem_diff.mp ((hNext j) (hLater j i hji'))).2
      exact hnot he
  obtain ⟨b,hFibre⟩ := Finite.exists_infinite_fiber selected
  let fibre : Set ℕ := selected ⁻¹' {b}
  have hfibre : fibre.Infinite := Set.infinite_coe_iff.mp hFibre
  let e : ℕ ↪ fibre := hfibre.natEmbedding fibre
  let indices : ℕ ↪ ℕ :=
    ⟨fun n => (e n).val, by
      intro i j he
      exact e.injective (Subtype.ext he)⟩
  have hIndex (n : ℕ) : selected (indices n) = b := by
    have h := (e n).property
    simpa only [fibre, indices, Set.mem_preimage,
      Set.mem_singleton_iff] using h
  let f : ℕ ↪ α :=
    ⟨fun n => pivot (indices n), fun i j he => indices.injective (hPivots he)⟩
  refine ⟨b,f,?_⟩
  intro i j hij
  change colour (pivot (indices i)) (pivot (indices j)) = b
  have hne : indices i ≠ indices j := indices.injective.ne hij
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hForward (indices i) (indices j) hlt).trans (hIndex i)
  · calc
      colour (pivot (indices i)) (pivot (indices j)) =
          colour (pivot (indices j)) (pivot (indices i)) := hsym _ _
      _ = selected (indices j) := hForward (indices j) (indices i) hgt
      _ = b := hIndex j

/-- Finite old monochromatic cliques of every size use ONE fixed
colour, not a new colour chosen for each cardinality. -/
theorem arbitrarily_large_monochromatic_cliques
    {α : Type u} {β : Type v} [Infinite α] [Finite β]
    (colour : α → α → β)
    (hsym : ∀ x y, colour x y = colour y x) :
    ∃ b : β, ∀ n : ℕ, ∃ f : Fin n ↪ α,
      ∀ i j : Fin n, i ≠ j → colour (f i) (f j) = b := by
  obtain ⟨b,f,hf⟩ := infinite_monochromatic_pairs colour hsym
  refine ⟨b,?_⟩
  intro n
  let e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  refine ⟨e.trans f,?_⟩
  intro i j hij
  exact hf (i.val) (j.val) (by
    intro h
    exact hij (Fin.ext h))

end
end CCO.CloneTupleGeometry
