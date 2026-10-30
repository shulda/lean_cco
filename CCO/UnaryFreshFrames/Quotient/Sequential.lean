import CCO.UnaryFreshFrames.Quotient.System
import CCO.UnaryFreshFrames.Quotient.NamedNecessity
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite sequential requests, across different real/quotient sorts.
Each new representative avoids the full closures of earlier representatives;
only forced values are permitted to recur. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure.NamedQuotientSystem
variable {L : Language.{u}} {V : Type v} {H : Structure L V} {real : Set L.Sorts}

abbrev Request (S : H.NamedQuotientSystem real) :=
  Σ q : S.Index, H.Carrier (S.projection q).target

def IsChoice (S : H.NamedQuotientSystem real) (r : S.Request) (x : V) : Prop :=
  ∃ hx : H.sort x = (S.projection r.1).source,
    H.typedEval (S.projection r.1).term ⟨x, hx⟩ = r.2

theorem exists_choice (S : H.NamedQuotientSystem real) (G : Subgroup H.Aut)
    (ht : S.SourceTransitive G) (hfinite : ∀ x : V, (H.closureAt x).Finite)
    (hkernel : S.KernelClauses) (r : S.Request) (Z : Set V) (hZ : Z.Finite) :
    ∃ x : V, S.IsChoice r x ∧ H.sort x ∈ real ∧
      H.closureAt x ∩ Z = H.closureAt r.2.val ∩ Z ∧ x ∉ Z := by
  let p := S.projection r.1
  obtain ⟨x, hx, hcl, hfresh, _⟩ := H.named_fibre_avoidance G (ht r.1) p.term
    p.surjective p.strict hfinite (hkernel r.1).1 (hkernel r.1).2 r.2 Z hZ
  exact ⟨x.val, ⟨x.property, hx⟩, x.property.symm ▸ S.source_real r.1, hcl, hfresh⟩

/-- C27: actual named quotient requests can be satisfied sequentially with
pairwise distinct real representatives. A new singleton closure can meet an
earlier closure ONLY in its own forced base closure. -/
theorem finite_sequential_choices (S : H.NamedQuotientSystem real) (G : Subgroup H.Aut)
    (ht : S.SourceTransitive G) (hfinite : ∀ x : V, (H.closureAt x).Finite)
    (hkernel : S.KernelClauses) (n : ℕ) (r : Fin n → S.Request)
    (Z : Set V) (hZ : Z.Finite) :
    ∃ f : Fin n → V, Function.Injective f ∧
      (∀ i, S.IsChoice (r i) (f i) ∧ H.sort (f i) ∈ real ∧
        H.closureAt (f i) ∩ Z = H.closureAt (r i).2.val ∩ Z ∧ f i ∉ Z) ∧
      ∀ i j, i < j → H.closureAt (f j) ∩ H.closureAt (f i) ⊆ H.closureAt (r j).2.val := by
  classical
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f, hf, hP, hsep⟩ := ih (fun i => r i.castSucc)
    let old := ⋃ i : Fin n, H.closureAt (f i)
    have hold : old.Finite := Set.finite_iUnion fun i => hfinite (f i)
    obtain ⟨x, hxchoice, hxreal, hxcl, hxfresh⟩ := S.exists_choice G ht hfinite hkernel
      (r (Fin.last n)) (Z ∪ old) (hZ.union hold)
    have hxnot : x ∉ Set.range f := by
      rintro ⟨i, rfl⟩
      exact hxfresh (Or.inr (Set.mem_iUnion.mpr ⟨i, H.subset_closure {f i} rfl⟩))
    refine ⟨Fin.snoc f x, Fin.snoc_injective_of_injective hf hxnot, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | cast i => simpa only [Fin.snoc_castSucc] using hP i
      | last =>
        simp only [Fin.snoc_last]
        refine ⟨hxchoice, hxreal, ?_, fun hz => hxfresh (Or.inl hz)⟩
        apply Set.Subset.antisymm
        · intro y hy
          have hz : y ∈ H.closureAt x ∩ (Z ∪ old) := ⟨hy.1, Or.inl hy.2⟩
          rw [hxcl] at hz
          exact ⟨hz.1, hy.2⟩
        · intro y hy
          have hz : y ∈ H.closureAt (r (Fin.last n)).2.val ∩ (Z ∪ old) :=
            ⟨hy.1, Or.inl hy.2⟩
          rw [← hxcl] at hz
          exact ⟨hz.1, hy.2⟩
    · intro i j hij
      induction j using Fin.lastCases with
      | cast j =>
        induction i using Fin.lastCases with
        | cast i => simpa only [Fin.snoc_castSucc] using hsep i j hij
        | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hij)
      | last =>
        induction i using Fin.lastCases with
        | last => exact False.elim ((lt_irrefl _) hij)
        | cast i =>
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          intro y hy
          have hz : y ∈ H.closureAt x ∩ (Z ∪ old) :=
            ⟨hy.1, Or.inr (Set.mem_iUnion.mpr ⟨i, hy.2⟩)⟩
          rw [hxcl] at hz
          exact hz.1

/-- Actual unforced terms of a selected representative are outside the
closure of its quotient point, by a genuine subgroup stabilizer motion. -/
theorem choice_unforced_not_in_base (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : S.SourceTransitive G) (r : S.Request) (x : V)
    (hx : S.IsChoice r x) (k : L.Sorts) (t : Term L (S.projection r.1).source k)
    (hn : ¬ Quotient.KernelLe (H.typedEval (S.projection r.1).term) (H.termFunction t)) :
    H.eval t x ∉ H.closureAt r.2.val := by
  rcases hx with ⟨hxs, hxp⟩
  have h := H.nonforced_value_not_mem_closure G (ht r.1)
    (S.projection r.1).term t hn ⟨x, hxs⟩
  rw [hxp] at h
  exact h

/-- The concrete finite sequence also avoids every earlier UNFORCED value
(and even every earlier singleton-closure value) with all new unforced terms.
Forced values are deliberately allowed to recur. -/
theorem finite_sequential_avoidance (S : H.NamedQuotientSystem real) (G : Subgroup H.Aut)
    (ht : S.SourceTransitive G) (hfinite : ∀ x : V, (H.closureAt x).Finite)
    (hkernel : S.KernelClauses) (n : ℕ) (r : Fin n → S.Request)
    (Z : Set V) (hZ : Z.Finite) :
    ∃ f : Fin n → V, Function.Injective f ∧ (∀ i, S.IsChoice (r i) (f i)) ∧
      (∀ i, H.sort (f i) ∈ real ∧ f i ∉ Z) ∧
      ∀ j k (t : Term L (S.projection (r j).1).source k),
        ¬ Quotient.KernelLe (H.typedEval (S.projection (r j).1).term) (H.termFunction t) →
        H.eval t (f j) ∉ Z ∧ ∀ i, i < j → H.eval t (f j) ∉ H.closureAt (f i) := by
  obtain ⟨f, hf, hP, hsep⟩ := S.finite_sequential_choices G ht hfinite hkernel n r Z hZ
  refine ⟨f, hf, fun i => (hP i).1, fun i => ⟨(hP i).2.1, (hP i).2.2.2⟩, ?_⟩
  intro j k t hn
  have hoff := S.choice_unforced_not_in_base G ht (r j) (f j) (hP j).1 k t hn
  have hmem : H.eval t (f j) ∈ H.closureAt (f j) :=
    H.eval_mem_closed (H.closure_closed {f j}) t (H.subset_closure {f j} rfl)
  refine ⟨?_, ?_⟩
  · intro hz
    have hm : H.eval t (f j) ∈ H.closureAt (f j) ∩ Z := ⟨hmem, hz⟩
    rw [(hP j).2.2.1] at hm
    exact hoff hm.1
  · intro i hij hi
    exact hoff (hsep i j hij ⟨hmem, hi⟩)

end CCO.UnaryFreshFrames.Structure.NamedQuotientSystem
