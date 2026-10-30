import CCO.UnaryFreshFrames.Quotient.Named
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Lattice.Fold

/-! C36 derives a uniform singleton bound from the FINITELY many actual
transitive real sorts. It is not a generator-independent bound on closures. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

theorem aut_closureAt (g : H.Aut) (x : V) :
    H.closureAt (g • x) = (fun y => g • y) '' H.closureAt x := by
  simpa only [closureAt, Set.image_singleton] using H.aut_closure g {x}

theorem closureAt_ncard_eq (G : Subgroup H.Aut) {i : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i)) (x y : H.Carrier i) :
    (H.closureAt x.val).ncard = (H.closureAt y.val).ncard := by
  obtain ⟨g, hg⟩ := ht x y
  have he : g.val • x.val = y.val := congrArg Subtype.val hg
  rw [← he, H.aut_closureAt g.val x.val]
  exact (Set.ncard_image_of_injective _ (MulAction.injective g.val)).symm

theorem uniform_real_singleton_bound (hfin : H.LocallyFinite) (G : Subgroup H.Aut) (real : L.Sorts → Prop)
    [Finite {i : L.Sorts // real i}]
    (ht : ∀ i, real i → Quotient.Transitive (G := G) (M := H.Carrier i)) :
    ∃ N : ℕ, ∀ x : V, real (H.sort x) →
      (H.closureAt x).Finite ∧ (H.closureAt x).ncard ≤ N := by
  classical
  let : Fintype {i : L.Sorts // real i} := Fintype.ofFinite _
  let size : {i : L.Sorts // real i} → ℕ := fun i =>
    if h : Nonempty (H.Carrier i.val) then (H.closureAt (Classical.choice h).val).ncard else 0
  refine ⟨Finset.univ.sup size, ?_⟩
  intro x hx
  refine ⟨hfin {x} (Set.finite_singleton x), ?_⟩
  let i : {i : L.Sorts // real i} := ⟨H.sort x, hx⟩
  have he : size i = (H.closureAt x).ncard := by
    dsimp only [size]
    rw [dite_eq_left (show Nonempty (H.Carrier i.val) from ⟨⟨x, rfl⟩⟩)]
    exact H.closureAt_ncard_eq G (ht i.val i.property) _ ⟨x, rfl⟩
  rw [← he]
  exact Finset.le_sup (Finset.mem_univ i)

/-- Exact unary singleton additivity yields the stated linear bound. -/
theorem closure_ncard_le_mul (N : ℕ) (real : L.Sorts → Prop)
    (hb : ∀ x, real (H.sort x) → (H.closureAt x).ncard ≤ N)
    (D : Finset V) (hD : ∀ x ∈ D, real (H.sort x)) :
    (H.closure (D : Set V)).ncard ≤ D.card * N := by
  classical
  induction D using Finset.induction_on with
  | empty => simp only [Finset.coe_empty, H.closure_empty, Set.ncard_empty, Finset.card_empty,
      Nat.zero_mul, le_refl]
  | @insert x D hx ih =>
    rw [Finset.coe_insert, ← Set.singleton_union, H.closure_union, Finset.card_insert_of_notMem hx]
    have hd := ih (fun y hy => hD y (Finset.mem_insert_of_mem hy))
    have hh := hb x (hD x (Finset.mem_insert_self _ _))
    apply (Set.ncard_union_le _ _).trans
    calc
      (H.closure {x}).ncard + (H.closure (D : Set V)).ncard ≤ N + D.card * N :=
        Nat.add_le_add hh hd
      _ = (D.card + 1) * N := by simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end CCO.UnaryFreshFrames.Structure
