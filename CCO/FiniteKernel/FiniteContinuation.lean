import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# Explicit finite-continuation construction

The finite failure-bound argument and subsequent recursion are proved here.
No compactness or external König theorem is imported. Finite nonempty levels
need not have surjective restriction maps.
-/

universe u
namespace CCO.FiniteKernel

theorem finite_nested_choice {A : Type u} [Finite A]
    (P : ℕ → A → Prop)
    (hmono : ∀ {m n}, m ≤ n → ∀ a, P n a → P m a)
    (hne : ∀ n, ∃ a, P n a) : ∃ a, ∀ n, P n a := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  by_contra h
  have hbad : ∀ a, ∃ n, ¬ P n a := by
    intro a
    by_contra hn
    exact h ⟨a,fun n => Classical.byContradiction (fun hh => hn ⟨n,hh⟩)⟩
  choose bad hbad using hbad
  let N := Finset.univ.sup bad
  obtain ⟨a,ha⟩ := hne N
  exact hbad a (hmono (Finset.le_sup (Finset.mem_univ a)) a ha)

structure FiniteTower where
  Level : ℕ → Type u
  finite_level : ∀ n, Finite (Level n)
  nonempty_level : ∀ n, Nonempty (Level n)
  restrict : ∀ n m, n ≤ m → Level m → Level n
  restrict_self : ∀ n x, restrict n n le_rfl x = x
  restrict_trans : ∀ n m k (hnm : n ≤ m) (hmk : m ≤ k) x,
    restrict n m hnm (restrict m k hmk x) = restrict n k (hnm.trans hmk) x

namespace FiniteTower
variable (T : FiniteTower.{u})

instance (n : ℕ) : Finite (T.Level n) := T.finite_level n
instance (n : ℕ) : Nonempty (T.Level n) := T.nonempty_level n

def Good (n : ℕ) (x : T.Level n) : Prop :=
  ∀ m (hnm : n ≤ m), ∃ y : T.Level m, T.restrict n m hnm y = x

theorem good_root : ∃ x : T.Level 0, T.Good 0 x := by
  have hm : ∀ {m n}, m ≤ n → ∀ x : T.Level 0,
      (∃ y : T.Level n, T.restrict 0 n (Nat.zero_le n) y = x) →
      ∃ y : T.Level m, T.restrict 0 m (Nat.zero_le m) y = x := by
    intro m n hmn x
    rintro ⟨y,hy⟩
    refine ⟨T.restrict m n hmn y,?_⟩
    exact (T.restrict_trans 0 m n (Nat.zero_le m) hmn y).trans hy
  have hn : ∀ n, ∃ x : T.Level 0, ∃ y : T.Level n,
      T.restrict 0 n (Nat.zero_le n) y = x := by
    intro n
    obtain ⟨y⟩ := T.nonempty_level n
    exact ⟨T.restrict 0 n (Nat.zero_le n) y,y,rfl⟩
  obtain ⟨x,hx⟩ := finite_nested_choice _ hm hn
  exact ⟨x,fun m _ => hx m⟩

/-- An infinitely continuing node has an infinitely continuing child: if every
child failed, finitely many chosen failure levels would have a common bound. -/
theorem good_child (n : ℕ) (x : T.Level n) (hx : T.Good n x) :
    ∃ y : T.Level (n+1), T.restrict n (n+1) (Nat.le_succ n) y = x ∧ T.Good (n+1) y := by
  let P : ℕ → T.Level (n+1) → Prop := fun k y =>
    T.restrict n (n+1) (Nat.le_succ n) y = x ∧
      ∃ z : T.Level (n+1+k), T.restrict (n+1) (n+1+k) (by omega) z = y
  have hmono : ∀ {a b}, a ≤ b → ∀ y, P b y → P a y := by
    intro a b hab y hy
    obtain ⟨z,hz⟩ := hy.2
    refine ⟨hy.1,T.restrict (n+1+a) (n+1+b) (by omega) z,?_⟩
    exact (T.restrict_trans (n+1) (n+1+a) (n+1+b) (by omega) (by omega) z).trans hz
  have hne : ∀ k, ∃ y, P k y := by
    intro k
    obtain ⟨z,hz⟩ := hx (n+1+k) (by omega)
    refine ⟨T.restrict (n+1) (n+1+k) (by omega) z,?_,z,rfl⟩
    exact (T.restrict_trans n (n+1) (n+1+k) (by omega) (by omega) z).trans hz
  obtain ⟨y,hy⟩ := finite_nested_choice P hmono hne
  refine ⟨y,(hy 0).1,?_⟩
  intro m hnm
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact (hy k).2

theorem coherent_path : ∃ f : ∀ n, T.Level n,
    ∀ n, T.restrict n (n+1) (Nat.le_succ n) (f (n+1)) = f n := by
  classical
  let root : {x : T.Level 0 // T.Good 0 x} :=
    ⟨Classical.choose T.good_root,Classical.choose_spec T.good_root⟩
  let next (n : ℕ) (x : {x : T.Level n // T.Good n x}) :
      {x : T.Level (n+1) // T.Good (n+1) x} :=
    ⟨Classical.choose (T.good_child n x.val x.property),
      (Classical.choose_spec (T.good_child n x.val x.property)).2⟩
  let f : ∀ n, {x : T.Level n // T.Good n x} := fun n => Nat.rec root next n
  refine ⟨fun n => (f n).val,?_⟩
  intro n
  exact (Classical.choose_spec (T.good_child n (f n).val (f n).property)).1

theorem coherent_path_restrict (f : ∀ n, T.Level n)
    (hf : ∀ n, T.restrict n (n+1) (Nat.le_succ n) (f (n+1)) = f n) :
    ∀ n m (hnm : n ≤ m), T.restrict n m hnm (f m) = f n := by
  intro n m hnm
  induction m,hnm using Nat.le_induction with
  | base => exact T.restrict_self n (f n)
  | @succ m hnm ih =>
      rw [← T.restrict_trans n m (m+1) hnm (Nat.le_succ m),hf m,ih]

end FiniteTower
end CCO.FiniteKernel
