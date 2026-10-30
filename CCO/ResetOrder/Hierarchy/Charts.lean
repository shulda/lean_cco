import CCO.ResetOrder.Hierarchy.Quotients
import CCO.ResetOrder.Hierarchy.Orders
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! Named paths have genuine inverse charts inside the SAME closed object. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
structure TransitionPaths (I : Type u) (X : I → Type v) where
  Path : I → I → Type w
  identity : ∀ i, Path i i
  compose : ∀ {i j k}, Path i j → Path j k → Path i k
  inverse : ∀ {i j}, Path i j → Path j i
  map : ∀ {i j}, Path i j → (X i ≃ X j)
  map_identity : ∀ i x, map (identity i) x = x
  map_compose : ∀ {i j k} (p : Path i j) (q : Path j k) x,
    map (compose p q) x = map q (map p x)
  map_inverse : ∀ {i j} (p : Path i j) x, map (inverse p) (map p x) = x
  holonomy : ∀ {i} (p : Path i i) x, map p x = x

namespace TransitionPaths
variable {I : Type u} {X : I → Type v} (T : TransitionPaths.{u,v,w} I X)
theorem path_independent {i j : I} (p q : T.Path i j) (x : X i) : T.map p x = T.map q x := by
  apply (T.map (T.inverse q)).injective
  rw [← T.map_compose, T.holonomy, T.map_inverse]

def SameOrbit (i j : I) : Prop := Nonempty (T.Path i j)
theorem sameOrbit_refl (i : I) : T.SameOrbit i i := ⟨T.identity i⟩
theorem sameOrbit_symm {i j : I} : T.SameOrbit i j → T.SameOrbit j i :=
  fun ⟨p⟩ => ⟨T.inverse p⟩
theorem sameOrbit_trans {i j k : I} : T.SameOrbit i j → T.SameOrbit j k → T.SameOrbit i k :=
  fun ⟨p⟩ ⟨q⟩ => ⟨T.compose p q⟩

theorem inverse_chart {i j : I} (p : T.Path i j) (y : X j) : ∃ x : X i, T.map p x = y :=
  (T.map p).surjective y

def transportOrder {i j : I} (p : T.Path i j) (o : TotalOrder (X i)) : TotalOrder (X j) :=
  o.pullback (T.map p).symm (T.map p).symm.injective

theorem transportOrder_independent {i j : I} (p q : T.Path i j) (o : TotalOrder (X i)) :
    T.transportOrder p o = T.transportOrder q o := by
  apply TotalOrder.ext
  intro x y
  have hx : (T.map p).symm x = (T.map q).symm x := by
    apply (T.map p).injective
    rw [Equiv.apply_symm_apply, T.path_independent p q, Equiv.apply_symm_apply]
  have hy : (T.map p).symm y = (T.map q).symm y := by
    apply (T.map p).injective
    rw [Equiv.apply_symm_apply, T.path_independent p q, Equiv.apply_symm_apply]
  change o.lt ((T.map p).symm x) ((T.map p).symm y) ↔ _
  rw [hx, hy]
  rfl
end TransitionPaths

noncomputable def upperRank {L : Type u} [PartialOrder L] [Fintype L] (j : L) : ℕ :=
  Nat.card {l : L // j < l}

theorem upperRank_strict {L : Type u} [PartialOrder L] [Fintype L] {j l : L}
    (h : j < l) : upperRank l < upperRank j := by
  classical
  unfold upperRank
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let f : {m : L // l < m} → {m : L // j < m} := fun m => ⟨m.val, h.trans m.property⟩
  apply Fintype.card_lt_of_injective_not_surjective f
  · intro x y he
    apply Subtype.ext
    exact congrArg (fun z : {m : L // j < m} => z.val) he
  · intro hs
    obtain ⟨m, hm⟩ := hs ⟨l, h⟩
    have he : m.val = l := congrArg (fun z : {m : L // j < m} => z.val) hm
    have hml := m.property
    rw [he] at hml
    exact (lt_irrefl l) hml

theorem upperRank_transport {L : Type u} {M : Type v} [PartialOrder L] [PartialOrder M]
    [Fintype L] [Fintype M] {j : L} {k : M}
    (e : {l : L // j < l} ≃ {m : M // k < m}) : upperRank j = upperRank k := Nat.card_congr e
end CCO.ResetOrder.Hierarchy
