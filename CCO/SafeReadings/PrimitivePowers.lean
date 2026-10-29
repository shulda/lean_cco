import CCO.Selectors.NR2
import Mathlib.Data.Set.Card

/-! Uniform positive powers of arbitrary nonempty diversity loops. No exactness
or CCO assumption is used; equality occurs only in an interpreted equivalence. -/
universe u v w t
namespace CCO.SafeReadings
open CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Full primitivity on each actual named sort, without a definability restriction. -/
def SortwisePrimitive : Prop :=
  ∀ i (R : Setoid (X i)), ColourInvariantSetoid S R → R = ⊥ ∨ R = ⊤

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (primitive : SortwisePrimitive S)
variable {i : ι}

include H primitive in
/-- A nonempty idempotent diversity loop is the whole loop palette. -/
theorem primitive_closed_menu_full (J : S.Menu i i) (hJ : J.Nonempty)
    (closed : S.product J J ⊆ J) : J = Set.univ := by
  let R := menuSetoid S J closed
  have hR : ColourInvariantSetoid S R :=
    colourInvariantSetoid_of_invariant S H R (menuSetoid_invariant S H J closed)
  rcases primitive i R hR with he | he
  · obtain ⟨a, ha⟩ := hJ
    obtain ⟨x, y, hc⟩ := S.realized a
    have hr : R.r x y := Or.inr ⟨a, ha, hc⟩
    rw [he] at hr
    exact False.elim (S.menuRel_ne (⟨a, ha, hc⟩ : S.menuRel J x y) (congrArg (Sigma.mk i) hr))
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨x, y, hc⟩ := S.realized a
    have hr : R.r x y := by rw [he]; trivial
    rcases hr with hxy | ⟨b, hb, hd⟩
    · exact False.elim (S.menuRel_ne (⟨a, Set.mem_univ a, hc⟩ :
        S.menuRel (Set.univ : S.Menu i i) x y) (congrArg (Sigma.mk i) hxy))
    · have hab : b = a := Option.some.inj (hd.symm.trans hc)
      exact hab ▸ hb

/-- Index n denotes the positive even exponent 2(n+1). -/
def evenPower (W : S.Menu i i) (n : Nat) : S.Menu i i :=
  loopPower S W (2*n+1)

variable (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
variable (W : S.Menu i i) (hW : W.Nonempty)

include point hW in
theorem evenPower_nonempty (n : Nat) : (evenPower S W n).Nonempty :=
  loopPower_nonempty S point W hW _

include point edge hW in
theorem evenPower_mono : Monotone (evenPower S W) :=
  loopPower_parity_monotone S point edge W hW 1

include edge in
theorem evenPower_succ (n : Nat) :
    evenPower S W (n+1) = S.product (evenPower S W n) (evenPower S W 0) := by
  rw [evenPower, evenPower, evenPower, loopPower_add S edge]
  congr 1

include edge in
theorem evenPower_stable_of_adjacent {n : Nat}
    (hn : evenPower S W n = evenPower S W (n+1)) :
    ∀ k, n ≤ k → evenPower S W k = evenPower S W n := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [evenPower_succ S edge, ih, ← evenPower_succ S edge, ← hn]

include H primitive point edge hW in
theorem evenPower_full_of_adjacent {n : Nat}
    (hn : evenPower S W n = evenPower S W (n+1)) :
    evenPower S W n = Set.univ := by
  apply primitive_closed_menu_full S H primitive _ (evenPower_nonempty S point W hW n)
  have hidem : S.product (evenPower S W n) (evenPower S W n) = evenPower S W n := by
    simp only [evenPower, loopPower_add S edge]
    rw [show (2*n+1)+(2*n+1)+1 = 2*(2*n+1)+1 by omega]
    exact evenPower_stable_of_adjacent S edge W hn (2*n+1) (by omega)
  rw [hidem]

include H primitive point edge hW in
/-- The exact source bound: exponent 2 times the size of the loop palette. -/
theorem primitive_loopPower_full :
    loopPower S W (2 * Nat.card (S.Atom i i) - 1) = Set.univ := by
  classical
  let : Fintype (S.Atom i i) := S.finiteAtom i i
  let m := Nat.card (S.Atom i i)
  have hm : 0 < m := by
    obtain ⟨a, _⟩ := hW
    exact Nat.card_pos_iff.mpr ⟨⟨a⟩, inferInstance⟩
  have grow (n : Nat) (hn : n < m) : n+1 ≤ (evenPower S W n).ncard := by
    induction n with
    | zero => exact (evenPower_nonempty S point W hW 0).ncard_pos
    | succ n ih =>
      have ih := ih (by omega)
      by_cases he : evenPower S W n = evenPower S W (n+1)
      · have ht := evenPower_full_of_adjacent S H primitive point edge W hW he
        rw [← he, ht, Set.ncard_univ]
        omega
      · have hs : evenPower S W n ⊂ evenPower S W (n+1) :=
          (evenPower_mono S point edge W hW (Nat.le_succ n)).ssubset_of_ne he
        have hc := Set.ncard_lt_ncard hs
        omega
  have hc := grow (m-1) (by omega)
  have he : evenPower S W (m-1) = Set.univ := by
    apply (Set.eq_univ_iff_ncard _).mpr
    have hu := Set.ncard_le_card (evenPower S W (m-1))
    change (evenPower S W (m-1)).ncard ≤ m at hu
    omega
  simpa only [evenPower, show 2*(m-1)+1 = 2*m-1 by omega] using he

include H primitive point edge hW in
/-- Every later positive power is also full; indices are exponents minus one. -/
theorem primitive_loopPower_full_of_le (n : Nat)
    (hn : 2 * Nat.card (S.Atom i i) - 1 ≤ n) :
    loopPower S W n = Set.univ := by
  induction n, hn using Nat.le_induction with
  | base => exact primitive_loopPower_full S H primitive point edge W hW
  | succ n hn ih =>
    rw [loopPower_succ, ih]
    exact S.top_product_of_point_gluing point W hW

end CCO.SafeReadings
