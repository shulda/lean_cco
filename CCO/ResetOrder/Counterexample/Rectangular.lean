import CCO.ResetOrder.Counterexample.ConvexRanks
import Mathlib.Data.Prod.Lex

/-! Rectangular nested-equivalence hosts, and exact comparisons between
convex blocks. These facts apply to any legal convex order of the host. -/
namespace CCO.ResetOrder.Counterexample

abbrev Rectangle (n : ℕ) := Fin n × Fin n × Fin n

def rectangleBase (n : ℕ) : Nested (Rectangle n) where
  P := Setoid.ker Prod.fst
  Q := Setoid.ker (fun x => (x.1, x.2.1))
  refine := by
    intro x y h
    exact congrArg (fun z : Fin n × Fin n => z.1) h

private abbrev RectangleKey (n : ℕ) := Fin n ×ₗ (Fin n ×ₗ Fin n)

def rectangleKey {n : ℕ} (x : Rectangle n) : RectangleKey n :=
  toLex (x.1, toLex x.2)


private theorem rectangle_le_p {n : ℕ} (x y : Rectangle n)
    (h : rectangleKey x ≤ rectangleKey y) : x.1 ≤ y.1 :=
  @Prod.Lex.monotone_fst (Fin n) (Fin n ×ₗ Fin n) _ _
    (rectangleKey x) (rectangleKey y) h

def rectangleOrder (n : ℕ) : (rectangleBase n).ConvexOrder where
  order := LinearOrder.lift' rectangleKey (by
    intro x y h
    exact congrArg (fun k : RectangleKey n => ((ofLex k).1, ofLex (ofLex k).2)) h)
  convexP := by
    intro a b c hab hbc hac
    change rectangleKey a ≤ rectangleKey b at hab
    change rectangleKey b ≤ rectangleKey c at hbc
    change a.1 = b.1
    change a.1 = c.1 at hac
    exact le_antisymm (rectangle_le_p a b hab)
      (hac ▸ rectangle_le_p b c hbc)
  convexQ := by
    intro a b c hab hbc hac
    change rectangleKey a ≤ rectangleKey b at hab
    change rectangleKey b ≤ rectangleKey c at hbc
    change (a.1, a.2.1) = (c.1, c.2.1) at hac
    change (a.1, a.2.1) = (b.1, b.2.1)
    have hpac : a.1 = c.1 := congrArg (fun z : Fin n × Fin n => z.1) hac
    have hpab : a.1 = b.1 := le_antisymm (rectangle_le_p a b hab)
      (hpac ▸ rectangle_le_p b c hbc)
    have hpbc : b.1 = c.1 := hpab.symm.trans hpac
    have hqab := (Prod.Lex.toLex_le_toLex'.mp hab).2 hpab
    have hqbc := (Prod.Lex.toLex_le_toLex'.mp hbc).2 hpbc
    have hqac : a.2.1 = c.2.1 := congrArg (fun z : Fin n × Fin n => z.2) hac
    exact Prod.ext hpab (le_antisymm (Prod.Lex.monotone_fst _ _ hqab)
      (hqac ▸ Prod.Lex.monotone_fst _ _ hqbc))

theorem rectangle_lt_iff {n : ℕ} (x y : Rectangle n) :
    (rectangleOrder n).order.lt x y ↔
      x.1 < y.1 ∨ x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ x.2.1 = y.2.1 ∧ x.2.2 < y.2.2) := by
  change rectangleKey x < rectangleKey y ↔ _
  simp only [rectangleKey, Prod.Lex.toLex_lt_toLex]

/-- Distinct convex classes are wholly separated. The representatives are
arbitrary points of the same two actual classes. -/
theorem compare_convex_classes {X : Type*} (o : LinearOrder X) (R : Setoid X)
    (convex : ∀ {a b c}, o.le a b → o.le b c → R.r a c → R.r a b)
    {x y x' y' : X} (hx : R.r x x') (hy : R.r y y') (hxy : ¬ R.r x y) :
    o.lt x y ↔ o.lt x' y' := by
  have hxy' : ¬ R.r x' y' := fun h => hxy (R.trans hx (R.trans h (R.symm hy)))
  constructor
  · intro h
    have hq := (convexQuotient_lt_iff o R convex x y).mpr ⟨h, hxy⟩
    rw [Quotient.sound hx, Quotient.sound hy] at hq
    exact ((convexQuotient_lt_iff o R convex x' y').mp hq).1
  · intro h
    have hq := (convexQuotient_lt_iff o R convex x' y').mpr ⟨h, hxy'⟩
    rw [← Quotient.sound hx, ← Quotient.sound hy] at hq
    exact ((convexQuotient_lt_iff o R convex x y).mp hq).1

namespace Nested.ConvexOrder
variable {X : Type*} [Finite X] {A : Nested X} (a : ConvexOrder A)

/-- Every finite ordered nested-equivalence diagram embeds in a rectangle
of side card(X). This is its actual ordered block-rank representation. -/
noncomputable def rankEmbedding :
    Embedding a (rectangleOrder (Nat.card X)) where
  point x := (⟨a.pRank x, a.pRank_lt_card x⟩,
    ⟨a.qRank x, a.qRank_lt_card x⟩, ⟨orderRank a.order x, orderRank_lt_card _ x⟩)
  injective := by
    intro x y h
    exact (orderRank_injective a.order) (congrArg (fun t : Rectangle (Nat.card X) => t.2.2.val) h)
  p_iff x y := by
    change (⟨a.pRank x, _⟩ : Fin (Nat.card X)) = ⟨a.pRank y, _⟩ ↔ A.P.r x y
    exact Fin.ext_iff.trans a.pRank_eq_iff
  q_iff x y := by
    change ((⟨a.pRank x, _⟩ : Fin (Nat.card X)), (⟨a.qRank x, _⟩ : Fin (Nat.card X))) =
      (⟨a.pRank y, _⟩, ⟨a.qRank y, _⟩) ↔ A.Q.r x y
    rw [Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff, a.pRank_eq_iff, a.qRank_eq_iff]
    exact ⟨And.right, fun h => ⟨A.refine h, h⟩⟩
  lt_iff x y := by
    rw [rectangle_lt_iff]
    simp only [Fin.mk.injEq]
    change (a.pRank x < a.pRank y ∨ a.pRank x = a.pRank y ∧
      (a.qRank x < a.qRank y ∨ a.qRank x = a.qRank y ∧
        orderRank a.order x < orderRank a.order y)) ↔ a.order.lt x y
    rw [a.pRank_lt_iff, a.pRank_eq_iff, a.qRank_lt_iff,
      a.qRank_eq_iff, orderRank_lt_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, (⟨h, _⟩ | ⟨_, h⟩)⟩) <;> exact h
    · intro h
      by_cases hp : A.P.r x y
      · right
        refine ⟨hp, ?_⟩
        by_cases hq : A.Q.r x y
        · exact Or.inr ⟨hq, h⟩
        · exact Or.inl ⟨h, hq⟩
      · exact Or.inl ⟨h, hp⟩

end Nested.ConvexOrder
end CCO.ResetOrder.Counterexample
