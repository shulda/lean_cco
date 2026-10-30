import CCO.ResetOrder.Counterexample.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite convex quotients carry their actual induced linear orders. Their
ranks give a faithful three-coordinate ordered-block representation. -/
universe u
namespace CCO.ResetOrder.Counterexample

private def convexFibres {X : Type u} (o : LinearOrder X) (R : Setoid X)
    (h : ∀ {a b c}, o.le a b → o.le b c → R.r a c → R.r a b) :
    ∀ q : Quotient R, @Set.OrdConnected X o.toPreorder (Quotient.mk R ⁻¹' {q}) := by
  intro q
  constructor
  intro x hx y hy z hz
  change Quotient.mk R x = q at hx
  change Quotient.mk R y = q at hy
  change Quotient.mk R z = q
  have hxy : R.r x y := Quotient.exact (hx.trans hy.symm)
  exact (Quotient.sound (h hz.1 hz.2 hxy)).symm.trans hx

noncomputable def convexQuotientOrder {X : Type u} (o : LinearOrder X) (R : Setoid X)
    (h : ∀ {a b c}, o.le a b → o.le b c → R.r a c → R.r a b) :
    LinearOrder (Quotient R) := by
  classical
  letI := o
  letI := convexFibres o R h
  infer_instance

theorem convexQuotient_lt_iff {X : Type u} (o : LinearOrder X) (R : Setoid X)
    (h : ∀ {a b c}, o.le a b → o.le b c → R.r a c → R.r a b) (x y : X) :
    (convexQuotientOrder o R h).lt (Quotient.mk R x) (Quotient.mk R y) ↔
      o.lt x y ∧ ¬ R.r x y := by
  classical
  letI := o
  letI := convexFibres o R h
  exact Quotient.mk_lt_mk

noncomputable def orderRank {X : Type u} [Finite X] (o : LinearOrder X) (x : X) : ℕ := by
  letI := o
  letI := Fintype.ofFinite X
  exact ((Fintype.orderIsoFinOfCardEq X rfl).symm x).val

theorem orderRank_lt_iff {X : Type u} [Finite X] (o : LinearOrder X) (x y : X) :
    orderRank o x < orderRank o y ↔ o.lt x y := by
  letI := o
  letI := Fintype.ofFinite X
  exact (Fintype.orderIsoFinOfCardEq X rfl).symm.lt_iff_lt

theorem orderRank_injective {X : Type u} [Finite X] (o : LinearOrder X) :
    Function.Injective (orderRank o) := by
  intro x y h
  letI := o
  exact le_antisymm (le_of_not_gt (fun hyx =>
    (lt_irrefl _ : ¬ orderRank o y < orderRank o y)
      (h ▸ (orderRank_lt_iff o y x).mpr hyx)))
    (le_of_not_gt (fun hxy =>
    (lt_irrefl _ : ¬ orderRank o y < orderRank o y)
      (h ▸ (orderRank_lt_iff o x y).mpr hxy)))

theorem orderRank_lt_card {X : Type u} [Finite X] (o : LinearOrder X) (x : X) :
    orderRank o x < Nat.card X := by
  letI := o
  letI := Fintype.ofFinite X
  simpa only [orderRank, Nat.card_eq_fintype_card] using
    ((Fintype.orderIsoFinOfCardEq X rfl).symm x).isLt

namespace Nested.ConvexOrder
variable {X : Type u} [Finite X] {A : Nested X} (a : ConvexOrder A)

noncomputable def pRank (x : X) : ℕ :=
  orderRank (convexQuotientOrder a.order A.P a.convexP) (Quotient.mk A.P x)
noncomputable def qRank (x : X) : ℕ :=
  orderRank (convexQuotientOrder a.order A.Q a.convexQ) (Quotient.mk A.Q x)
noncomputable def vRank (x : X) : ℕ := orderRank a.order x

theorem pRank_eq_iff {x y : X} : a.pRank x = a.pRank y ↔ A.P.r x y := by
  exact (orderRank_injective _).eq_iff.trans Quotient.eq_iff_equiv

theorem qRank_eq_iff {x y : X} : a.qRank x = a.qRank y ↔ A.Q.r x y := by
  exact (orderRank_injective _).eq_iff.trans Quotient.eq_iff_equiv

theorem pRank_lt_iff {x y : X} : a.pRank x < a.pRank y ↔ a.order.lt x y ∧ ¬ A.P.r x y :=
  (orderRank_lt_iff _ _ _).trans (convexQuotient_lt_iff _ _ _ x y)

theorem qRank_lt_iff {x y : X} : a.qRank x < a.qRank y ↔ a.order.lt x y ∧ ¬ A.Q.r x y :=
  (orderRank_lt_iff _ _ _).trans (convexQuotient_lt_iff _ _ _ x y)

theorem pRank_lt_card (x : X) : a.pRank x < Nat.card X := by
  exact lt_of_lt_of_le (orderRank_lt_card _ _) (Nat.card_le_card_of_surjective
    (Quotient.mk A.P) Quotient.mk_surjective)

theorem qRank_lt_card (x : X) : a.qRank x < Nat.card X := by
  exact lt_of_lt_of_le (orderRank_lt_card _ _) (Nat.card_le_card_of_surjective
    (Quotient.mk A.Q) Quotient.mk_surjective)

end Nested.ConvexOrder
end CCO.ResetOrder.Counterexample
