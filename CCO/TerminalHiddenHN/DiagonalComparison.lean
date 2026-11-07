import CCO.TerminalHiddenHN.GenericReadout
import Mathlib.Order.OrderDual

/-! Two distinct term values at one actual real root detect reversal of the
hidden order. On a singleton every comparison between distinct real roots
agrees vacuously, so those comparisons cannot determine the readout. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P)

/-- Reverse the actual order on the same literal generated closure. -/
def reverseReadout {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    D.ReadoutOn A :=
  ⟨@OrderDual.instLinearOrder (D.realClosure A) a.order⟩

theorem termComparison_reverse_iff {A : CCO.FiniteInduced (X := X)}
    (a : D.ReadoutOn A) {s t j z : U.Sorts}
    (q : Term U s t) (p : Term U j z) (x y : A.vertices) :
    D.TermComparison (D.reverseReadout a) q p x y ↔ D.TermComparison a p q y x :=
  Iff.rfl

/-- This retains all typed term pairs but only distinct original roots. -/
def OffDiagonalComparisonsAgree {A : CCO.FiniteInduced (X := X)}
    (a b : D.ReadoutOn A) : Prop :=
  ∀ {s t j z : U.Sorts} (q : Term U s t) (p : Term U j z)
    (x y : A.vertices), x ≠ y →
      (D.TermComparison a q p x y ↔ D.TermComparison b q p x y)

theorem offDiagonal_comparisons_agree_of_subsingleton
    {A : CCO.FiniteInduced (X := X)} (hA : A.vertices.Subsingleton)
    (a b : D.ReadoutOn A) : D.OffDiagonalComparisonsAgree a b := by
  intro s t j z q p x y hxy
  exact (hxy (Subtype.ext (hA x.property y.property))).elim

/-- A diagonal comparison changes under reversal whenever its two
correctly typed values at the same marked root are distinct. -/
theorem diagonal_comparison_changes {A : CCO.FiniteInduced (X := X)}
    (a : D.ReadoutOn A) (x : A.vertices) {t z : U.Sorts}
    (q : Term U (D.realSort x.val.1) t) (p : Term U (D.realSort x.val.1) z)
    (hne : P.eval q (D.realPoint x.val) ≠ P.eval p (D.realPoint x.val)) :
    ¬ (D.TermComparison a q p x x ↔ D.TermComparison (D.reverseReadout a) q p x x) := by
  letI : LinearOrder (D.realClosure A) := a.order
  have hn : D.termPoint q x ≠ D.termPoint p x := by
    intro h
    exact hne (congrArg Subtype.val h)
  intro h
  have hh := h.trans (D.termComparison_reverse_iff a q p x x)
  change (D.termPoint q x < D.termPoint p x ↔ D.termPoint p x < D.termPoint q x) at hh
  rcases lt_trichotomy (D.termPoint q x) (D.termPoint p x) with hlt | heq | hgt
  · exact lt_asymm hlt (hh.mp hlt)
  · exact hn heq
  · exact lt_asymm hgt (hh.mpr hgt)

/-- Distinct output sorts already guarantee distinct actual term values. -/
theorem term_values_ne_of_output_ne {A : CCO.FiniteInduced (X := X)}
    (x : A.vertices) {t z : U.Sorts}
    (q : Term U (D.realSort x.val.1) t) (p : Term U (D.realSort x.val.1) z)
    (htz : t ≠ z) :
    P.eval q (D.realPoint x.val) ≠ P.eval p (D.realPoint x.val) := by
  intro h
  exact htz ((P.eval_sort q (D.sort_realPoint x.val)).symm.trans
    ((congrArg P.sort h).trans (P.eval_sort p (D.sort_realPoint x.val))))

theorem diagonal_comparison_changes_of_output_ne {A : CCO.FiniteInduced (X := X)}
    (a : D.ReadoutOn A) (x : A.vertices) {t z : U.Sorts}
    (q : Term U (D.realSort x.val.1) t) (p : Term U (D.realSort x.val.1) z)
    (htz : t ≠ z) :
    ¬ (D.TermComparison a q p x x ↔ D.TermComparison (D.reverseReadout a) q p x x) :=
  D.diagonal_comparison_changes a x q p (D.term_values_ne_of_output_ne x q p htz)

/-- For any actual singleton, deleting same-root comparisons loses
information as soon as two term values at its root differ. -/
theorem singleton_diagonal_necessary {A : CCO.FiniteInduced (X := X)}
    (hA : A.vertices.Subsingleton) (a : D.ReadoutOn A) (x : A.vertices)
    {t z : U.Sorts} (q : Term U (D.realSort x.val.1) t)
    (p : Term U (D.realSort x.val.1) z)
    (hne : P.eval q (D.realPoint x.val) ≠ P.eval p (D.realPoint x.val)) :
    D.OffDiagonalComparisonsAgree a (D.reverseReadout a) ∧
      ¬ (D.TermComparison a q p x x ↔ D.TermComparison (D.reverseReadout a) q p x x) ∧
      a ≠ D.reverseReadout a := by
  have hc := D.diagonal_comparison_changes a x q p hne
  refine ⟨D.offDiagonal_comparisons_agree_of_subsingleton hA a (D.reverseReadout a),hc,?_⟩
  intro h
  exact hc (iff_of_eq (congrArg (fun b => D.TermComparison b q p x x) h))

end
end CCO.TerminalHiddenHN.RealInterpretation
