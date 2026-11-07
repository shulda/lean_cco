import CCO.TerminalHiddenHN.GenericReadout
import CCO.TerminalHiddenHN.InterpretationNormalForms
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma

/-! The finite comparison alphabet is derived from actual semantic term
normal forms. It compares ALL typed presentations, including two terms
on the same real root, and determines the entire chosen closure order. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P) (H : CCO.HomogeneousSource S G)

abbrev ComparisonName := Σ i : ι, Σ j : ι, Σ s : U.Sorts, Σ t : U.Sorts,
  Fin (D.functionCount H (D.realSort i) s) ×
    Fin (D.functionCount H (D.realSort j) t)

theorem ComparisonName_finite : Finite (D.ComparisonName H) := by
  classical
  letI : Fintype ι := S.finiteSort
  letI : Fintype U.Sorts := @Fintype.ofFinite U.Sorts D.finiteSorts
  unfold ComparisonName
  infer_instance

attribute [instance] ComparisonName_finite

def comparison {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (q : D.ComparisonName H) (x y : A.vertices) : Prop :=
  x.val.1 = q.1 ∧ y.val.1 = q.2.1 ∧
    D.TermComparison a (D.normalTerm H (D.realSort q.1) q.2.2.1 q.2.2.2.2.1)
      (D.normalTerm H (D.realSort q.2.1) q.2.2.2.1 q.2.2.2.2.2) x y

theorem comparison_sorted {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (q : D.ComparisonName H) (x y : A.vertices) (h : D.comparison H a q x y) :
    x.val.1 = q.1 ∧ y.val.1 = q.2.1 := ⟨h.1,h.2.1⟩

theorem comparison_readoutEmbedding {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} (e : D.ReadoutEmbedding H a b)
    (q : D.ComparisonName H) (x y : A.vertices) :
    D.comparison H a q x y ↔ D.comparison H b q (e.old.toEmbedding x) (e.old.toEmbedding y) := by
  unfold comparison
  rw [e.old.preserves_sort x,e.old.preserves_sort y]
  exact and_congr_right (fun _ => and_congr_right (fun _ =>
    (D.readout_comparison_iff H e _ _ x y).symm))

theorem comparison_restrict {A B : CCO.FiniteInduced (X := X)}
    (e : CCO.InducedEmbedding S A B) (b : D.ReadoutOn B)
    (q : D.ComparisonName H) (x y : A.vertices) :
    D.comparison H (D.restrictReadout H e b) q x y ↔
      D.comparison H b q (e.toEmbedding x) (e.toEmbedding y) :=
  D.comparison_readoutEmbedding H (D.restrictReadoutEmbedding H e b) q x y

private theorem eval_cast_source {B : Language.{k}} {Z : Type l} (P0 : Structure B Z)
    {s s' t : B.Sorts} (h : s = s') (q : Term B s t) (x : Z) :
    P0.eval (h ▸ q) x = P0.eval q x := by
  cases h; rfl

/-- Each actual closure point is one correctly typed original term at
one retained original root, before any normal form is selected. -/
theorem realClosure_term_surjective (A : CCO.FiniteInduced (X := X)) (x : D.realClosure A) :
    ∃ a : A.vertices, ∃ t, ∃ q : Term U (D.realSort a.val.1) t, D.termPoint q a = x := by
  obtain ⟨z,⟨p,hp,rfl⟩,t,q,hq⟩ := x.property
  refine ⟨⟨p,hp⟩,t,(D.sort_realPoint p) ▸ q,?_⟩
  exact Subtype.ext ((eval_cast_source P (D.sort_realPoint p) q _).trans hq)

/-- Finite forms cover the ENTIRE literal closure. In particular this
also covers pairs whose two presentations use the SAME real root. -/
theorem realClosure_form_surjective (A : CCO.FiniteInduced (X := X)) (x : D.realClosure A) :
    ∃ a : A.vertices, ∃ t : U.Sorts, ∃ i : Fin (D.functionCount H (D.realSort a.val.1) t),
      D.termPoint (D.normalTerm H (D.realSort a.val.1) t i) a = x := by
  obtain ⟨a,t,q,hq⟩ := D.realClosure_term_surjective A x
  refine ⟨a,t,D.normalIndex H q,?_⟩
  exact (Subtype.ext (D.normalTerm_eval H q _ (D.sort_realPoint a.val)).symm).trans hq

/-- The finite comparison tables have no additional arbitrary bits:
they faithfully determine the sole readout datum, the actual order. -/
theorem readout_faithful {A : CCO.FiniteInduced (X := X)} (a b : D.ReadoutOn A)
    (h : ∀ q x y, D.comparison H a q x y ↔ D.comparison H b q x y) : a = b := by
  have he : a.order = b.order := by
    apply LinearOrder.ext_lt
    intro x y
    obtain ⟨aa,s,i,hx⟩ := D.realClosure_form_surjective H A x
    obtain ⟨bb,t,j,hy⟩ := D.realClosure_form_surjective H A y
    have hh := h ⟨aa.val.1,bb.val.1,s,t,i,j⟩ aa bb
    change (aa.val.1 = aa.val.1 ∧ bb.val.1 = bb.val.1 ∧
      @LT.lt _ a.order.toLT _ _) ↔
      (aa.val.1 = aa.val.1 ∧ bb.val.1 = bb.val.1 ∧ @LT.lt _ b.order.toLT _ _) at hh
    simpa only [true_and,hx,hy] using hh
  cases a; cases b; cases he; rfl

/-- Every old induced embedding preserving the finite comparison tables
has the unique marked, ordered hidden extension. -/
def readoutEmbedding_of_comparisons {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} (e : CCO.InducedEmbedding S A B)
    (h : ∀ q x y, D.comparison H a q x y ↔
      D.comparison H b q (e.toEmbedding x) (e.toEmbedding y)) : D.ReadoutEmbedding H a b := by
  refine ⟨e,?_⟩
  intro x y
  obtain ⟨aa,s,i,hx⟩ := D.realClosure_form_surjective H A x
  obtain ⟨bb,t,j,hy⟩ := D.realClosure_form_surjective H A y
  have hh := (h ⟨aa.val.1,bb.val.1,s,t,i,j⟩ aa bb).symm
  simp only [comparison,e.preserves_sort,true_and] at hh
  change @LT.lt _ b.order.toLT _ _ ↔ @LT.lt _ a.order.toLT _ _ at hh
  have hxl := D.closureMap_term H e (D.normalTerm H (D.realSort aa.val.1) s i) aa
  have hyl := D.closureMap_term H e (D.normalTerm H (D.realSort bb.val.1) t j) bb
  simpa only [← hxl,← hyl,hx,hy] using hh

theorem comparison_embedding_iff {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} (e : CCO.InducedEmbedding S A B) :
    (∃ f : D.ReadoutEmbedding H a b, f.old = e) ↔
      ∀ q x y, D.comparison H a q x y ↔
        D.comparison H b q (e.toEmbedding x) (e.toEmbedding y) := by
  constructor
  · rintro ⟨f,rfl⟩
    exact D.comparison_readoutEmbedding H f
  · intro h
    exact ⟨D.readoutEmbedding_of_comparisons H e h,rfl⟩

theorem readout_nonempty (H : CCO.HomogeneousSource S G) (A : CCO.FiniteInduced (X := X)) : Nonempty (D.ReadoutOn A) := by
  letI : Finite (D.realClosure A) := (D.realClosurePiece H A).finite.to_subtype
  letI : Fintype (D.realClosure A) := Fintype.ofFinite _
  exact ⟨⟨LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective⟩⟩

end
end CCO.TerminalHiddenHN.RealInterpretation
