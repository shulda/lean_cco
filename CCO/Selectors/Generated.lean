import CCO.Selectors.Basic
import CCO.Selectors.NR2
import Mathlib.Logic.Function.Iterate

/-! Genuine original typed normal forms, with absent multipliers represented
by identity actions and never by a new strong menu. -/
universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

inductive Outside : ι → ι → Type (max u w)
  | absent (i : ι) : Outside i i
  | present {i j} (P : S.Menu i j) (exact : StrongExact.Exact S P) : Outside i j

namespace Outside
variable {S} {a b c d : ι}
def left : Outside S a b → S.Menu b c → S.Menu a c
  | .absent _, A => A
  | .present P _, A => S.product P A

def right (A : S.Menu a b) : Outside S b c → S.Menu a c
  | .absent _ => A
  | .present P _ => S.product A P

def comp (alg : ExactCalculus S) : Outside S a b → Outside S b c → Outside S a c
  | .absent _, R => R
  | .present P hP, .absent _ => .present P hP
  | .present P hP, .present Q hQ => .present (S.product P Q) (alg.product hP hQ)

def opposite (alg : ExactCalculus S) : Outside S a b → Outside S b a
  | .absent _ => .absent _
  | .present P hP => .present (S.opposite P) (alg.opposite hP)

theorem left_comp (alg : ExactCalculus S) (edge : S.RealEdgeGluing)
    (P : Outside S a b) (Q : Outside S b c) (A : S.Menu c d) :
    (comp alg P Q).left A = P.left (Q.left A) := by
  cases P <;> cases Q <;> simp only [comp,left]
  exact S.product_assoc_of_edge_gluing edge _ _ _

theorem right_comp (alg : ExactCalculus S) (edge : S.RealEdgeGluing)
    (A : S.Menu a b) (P : Outside S b c) (Q : Outside S c d) :
    right (right A P) Q = right A (comp alg P Q) := by
  cases P <;> cases Q <;> simp only [comp,right]
  exact S.product_assoc_of_edge_gluing edge _ _ _

theorem left_right (edge : S.RealEdgeGluing)
    (P : Outside S a b) (A : S.Menu b c) (Q : Outside S c d) :
    P.left (right A Q) = right (P.left A) Q := by
  cases P <;> cases Q <;> simp only [left,right]
  exact (S.product_assoc_of_edge_gluing edge _ _ _).symm

theorem opposite_left_right (alg : ExactCalculus S) (edge : S.RealEdgeGluing)
    (P : Outside S a b) (A : S.Menu b c) (Q : Outside S c d) :
    S.opposite (P.left (right A Q)) =
      (Q.opposite alg).left (right (S.opposite A) (P.opposite alg)) := by
  cases P <;> cases Q <;> simp only [left,right,opposite,S.product_opposite]
  exact S.product_assoc_of_edge_gluing edge _ _ _

end Outside

inductive NormalForm {a b : ι} (A : S.Menu a b) :
    {i j : ι} → S.Menu i j → Prop
  | forward {i j} (L : Outside S i a) (R : Outside S b j) :
      NormalForm A (L.left (Outside.right A R))
  | reverse {i j} (L : Outside S i b) (R : Outside S a j) :
      NormalForm A (L.left (Outside.right (S.opposite A) R))

/-- Every original product/converse generated menu has an actual two-sided
normal form in one of the two correctly typed orientations. -/
theorem generated_normalForm (alg : ExactCalculus S) (edge : S.RealEdgeGluing)
    {a b : ι} (A : S.Menu a b) {D : TaggedMenu S}
    (h : Generated S ⟨a,b,A⟩ D) :
    match D with | ⟨_,_,B⟩ => NormalForm S A B := by
  induction h with
  | seed => exact .forward (.absent _) (.absent _)
  | @opposite D h ih =>
    rcases D with ⟨i,j,B⟩
    cases ih with
    | forward L R =>
      simpa only [flip,Outside.opposite_left_right alg edge] using
        (NormalForm.reverse (S := S) (A := A) (R.opposite alg) (L.opposite alg))
    | reverse L R =>
      simpa only [flip,Outside.opposite_left_right alg edge,S.opposite_opposite] using
        (NormalForm.forward (S := S) (A := A) (R.opposite alg) (L.opposite alg))
  | left P hP h ih =>
    cases ih with
    | forward L R =>
      have hn := NormalForm.forward (S := S) (A := A) (Outside.comp alg (.present P hP) L) R
      rw [Outside.left_comp alg edge] at hn
      exact hn
    | reverse L R =>
      have hn := NormalForm.reverse (S := S) (A := A) (Outside.comp alg (.present P hP) L) R
      rw [Outside.left_comp alg edge] at hn
      exact hn
  | right P hP h ih =>
    cases ih with
    | forward L R =>
      have hn := NormalForm.forward (S := S) (A := A) L (Outside.comp alg R (.present P hP))
      rw [←Outside.right_comp alg edge, Outside.left_right edge] at hn
      exact hn
    | reverse L R =>
      have hn := NormalForm.reverse (S := S) (A := A) L (Outside.comp alg R (.present P hP))
      rw [←Outside.right_comp alg edge, Outside.left_right edge] at hn
      exact hn

/-- A parallel generated return is multiplication by loops or absent
identity actions, including reverse-oriented returns across different sorts. -/
theorem parallel_return (alg : ExactCalculus S) (edge : S.RealEdgeGluing)
    {i j : ι} {A B : S.Menu i j} (h : NormalForm S A B) :
    ∃ L : Outside S i i, ∃ R : Outside S j j, B = L.left (Outside.right A R) := by
  cases h with
  | forward L R => exact ⟨L,R,rfl⟩
  | reverse L R =>
    by_cases hij : i = j
    · subst j
      exact ⟨L,R,by rw [S.loop_opposite]⟩
    · cases L with
      | absent => exact False.elim (hij rfl)
      | present P hP =>
        cases R with
        | absent => exact False.elim (hij rfl)
        | present Q hQ =>
          refine ⟨.absent _,.present (S.product (S.opposite P) Q)
            (alg.product (alg.opposite hP) hQ),?_⟩
          simp only [Outside.left,Outside.right]
          have hs : S.product P (S.opposite A) = S.product A (S.opposite P) := by
            calc
              S.product P (S.opposite A) = S.opposite (S.product P (S.opposite A)) :=
                (S.loop_opposite _).symm
              _ = S.product A (S.opposite P) := by
                rw [S.product_opposite,S.opposite_opposite]
          rw [←S.product_assoc_of_edge_gluing edge,hs,S.product_assoc_of_edge_gluing edge]

end CCO.Selectors
