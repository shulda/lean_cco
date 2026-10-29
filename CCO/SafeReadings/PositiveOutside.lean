import CCO.SafeReadings.MenuCalculus

/-! Positive outside profiles. Absence is an identity operation on menus;
it is never an equality atom or a diversity menu. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

inductive PositiveOutside : ι → ι → Type (max u w)
  | absent (i : ι) : PositiveOutside i i
  | present {i j} (P : S.Menu i j) (nonempty : P.Nonempty) : PositiveOutside i j

namespace PositiveOutside
variable {S} {a b c d : ι}

def positive : PositiveOutside S a b → Bool
  | .absent _ => false
  | .present _ _ => true

def left : PositiveOutside S a b → S.Menu b c → S.Menu a c
  | .absent _, A => A
  | .present P _, A => S.product P A

def right (A : S.Menu a b) : PositiveOutside S b c → S.Menu a c
  | .absent _ => A
  | .present P _ => S.product A P

def comp (point : S.RealPointGluing) :
    PositiveOutside S a b → PositiveOutside S b c → PositiveOutside S a c
  | .absent _, R => R
  | .present P hP, .absent _ => .present P hP
  | .present P hP, .present Q hQ =>
      .present (S.product P Q) (S.product_nonempty_of_point_gluing point hP hQ)

def opposite : PositiveOutside S a b → PositiveOutside S b a
  | .absent _ => .absent _
  | .present P hP => .present (S.opposite P) (by
      obtain ⟨a, ha⟩ := hP
      refine ⟨S.conv a, ?_⟩
      change S.conv (S.conv a) ∈ P
      rw [S.conv_invol]
      exact ha)

@[simp] theorem positive_comp (point : S.RealPointGluing)
    (P : PositiveOutside S a b) (Q : PositiveOutside S b c) :
    (P.comp point Q).positive = (P.positive || Q.positive) := by
  cases P <;> cases Q <;> rfl

@[simp] theorem positive_opposite (P : PositiveOutside S a b) :
    P.opposite.positive = P.positive := by cases P <;> rfl

theorem left_comp (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (P : PositiveOutside S a b) (Q : PositiveOutside S b c) (A : S.Menu c d) :
    (P.comp point Q).left A = P.left (Q.left A) := by
  cases P <;> cases Q <;> simp only [comp, left]
  exact S.product_assoc_of_edge_gluing edge _ _ _

theorem right_comp (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (A : S.Menu a b) (P : PositiveOutside S b c) (Q : PositiveOutside S c d) :
    right (right A P) Q = right A (P.comp point Q) := by
  cases P <;> cases Q <;> simp only [comp, right]
  exact S.product_assoc_of_edge_gluing edge _ _ _

theorem left_right (edge : S.RealEdgeGluing)
    (P : PositiveOutside S a b) (A : S.Menu b c) (Q : PositiveOutside S c d) :
    P.left (right A Q) = right (P.left A) Q := by
  cases P <;> cases Q <;> simp only [left, right]
  exact (S.product_assoc_of_edge_gluing edge _ _ _).symm

theorem opposite_left_right (edge : S.RealEdgeGluing)
    (P : PositiveOutside S a b) (A : S.Menu b c) (Q : PositiveOutside S c d) :
    S.opposite (P.left (right A Q)) =
      Q.opposite.left (right (S.opposite A) P.opposite) := by
  cases P <;> cases Q <;> simp only [left, right, opposite, S.product_opposite]
  exact S.product_assoc_of_edge_gluing edge _ _ _

theorem left_nonempty (point : S.RealPointGluing)
    (P : PositiveOutside S a b) {A : S.Menu b c} (hA : A.Nonempty) :
    (P.left A).Nonempty := by
  cases P with
  | absent => exact hA
  | present P hP => exact S.product_nonempty_of_point_gluing point hP hA

theorem right_nonempty (point : S.RealPointGluing)
    {A : S.Menu a b} (hA : A.Nonempty) (P : PositiveOutside S b c) :
    (right A P).Nonempty := by
  cases P with
  | absent => exact hA
  | present P hP => exact S.product_nonempty_of_point_gluing point hA hP

end PositiveOutside

end CCO.SafeReadings

namespace CCO.Selectors.PureTagAction
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Λ : Type z} [Group Λ] {N : Type t} (A : Selectors.PureTagAction S Λ N)

/-- The genuine pure action on a menu, with its transported endpoints displayed. -/
def menuAct (g : Λ) {i j} (P : S.Menu i j) : S.Menu (A.tag g i) (A.tag g j) :=
  cast (congrArg₂ S.Menu (A.source g ⟨i,j,P⟩) (A.target g ⟨i,j,P⟩))
    (A.act g ⟨i,j,P⟩).2.2

theorem tagged_menuAct (g : Λ) {i j} (P : S.Menu i j) :
    (⟨A.tag g i,A.tag g j,A.menuAct g P⟩ : TaggedMenu S) = A.act g ⟨i,j,P⟩ := by
  have cast_tag (E : TaggedMenu S) (a b : ι) (ha : E.1 = a) (hb : E.2.1 = b) :
      (⟨a,b,cast (congrArg₂ S.Menu ha hb) E.2.2⟩ : TaggedMenu S) = E := by
    rcases E with ⟨i',j',E⟩
    dsimp at ha hb ⊢
    cases ha; cases hb
    rfl
  exact cast_tag (A.act g ⟨i,j,P⟩) (A.tag g i) (A.tag g j)
    (A.source g ⟨i,j,P⟩) (A.target g ⟨i,j,P⟩)

theorem menuAct_nonempty (g : Λ) {i j} {P : S.Menu i j} (hP : P.Nonempty) :
    (A.menuAct g P).Nonempty := by
  obtain ⟨a, ha⟩ := hP
  have hn : A.label a ∈ names S A.label (A.act g ⟨i,j,P⟩) := by
    rw [A.literal]; exact ⟨a,ha,rfl⟩
  rw [← A.tagged_menuAct] at hn
  obtain ⟨b,hb,_⟩ := hn
  exact ⟨b,hb⟩

theorem menuAct_opposite (g : Λ) {i j} (P : S.Menu i j) :
    A.menuAct g (S.opposite P) = S.opposite (A.menuAct g P) := by
  have he := A.opposite g ⟨i,j,P⟩
  rw [← A.tagged_menuAct, ← A.tagged_menuAct] at he
  simpa only [flip, Sigma.mk.injEq, heq_eq_eq, true_and] using he

theorem menuAct_product (g : Λ) {i j k} (P : S.Menu i j) (Q : S.Menu j k) :
    A.menuAct g (S.product P Q) = S.product (A.menuAct g P) (A.menuAct g Q) := by
  have hp : IsProduct S (A.act g ⟨i,j,P⟩) (A.act g ⟨j,k,Q⟩)
      (A.act g ⟨i,k,S.product P Q⟩) := A.product g ⟨i,j,k,P,Q,rfl,rfl,rfl⟩
  rw [← A.tagged_menuAct, ← A.tagged_menuAct, ← A.tagged_menuAct] at hp
  obtain ⟨a,b,c,P',Q',hP,hQ,hR⟩ := hp
  cases hP; cases hQ
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hR

end CCO.Selectors.PureTagAction
