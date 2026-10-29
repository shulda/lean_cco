import CCO.SafeReadings.PositiveOutside

/-! Typed Gamma/converse normal forms retain a syntactic positive bit.
Every multiplication contributes a positive outside word; transport and
converse preserve it, including nonexact ambient multipliers. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

namespace PositiveOutside
variable {S} {a b c d : ι}
def move (g : Λ) : PositiveOutside S a b →
    PositiveOutside S (A.tag g a) (A.tag g b)
  | .absent _ => .absent _
  | .present P hP => .present (A.menuAct g P) (A.menuAct_nonempty g hP)

@[simp] theorem positive_move (g : Λ) (P : PositiveOutside S a b) :
    (P.move A g).positive = P.positive := by cases P <;> rfl

theorem move_left (g : Λ) (P : PositiveOutside S a b) (D : S.Menu b c) :
    A.menuAct g (P.left D) = (P.move A g).left (A.menuAct g D) := by
  cases P <;> simp only [left, move, A.menuAct_product]

theorem move_right (g : Λ) (D : S.Menu a b) (P : PositiveOutside S b c) :
    A.menuAct g (right D P) = right (A.menuAct g D) (P.move A g) := by
  cases P <;> simp only [right, move, A.menuAct_product]
end PositiveOutside

/-- The bit records whether THIS path has made a multiplication move. -/
inductive PositiveGenerated (Q : Family S) (seed : TaggedMenu S) : TaggedMenu S → Bool → Prop
  | seed : PositiveGenerated Q seed seed false
  | opposite {D p} : PositiveGenerated Q seed D p → PositiveGenerated Q seed (flip S D) p
  | left {i j k} (P : S.Menu i j) (hP : (⟨i,j,P⟩ : TaggedMenu S) ∈ Q)
      {D : S.Menu j k} {p} : PositiveGenerated Q seed ⟨j,k,D⟩ p →
      PositiveGenerated Q seed ⟨i,k,S.product P D⟩ true
  | right {i j k} {D : S.Menu i j} (P : S.Menu j k)
      (hP : (⟨j,k,P⟩ : TaggedMenu S) ∈ Q) {p} :
      PositiveGenerated Q seed ⟨i,j,D⟩ p → PositiveGenerated Q seed ⟨i,k,S.product D P⟩ true
  | action (g : Λ) {D p} : PositiveGenerated Q seed D p →
      PositiveGenerated Q seed (A.act g D) p

theorem generated_positive {Q : Family S} {seed D : TaggedMenu S}
    (h : Generated S Q A seed D) : ∃ p, PositiveGenerated S A Q seed D p := by
  induction h with
  | seed => exact ⟨false,.seed⟩
  | opposite h ih => obtain ⟨p,hp⟩ := ih; exact ⟨p,.opposite hp⟩
  | left P hP h ih => obtain ⟨p,hp⟩ := ih; exact ⟨true,.left P hP hp⟩
  | right P hP h ih => obtain ⟨p,hp⟩ := ih; exact ⟨true,.right P hP hp⟩
  | action g h ih => obtain ⟨p,hp⟩ := ih; exact ⟨p,.action g hp⟩

theorem PositiveGenerated.trans {Q : Family S} {seed D E : TaggedMenu S} {p q}
    (h : PositiveGenerated S A Q seed D p) (k : PositiveGenerated S A Q D E q) :
    PositiveGenerated S A Q seed E (p || q) := by
  induction k with
  | seed => simpa using h
  | opposite k ih => exact .opposite ih
  | left P hP k ih => simpa using (PositiveGenerated.left P hP ih)
  | right P hP k ih => simpa using (PositiveGenerated.right P hP ih)
  | action g k ih => exact .action g ih

include A in
/-- A path with no multiplication fixes literal names, provided typed converse
also fixes the original literal names. -/
theorem PositiveGenerated.names_of_false {Q : Family S} (hc : LiteralConverse S A)
    {seed D : TaggedMenu S} {p} (h : PositiveGenerated S A Q seed D p) (hp : p = false) :
    names S A.label D = names S A.label seed := by
  induction h with
  | seed => rfl
  | @opposite D p h ih =>
    rw [← ih hp]
    rcases D with ⟨i,j,D⟩
    ext n
    constructor
    · rintro ⟨a,ha,han⟩
      exact ⟨S.conv a,ha,(hc a).trans han⟩
    · rintro ⟨a,ha,han⟩
      refine ⟨S.conv a, ?_, (hc a).trans han⟩
      change S.conv (S.conv a) ∈ D
      simpa only [S.conv_invol] using ha
  | left P hP h ih => cases hp
  | right P hP h ih => cases hp
  | action g h ih => exact (A.literal g _).trans (ih hp)

variable (point : S.RealPointGluing) (edge : S.RealEdgeGluing)

/-- Fullness is an actual menu property on the displayed pair palette. -/
def Full (D : TaggedMenu S) : Prop := D.2.2 = Set.univ

private theorem names_subset_full {D E : TaggedMenu S} (hD : Full S D)
    (hp : Parallel S D E) : names S A.label E ⊆ names S A.label D := by
  rcases D with ⟨i,j,D⟩
  rcases E with ⟨i',j',E⟩
  rcases hp with ⟨hi,hj⟩
  cases hi; cases hj
  intro n hn
  obtain ⟨a,ha,han⟩ := hn
  exact ⟨a,by rw [show D = Set.univ from hD]; trivial,han⟩

/-- Pure relabelling preserves fullness without requiring faithful tag action. -/
theorem full_action {D : TaggedMenu S} (hD : Full S D) (g : Λ) :
    Full S (A.act g D) := by
  apply Set.eq_univ_of_forall
  intro a
  let E : TaggedMenu S := ⟨(A.act g D).1,(A.act g D).2.1,{a}⟩
  have hp : Parallel S D (A.act g⁻¹ E) := by
    apply (A.parallel g _ _).mp
    rw [A.act_inv]
    exact ⟨rfl,rfl⟩
  have hn : A.label a ∈ names S A.label (A.act g⁻¹ E) := by
    rw [A.literal]
    exact ⟨a,by simp [E],rfl⟩
  have hm := names_subset_full S A hD hp hn
  rw [← A.literal g D] at hm
  obtain ⟨b,hb,hba⟩ := hm
  exact A.label_injective _ _ hba ▸ hb

include point in
/-- Full palettes cannot descend to proper menus by any generated path. -/
theorem PositiveGenerated.full {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    {seed D : TaggedMenu S} {p} (h : PositiveGenerated S A Q seed D p)
    (hs : Full S seed) : Full S D := by
  induction h with
  | seed => exact hs
  | @opposite D p h ih =>
    rcases D with ⟨i,j,D⟩
    change S.opposite D = Set.univ
    rw [show D = Set.univ from ih]
    rfl
  | left P hP h ih =>
    change S.product P _ = Set.univ
    dsimp only [Full] at ih
    rw [ih]
    exact S.product_top_of_point_gluing point P (hne hP)
  | right P hP h ih =>
    change S.product _ P = Set.univ
    dsimp only [Full] at ih
    rw [ih]
    exact S.top_product_of_point_gluing point P (hne hP)
  | action g h ih => exact full_action S A ih g

/-- The central action is recorded by an actual tagged equality. This
keeps endpoint transport literal instead of silently identifying palettes. -/
inductive NormalForm (seed : TaggedMenu S) : TaggedMenu S → Bool → Prop
  | forward (g : Λ) {a b i j} (C : S.Menu a b)
      (central : A.act g seed = ⟨a,b,C⟩)
      (L : PositiveOutside S i a) (R : PositiveOutside S b j) :
      NormalForm seed ⟨i,j,L.left (PositiveOutside.right C R)⟩ (L.positive || R.positive)
  | reverse (g : Λ) {a b i j} (C : S.Menu a b)
      (central : A.act g seed = ⟨a,b,C⟩)
      (L : PositiveOutside S i b) (R : PositiveOutside S a j) :
      NormalForm seed ⟨i,j,L.left (PositiveOutside.right (S.opposite C) R)⟩
        (L.positive || R.positive)

include point edge in
/-- Normalization preserves the positive bit exactly. -/
theorem positiveGenerated_normalForm {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    {seed D : TaggedMenu S} {p} (h : PositiveGenerated S A Q seed D p) :
    NormalForm S A seed D p := by
  induction h with
  | seed =>
    rcases seed with ⟨i,j,C⟩
    exact .forward 1 C (A.one _) (.absent _) (.absent _)
  | @opposite D p h ih =>
    cases ih with
    | forward g C hc L R =>
      have hn := NormalForm.reverse (S := S) (A := A) g C hc R.opposite L.opposite
      simpa only [Selectors.flip, PositiveOutside.opposite_left_right edge,
        PositiveOutside.positive_opposite, Bool.or_comm] using hn
    | reverse g C hc L R =>
      have hn := NormalForm.forward (S := S) (A := A) g C hc R.opposite L.opposite
      simpa only [Selectors.flip, PositiveOutside.opposite_left_right edge, S.opposite_opposite,
        PositiveOutside.positive_opposite, Bool.or_comm] using hn
  | left P hP h ih =>
    cases ih with
    | forward g C hc L R =>
      have hn := NormalForm.forward (S := S) (A := A) g C hc
        (PositiveOutside.comp point (.present P (hne hP)) L) R
      rw [PositiveOutside.positive_comp, PositiveOutside.left_comp point edge] at hn
      simpa only [
        PositiveOutside.left, PositiveOutside.positive, Bool.true_or] using hn
    | reverse g C hc L R =>
      have hn := NormalForm.reverse (S := S) (A := A) g C hc
        (PositiveOutside.comp point (.present P (hne hP)) L) R
      rw [PositiveOutside.positive_comp, PositiveOutside.left_comp point edge] at hn
      simpa only [
        PositiveOutside.left, PositiveOutside.positive, Bool.true_or] using hn
  | right P hP h ih =>
    cases ih with
    | forward g C hc L R =>
      have hn := NormalForm.forward (S := S) (A := A) g C hc L
        (PositiveOutside.comp point R (.present P (hne hP)))
      rw [PositiveOutside.positive_comp, ← PositiveOutside.right_comp point edge,
        PositiveOutside.left_right edge] at hn
      simpa only [ PositiveOutside.right, PositiveOutside.positive, Bool.or_true] using hn
    | reverse g C hc L R =>
      have hn := NormalForm.reverse (S := S) (A := A) g C hc L
        (PositiveOutside.comp point R (.present P (hne hP)))
      rw [PositiveOutside.positive_comp, ← PositiveOutside.right_comp point edge,
        PositiveOutside.left_right edge] at hn
      simpa only [ PositiveOutside.right, PositiveOutside.positive, Bool.or_true] using hn
  | action g h ih =>
    cases ih with
    | forward k C hc L R =>
      have hn := NormalForm.forward (S := S) (A := A) (g*k) (A.menuAct g C)
        (by rw [A.mul, hc, ← A.tagged_menuAct]) (L.move A g) (R.move A g)
      simpa only [← A.tagged_menuAct, PositiveOutside.move_left, PositiveOutside.move_right,
        PositiveOutside.positive_move] using hn
    | reverse k C hc L R =>
      have hn := NormalForm.reverse (S := S) (A := A) (g*k) (A.menuAct g C)
        (by rw [A.mul, hc, ← A.tagged_menuAct]) (L.move A g) (R.move A g)
      simpa only [← A.tagged_menuAct, PositiveOutside.move_left, PositiveOutside.move_right,
        A.menuAct_opposite, PositiveOutside.positive_move] using hn

end CCO.SafeReadings
