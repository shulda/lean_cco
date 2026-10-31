import CCO.RawOrbitals
import Mathlib.Data.Finset.Basic

/-!
# B050: fresh-fibre algebra for the actual quotient diversity pullback

This is the elementary core of the source-09 quotient STRONG semigroup
lemma. The required infinite fibres are an EXPLICIT hypothesis here.
The separate original-source SAP proof of that hypothesis is still an
open B050 obligation; this conditional algebra alone is not the source
theorem or its actual source instance.

The quotient is formed from a real original Setoid J. Its diagonal
pulls back to the *nonempty, if J is nontrivial and fresh*, old diversity
slice Jᵒ, never to the old identity.
-/

universe u

namespace CCO.TerminalLattice

variable {A : Type u}

/-- Every quotient class has fresh real representatives outside any
prescribed finite set. This is a temporary B050 C10 interface that must
later be derived from *original* SAP and actual source homogeneity. -/
def FreshFibre (J : Setoid A) : Prop :=
  ∀ (q : Quotient J) (forbidden : Finset A),
    ∃ y : A, y ∉ forbidden ∧ Quotient.mk J y = q

/-- Full OLD real diversity pullback of a relation on actual J-classes. -/
def quotientDiversity (J : Setoid A)
    (R : Quotient J → Quotient J → Prop) : A → A → Prop :=
  fun x y => x ≠ y ∧ R (Quotient.mk J x) (Quotient.mk J y)

/-- Two-letter positive STRONG real-path semantics: all three vertices
are distinct; no genuine equality letter is inserted. -/
def strongCompose (P Q : A → A → Prop) : A → A → Prop :=
  fun x z => x ≠ z ∧ ∃ y, x ≠ y ∧ y ≠ z ∧ P x y ∧ Q y z

/-- The true quotient diagonal pulls back to the OLD J diversity slice. -/
theorem quotientDiversity_diagonal (J : Setoid A) :
    quotientDiversity J (fun q r => q = r) =
      (fun x y => x ≠ y ∧ J x y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨hxy, hq⟩
    exact ⟨hxy, Quotient.exact hq⟩
  · rintro ⟨hxy, hJ⟩
    exact ⟨hxy, Quotient.sound hJ⟩

theorem quotientDiversity_inter (J : Setoid A)
    (R T : Quotient J → Quotient J → Prop) :
    quotientDiversity J (fun q r => R q r ∧ T q r) =
      (fun x y => quotientDiversity J R x y ∧ quotientDiversity J T x y) := by
  funext x y
  apply propext
  by_cases hxy : x = y
  · simp [quotientDiversity, hxy]
  · simp [quotientDiversity, hxy]

theorem quotientDiversity_union (J : Setoid A)
    (R T : Quotient J → Quotient J → Prop) :
    quotientDiversity J (fun q r => R q r ∨ T q r) =
      (fun x y => quotientDiversity J R x y ∨ quotientDiversity J T x y) := by
  funext x y
  apply propext
  by_cases hxy : x = y
  · simp [quotientDiversity, hxy]
  · simp [quotientDiversity, hxy]

/-- A quotient relation is determined by its full original diversity
pullback, including all quotient-diagonal pairs, once J-fibres are fresh. -/
theorem quotientDiversity_injective (J : Setoid A)
    (fresh : FreshFibre J) :
    Function.Injective (quotientDiversity J) := by
  classical
  intro R T h
  funext q r
  apply propext
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y, hy, hqr⟩ := fresh r ({x} : Finset A)
    have hxy : x ≠ y := by
      intro h
      apply hy
      simp [h]
    have hp : quotientDiversity J R x y = quotientDiversity J T x y :=
      congrFun (congrFun h x) y
    have hiff : R (Quotient.mk J x) (Quotient.mk J y) ↔
        T (Quotient.mk J x) (Quotient.mk J y) := by
      constructor
      · intro hr
        have hpt : quotientDiversity J T x y := Eq.mp hp ⟨hxy, hr⟩
        exact hpt.2
      · intro ht
        have hpr : quotientDiversity J R x y := Eq.mp hp.symm ⟨hxy, ht⟩
        exact hpr.2
    rw [hqr] at hiff
    exact hiff

/-- The precise two-step positive quotient lifting: composition of
the full OLD diversity pullbacks agrees with quotient RAW composition
at DISTINCT real endpoints. The intermediate J-class may coincide
with either endpoint class; only the original real points are fresh. -/
theorem quotientDiversity_strong_comp (J : Setoid A)
    (fresh : FreshFibre J)
    (R T : Quotient J → Quotient J → Prop) :
    strongCompose (quotientDiversity J R) (quotientDiversity J T) =
      quotientDiversity J (RawSymmetric.compose R T) := by
  classical
  funext x z
  apply propext
  constructor
  · rintro ⟨hxz, y, _hxy, _hyz, hR, hT⟩
    exact ⟨hxz, Quotient.mk J y, hR.2, hT.2⟩
  · rintro ⟨hxz, q, hR, hT⟩
    obtain ⟨y, hy, hqy⟩ := fresh q ({x, z} : Finset A)
    have hxy : x ≠ y := by
      intro h
      apply hy
      simp [h]
    have hyz : y ≠ z := by
      intro h
      apply hy
      simp [h]
    refine ⟨hxz, y, hxy, hyz, ⟨hxy, ?_⟩, ⟨hyz, ?_⟩⟩
    · rw [hqy]
      exact hR
    · rw [hqy]
      exact hT

/-- Every nonempty quotient relation gives a nonempty old diversity
pullback, including quotient-diagonal relations. -/
theorem quotientDiversity_nonempty (J : Setoid A)
    (fresh : FreshFibre J)
    (R : Quotient J → Quotient J → Prop)
    (hne : ∃ q r, R q r) :
    ∃ x y : A, quotientDiversity J R x y := by
  classical
  obtain ⟨q, r, hqr⟩ := hne
  obtain ⟨x, _, hx⟩ := fresh q (∅ : Finset A)
  obtain ⟨y, hy, hyq⟩ := fresh r ({x} : Finset A)
  have hxy : x ≠ y := by
    intro h
    apply hy
    simp [h]
  exact ⟨x, y, hxy, by simpa only [hx, hyq] using hqr⟩

end CCO.TerminalLattice
