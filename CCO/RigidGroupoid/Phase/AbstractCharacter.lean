import Mathlib.CategoryTheory.Groupoid
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel

/-! Pure character algebra.  No original source, exactness, quotient, phase
marking, or dominance hypothesis enters these constructions. -/

universe u v w
namespace CCO.RigidGroupoid.Phase.Abstract
open CategoryTheory

abbrev Bit := ZMod 2

structure Character (J : Type u) [Category.{v} J] where
  value : ∀ {a b : J}, (a ⟶ b) → Bit
  map_id : ∀ a, value (𝟙 a) = 0
  map_comp : ∀ {a b c : J} (R : a ⟶ b) (T : b ⟶ c),
    value (R ≫ T) = value R + value T

namespace Character
variable {J : Type u} [Groupoid.{v} J] (χ : Character J)

theorem map_inv {a b : J} (R : a ⟶ b) : χ.value (inv R) = -χ.value R := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← χ.map_comp]
  simp [χ.map_id]

end Character

/-- Extend the singleton containing the nonzero vector to a basis and use
its literal coordinate functional.  In particular this applies to every
finite elementary abelian isotropy space. -/
theorem detecting_character {V : Type w} [AddCommGroup V] [Module Bit V]
    [Finite V] (t : V) (ht : t ≠ 0) : ∃ ℓ : V →ₗ[Bit] Bit, ℓ t = 1 := by
  classical
  have hs : LinearIndepOn Bit id ({t} : Set V) := by
    exact LinearIndepOn.singleton ht
  let b := Module.Basis.extend hs
  have hm : t ∈ hs.extend (Set.subset_univ _) :=
    Module.Basis.subset_extend hs (by simp)
  let j : hs.extend (Set.subset_univ _) := ⟨t, hm⟩
  refine ⟨b.coord j, ?_⟩
  have hj : b j = t := Module.Basis.extend_apply_self hs j
  calc
    (b.coord j) t = (b.coord j) (b j) := congrArg (b.coord j) hj.symm
    _ = 1 := by simp

variable {J : Type u} [Groupoid.{v} J]

/-- Connectivity supplies the chosen paths; the root path is normalized to
the identity rather than required as additional source data. -/
noncomputable def normalizedConnectors (o : J) (connected : ∀ a, Nonempty (o ⟶ a))
    (a : J) : o ⟶ a := by
  classical
  exact if h : a = o then h.symm ▸ 𝟙 o else Classical.choice (connected a)

theorem normalizedConnectors_root (o : J) (connected : ∀ a, Nonempty (o ⟶ a)) :
    normalizedConnectors o connected o = 𝟙 o := by
  classical
  simp [normalizedConnectors]

/-- The root coefficient of an arrow, relative to actual chosen connectors. -/
noncomputable def rootCoefficient (o : J) (B : ∀ a, o ⟶ a) {a b : J} (R : a ⟶ b) : o ⟶ o :=
  B a ≫ R ≫ inv (B b)

theorem rootCoefficient_comp (o : J) (B : ∀ a, o ⟶ a)
    {a b c : J} (R : a ⟶ b) (T : b ⟶ c) :
    rootCoefficient o B (R ≫ T) = rootCoefficient o B R ≫ rootCoefficient o B T := by
  simp [rootCoefficient, Category.assoc]

theorem coefficient_reconstruct (o : J) (B : ∀ a, o ⟶ a)
    {a b : J} (R : a ⟶ b) :
    inv (B a) ≫ rootCoefficient o B R ≫ B b = R := by
  simp [rootCoefficient, Category.assoc]

theorem coefficient_unique (o : J) (B : ∀ a, o ⟶ a)
    {a b : J} (R : a ⟶ b) (h : o ⟶ o)
    (hh : inv (B a) ≫ h ≫ B b = R) : h = rootCoefficient o B R := by
  rw [← hh]
  simp [rootCoefficient, Category.assoc]

/-- A root additive character extends to every arrow.  Connectivity is used
only to supply the displayed connectors, not as a hidden source premise. -/
noncomputable def connectedCharacter (o : J) (B : ∀ a, o ⟶ a)
    (χ₀ : (o ⟶ o) → Bit) (χid : χ₀ (𝟙 o) = 0)
    (χcomp : ∀ R T, χ₀ (R ≫ T) = χ₀ R + χ₀ T) : Character J where
  value R := χ₀ (rootCoefficient o B R)
  map_id a := by simpa [rootCoefficient] using χid
  map_comp R T := by rw [rootCoefficient_comp, χcomp]

/-- Normalized root connector gives exactly the supplied root character. -/
theorem connectedCharacter_root (o : J) (B : ∀ a, o ⟶ a)
    (χ₀ : (o ⟶ o) → Bit) (χid : χ₀ (𝟙 o) = 0)
    (χcomp : ∀ R T, χ₀ (R ≫ T) = χ₀ R + χ₀ T)
    (hB : B o = 𝟙 o) (R : o ⟶ o) :
    (connectedCharacter o B χ₀ χid χcomp).value R = χ₀ R := by
  simp [connectedCharacter, rootCoefficient, hB]

noncomputable def transported {o : J} (t : o ⟶ o) {a : J} (R : o ⟶ a) : a ⟶ a := inv R ≫ t ≫ R

theorem transported_nonidentity {o a : J} (t : o ⟶ o) (ht : t ≠ 𝟙 o)
    (R : o ⟶ a) : transported t R ≠ 𝟙 a := by
  intro h
  apply ht
  have e := congrArg (fun f => R ≫ f ≫ inv R) h
  simpa [transported, Category.assoc] using e

theorem transported_square {o a : J} (t : o ⟶ o) (ht : t ≫ t = 𝟙 o)
    (R : o ⟶ a) : transported t R ≫ transported t R = 𝟙 a := by
  simp [transported, Category.assoc, ← Category.assoc t t, ht]

/-- Path-independence uses only commutativity in root isotropy. -/
theorem transported_independent {o a : J} (t : o ⟶ o)
    (hc : ∀ h : o ⟶ o, h ≫ t = t ≫ h) (R T : o ⟶ a) :
    transported t R = transported t T := by
  have e := congrArg (fun h => inv R ≫ h ≫ T) (hc (R ≫ inv T))
  simpa [transported, Category.assoc] using e.symm

theorem transported_character {o a : J} (χ : Character J) (t : o ⟶ o)
    (ht : χ.value t = 1) (R : o ⟶ a) : χ.value (transported t R) = 1 := by
  simp only [transported, χ.map_comp, χ.map_inv, ht]
  abel

end CCO.RigidGroupoid.Phase.Abstract
