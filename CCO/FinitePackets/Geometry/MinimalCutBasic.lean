import CCO.FinitePackets.Geometry.Lattice
import CCO.RealHull.Geometry.ClassSizes
import Mathlib.Order.Minimal

/-! Elementary minimality on ACTUAL real equivalence classes.  The finite
bottom is a parameter here; Sigma later supplies its genuine source instance.
No CCO, exact quotient, countability or distributive-lattice premise. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

def MinimalInfiniteCut (E : ColourEq S i) : Prop :=
  ¬ FiniteIndex S ⊥ E ∧ ∀ J : ColourEq S i, J < E → FiniteIndex S ⊥ J

def FiniteBottomSpec (F : ColourEq S i) : Prop :=
  FiniteIndex S ⊥ F ∧ ∀ J : ColourEq S i, FiniteIndex S ⊥ J → J ≤ F

theorem finiteIndex_bottom_iff_finite_classes (E : ColourEq S i) :
    FiniteIndex S ⊥ E ↔ ∀ x, Finite (ClassPoint S i E x) := by
  constructor
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv S i E x)
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv S i E x).symm

theorem cut_nonidentity {E : ColourEq S i} (hE : MinimalInfiniteCut S E) : E ≠ ⊥ := by
  intro he
  subst E
  exact hE.1 (finiteIndex_self S ⊥)

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

include H in
theorem cut_actual_classes_infinite {E : ColourEq S i} (hE : MinimalInfiniteCut S E)
    (x : X i) : Infinite (ClassPoint S i E x) := by
  apply not_finite_iff_infinite.mp
  intro hf
  letI := hf
  have hr : Finite (RelativeClass (⊥ : ColourEq S i).val E.val x) :=
    Finite.of_equiv _ (bottomClassEquiv S i E x).symm
  exact hE.1 ((finiteIndex_iff_at S H ⊥ E x).mpr hr)

theorem exists_minimal_infinite_cut [Infinite (X i)] :
    ∃ E : ColourEq S i, MinimalInfiniteCut S E := by
  have ht : ¬ FiniteIndex S (⊥ : ColourEq S i) ⊤ := by
    intro h
    obtain ⟨x⟩ := S.nonemptySort i
    letI := h x
    letI : Finite (ClassPoint S i ⊤ x) :=
      Finite.of_equiv _ (bottomClassEquiv S i ⊤ x)
    let e : ClassPoint S i ⊤ x ≃ X i := {
      toFun := Subtype.val
      invFun := fun y => ⟨y,trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    letI : Finite (X i) := Finite.of_equiv _ e
    exact not_finite (X i)
  obtain ⟨E,hE,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun E : ColourEq S i => ¬ FiniteIndex S ⊥ E) ⟨⊤,ht⟩
  refine ⟨E,hE,?_⟩
  intro J hJE
  by_contra hJ
  exact hJE.not_ge (hmin hJ hJE.le)

theorem cut_proper_le_finite_part {E F J : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F) (hJE : J < E) :
    J ≤ E ⊓ F :=
  le_inf hJE.le (hF.2 J (hE.2 J hJE))

theorem cut_finite_part_strict {E F : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F) : E ⊓ F < E := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  apply hE.1
  exact finiteIndex_lower S (by rw [← he]; exact inf_le_right) hF.1

theorem cut_lower_interval {E F : ColourEq S i}
    (hE : MinimalInfiniteCut S E) (hF : FiniteBottomSpec S F) :
    Set.Iic E = Set.Iic (E ⊓ F) ∪ {E} := by
  ext J
  constructor
  · intro hJ
    by_cases he : J = E
    · exact Or.inr he
    · exact Or.inl (cut_proper_le_finite_part S hE hF (lt_of_le_of_ne hJ he))
  · rintro (hJ | he)
    · change J ≤ E
      exact (show J ≤ E ⊓ F from hJ).trans inf_le_left
    · change J = E at he
      change J ≤ E
      exact he ▸ le_rfl

end CCO.FinitePackets.Geometry
